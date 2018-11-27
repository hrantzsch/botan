/*
* Functions for constant time operations on data and testing of
* constant time annotations using valgrind.
*
* For more information about constant time programming see
* Wagner, Molnar, et al "The Program Counter Security Model"
*
* (C) 2010 Falko Strenzke
* (C) 2015,2016 Jack Lloyd
*
* Botan is released under the Simplified BSD License (see license.txt)
*/

#ifndef BOTAN_TIMING_ATTACK_CM_H_
#define BOTAN_TIMING_ATTACK_CM_H_

#include <botan/secmem.h>
#include <type_traits>
#include <vector>

#if defined(BOTAN_HAS_VALGRIND)
  #include <valgrind/memcheck.h>
#endif

namespace Botan {

namespace CT {

/**
* Use valgrind to mark the contents of memory as being undefined.
* Valgrind will accept operations which manipulate undefined values,
* but will warn if an undefined value is used to decided a conditional
* jump or a load/store address. So if we poison all of our inputs we
* can confirm that the operations in question are truly const time
* when compiled by whatever compiler is in use.
*
* Even better, the VALGRIND_MAKE_MEM_* macros work even when the
* program is not run under valgrind (though with a few cycles of
* overhead, which is unfortunate in final binaries as these
* annotations tend to be used in fairly important loops).
*
* This approach was first used in ctgrind (https://github.com/agl/ctgrind)
* but calling the valgrind mecheck API directly works just as well and
* doesn't require a custom patched valgrind.
*/
template<typename T>
inline void poison(const T* p, size_t n)
   {
#if defined(BOTAN_HAS_VALGRIND)
   VALGRIND_MAKE_MEM_UNDEFINED(p, n * sizeof(T));
#else
   BOTAN_UNUSED(p);
   BOTAN_UNUSED(n);
#endif
   }

template<typename T>
inline void unpoison(const T* p, size_t n)
   {
#if defined(BOTAN_HAS_VALGRIND)
   VALGRIND_MAKE_MEM_DEFINED(p, n * sizeof(T));
#else
   BOTAN_UNUSED(p);
   BOTAN_UNUSED(n);
#endif
   }

template<typename T>
inline void unpoison(T& p)
   {
#if defined(BOTAN_HAS_VALGRIND)
   VALGRIND_MAKE_MEM_DEFINED(&p, sizeof(T));
#else
   BOTAN_UNUSED(p);
#endif
   }

/* Mask generation */

template<typename T>
inline constexpr T expand_top_bit(T a)
   {
   static_assert(std::is_unsigned<T>::value, "unsigned integer type required");
   return static_cast<T>(0) - (a >> (sizeof(T)*8-1));
   }

template<typename T>
inline constexpr T is_zero(T x)
   {
   static_assert(std::is_unsigned<T>::value, "unsigned integer type required");
   return expand_top_bit<T>(~x & (x - 1));
   }

/*
* T should be an unsigned machine integer type
* Expand to a mask used for other operations
* @param in an integer
* @return If n is zero, returns zero. Otherwise
* returns a T with all bits set for use as a mask with
* select.
*/
template<typename T>
inline constexpr T expand_mask(T x)
   {
   static_assert(std::is_unsigned<T>::value, "unsigned integer type required");
   return ~is_zero(x);
   }

template<typename T>
inline constexpr T select(T mask, T from0, T from1)
   {
   static_assert(std::is_unsigned<T>::value, "unsigned integer type required");
   //return static_cast<T>((from0 & mask) | (from1 & ~mask));
   return static_cast<T>(from1 ^ (mask & (from0 ^ from1)));
   }

template<typename T>
inline constexpr T select2(T mask0, T val0, T mask1, T val1, T val2)
   {
   return select<T>(mask0, val0, select<T>(mask1, val1, val2));
   }

template<typename T>
inline constexpr T select3(T mask0, T val0, T mask1, T val1, T mask2, T val2, T val3)
   {
   return select2<T>(mask0, val0, mask1, val1, select<T>(mask2, val2, val3));
   }

template<typename PredT, typename ValT>
inline constexpr ValT val_or_zero(PredT pred_val, ValT val)
   {
   return select(CT::expand_mask<ValT>(pred_val), val, static_cast<ValT>(0));
   }

template<typename T>
inline constexpr T is_equal(T x, T y)
   {
   return is_zero<T>(x ^ y);
   }

template<typename T>
inline constexpr T is_less(T a, T b)
   {
   return expand_top_bit<T>(a ^ ((a^b) | ((a-b)^a)));
   }

template<typename T>
inline constexpr T is_lte(T a, T b)
   {
   return CT::is_less(a, b) | CT::is_equal(a, b);
   }

template<typename C, typename T>
inline T conditional_return(C condvar, T left, T right)
   {
   const T val = CT::select(CT::expand_mask<T>(condvar), left, right);
   CT::unpoison(val);
   return val;
   }

template<typename T>
class Mask
   {
   public:
      static_assert(std::is_unsigned<T>::value, "CT::Mask only defined for unsigned integer types");

      Mask(const Mask<T>& other) = default;
      Mask<T>& operator=(const Mask<T>& other) = default;

      template<typename U>
      Mask(Mask<U> o) : m_mask(CT::expand_mask(o.value()))
         {
         }

      static Mask<T> set()
         {
         return Mask<T>(~0);
         }

      static Mask<T> cleared()
         {
         return Mask<T>(0);
         }

      static Mask<T> expand(T v)
         {
         return Mask<T>(expand_mask(v));
         }

      static Mask<T> is_nonzero(T v)
         {
         return Mask<T>(expand_mask(v));
         }

      static Mask<T> is_zero(T x)
         {
         return Mask<T>(CT::is_zero(x));
         }

      static Mask<T> is_equal(T x, T y)
         {
         return Mask<T>(CT::is_equal(x, y));
         }

      static Mask<T> is_lt(T x, T y)
         {
         return Mask<T>(CT::is_less(x, y));
         }

      static Mask<T> is_gt(T x, T y)
         {
         return Mask<T>::is_lt(y, x);
         }

      static Mask<T> is_lte(T x, T y)
         {
         return ~Mask<T>::is_gt(x, y);
         }

      static Mask<T> is_gte(T x, T y)
         {
         return ~Mask<T>::is_lt(x, y);
         }

      Mask<T>& operator&=(Mask<T> o) { m_mask &= o.value(); return (*this); }
      Mask<T>& operator^=(Mask<T> o) { m_mask ^= o.value(); return (*this); }
      Mask<T>& operator|=(Mask<T> o) { m_mask |= o.value(); return (*this); }

      friend Mask<T> operator&(Mask<T> x, Mask<T> y)
         {
         return Mask<T>(x.value() & y.value());
         }

      friend Mask<T> operator^(Mask<T> x, Mask<T> y)
         {
         return Mask<T>(x.value() ^ y.value());
         }

      friend Mask<T> operator|(Mask<T> x, Mask<T> y)
         {
         return Mask<T>(x.value() | y.value());
         }

      Mask<T> operator~() const
         {
         return Mask<T>(~value());
         }

      /**
      * Return x if the mask is set, or otherwise zero
      */
      T if_set_return(T x) const
         {
         return m_mask & x;
         }

      /**
      * Return x if the mask is cleared, or otherwise zero
      */
      T if_not_set_return(T x) const
         {
         return ~m_mask & x;
         }

      T select(T x, T y) const { return CT::select(m_mask, x, y); }

      Mask<T> select_mask(Mask<T> x, Mask<T> y) const
         {
         return Mask<T>(select(x.value(), y.value()));
         }

      void select_n(T output[], const T x[], const T y[], size_t len) const
         {
         for(size_t i = 0; i != len; ++i)
            output[i] = this->select(x[i], y[i]);
         }

      T value() const
         {
         return m_mask;
         }

   private:
      Mask(T m) : m_mask(m) {}

      T m_mask;
   };

template<typename T>
inline Mask<T> conditional_copy_mem(T cnd,
                                    T* to,
                                    const T* from0,
                                    const T* from1,
                                    size_t elems)
   {
   const auto mask = CT::Mask<T>::is_nonzero(cnd);
   mask.select_n(to, from0, from1, elems);
   return mask;
   }

template<typename T>
inline void cond_zero_mem(Mask<T> cnd,
                          T* array,
                          size_t elems)
   {
   for(size_t i = 0; i != elems; ++i)
      {
      array[i] = cnd.if_not_set_return(array[i]);
      }
   }

inline secure_vector<uint8_t> strip_leading_zeros(const uint8_t in[], size_t length)
   {
   size_t leading_zeros = 0;

   uint8_t only_zeros = 0xFF;

   for(size_t i = 0; i != length; ++i)
      {
      only_zeros = only_zeros & CT::is_zero<uint8_t>(in[i]);
      leading_zeros += CT::select<uint8_t>(only_zeros, 1, 0);
      }

   return secure_vector<uint8_t>(in + leading_zeros, in + length);
   }

inline secure_vector<uint8_t> strip_leading_zeros(const secure_vector<uint8_t>& in)
   {
   return strip_leading_zeros(in.data(), in.size());
   }

}

}

#endif
