/*
* Functions for constant time operations on data and testing of
* constant time annotations using valgrind.
*
* For more information about constant time programming see
* Wagner, Molnar, et al "The Program Counter Security Model"
*
* (C) 2010 Falko Strenzke
* (C) 2015,2016,2018 Jack Lloyd
*
* Botan is released under the Simplified BSD License (see license.txt)
*/

#ifndef BOTAN_CT_UTILS_H_
#define BOTAN_CT_UTILS_H_

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

/**
* TODO
* - new test suite
* - doc comments
* - document in manual?
* - run valgrind tests fix missing annotations
*/
template<typename T>
class Mask
   {
   public:
      static_assert(std::is_unsigned<T>::value, "CT::Mask only defined for unsigned integer types");

      Mask(const Mask<T>& other) = default;
      Mask<T>& operator=(const Mask<T>& other) = default;

      template<typename U>
      Mask(Mask<U> o) : m_mask(o.value())
         {
         static_assert(sizeof(U) > sizeof(T), "sizes ok");
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
         return ~Mask<T>::is_zero(v);
         }

      static Mask<T> is_zero(T x)
         {
         return Mask<T>(expand_top_bit(~x & (x - 1)));
         }

      template<typename U>
      static Mask<T> is_zero(U x)
         {
         static_assert(sizeof(U) > sizeof(T), "sizes ok");
         return Mask<T>(Mask<U>::is_zero(x));
         }

      static Mask<T> is_nonzero(T v)
         {
         return ~Mask<T>::is_zero(v);
         }

      static Mask<T> is_equal(T x, T y)
         {
         return Mask<T>::is_zero(static_cast<T>(x ^ y));
         }

      static Mask<T> is_lt(T x, T y)
         {
         return Mask<T>(expand_top_bit(x^((x^y) | ((x-y)^x))));
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

      T select(T x, T y) const
         {
         // (x & value()) | (y & ~value())
         return static_cast<T>(y ^ (value() & (x ^ y)));
         }

      Mask<T> select_mask(Mask<T> x, Mask<T> y) const
         {
         return Mask<T>(select(x.value(), y.value()));
         }

      void select_n(T output[], const T x[], const T y[], size_t len) const
         {
         for(size_t i = 0; i != len; ++i)
            output[i] = this->select(x[i], y[i]);
         }

      void if_set_zero_out(T buf[], size_t elems)
         {
         for(size_t i = 0; i != elems; ++i)
            {
            buf[i] = this->if_not_set_return(buf[i]);
            }
         }

      T unpoisoned_value() const
         {
         T r = value();
         CT::unpoison(r);
         return r;
         }

      bool is_set() const
         {
         return unpoisoned_value() != 0;
         }

      T value() const
         {
         return m_mask;
         }

   private:
      static T expand_top_bit(T a)
         {
         return static_cast<T>(0) - (a >> (sizeof(T)*8-1));
         }

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

inline secure_vector<uint8_t> strip_leading_zeros(const uint8_t in[], size_t length)
   {
   size_t leading_zeros = 0;

   auto only_zeros = Mask<uint8_t>::set();

   for(size_t i = 0; i != length; ++i)
      {
      only_zeros &= CT::Mask<uint8_t>::is_zero(in[i]);
      leading_zeros += only_zeros.if_set_return(1);
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
