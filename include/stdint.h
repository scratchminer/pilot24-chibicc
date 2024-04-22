#ifndef __STDINT_H
#define __STDINT_H

typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int24_t;
typedef unsigned int uint24_t;
typedef long int32_t;
typedef unsigned long uint32_t;
typedef signed char int_least8_t;
typedef unsigned char uint_least8_t;
typedef short int_least16_t;
typedef unsigned short uint_least16_t;
typedef int int_least24_t;
typedef unsigned int uint_least24_t;
typedef long int_least32_t;
typedef unsigned long uint_least32_t;
typedef signed char int_fast8_t;
typedef unsigned char uint_fast8_t;
typedef short int_fast16_t;
typedef unsigned short uint_fast16_t;
typedef int int_fast24_t;
typedef unsigned int uint_fast24_t;
typedef long int_fast32_t;
typedef unsigned long uint_fast32_t;

#define INT8_MIN -128
#define INT8_MAX 127
#define UINT8_MAX 255

#define INT16_MIN -32768
#define INT16_MAX 32767
#define UINT16_MAX 65535

#define INT24_MIN -8388608
#define INT24_MAX 8388607
#define UINT24_MAX 16777215

#define INT32_MIN -2147483647
#define INT32_MAX 2147483648
#define UINT32_MAX 4294967295

#define INT_LEAST8_MIN -128
#define INT_LEAST8_MAX 127
#define UINT_LEAST8_MAX 255

#define INT_LEAST16_MIN -32768
#define INT_LEAST16_MAX 32767
#define UINT_LEAST16_MAX 65535

#define INT_LEAST24_MIN -8388608
#define INT_LEAST24_MAX 8388607
#define UINT_LEAST24_MAX 16777215

#define INT_LEAST32_MIN -2147483647
#define INT_LEAST32_MAX 2147483648
#define UINT_LEAST32_MAX 4294967295

#define INT_FAST8_MIN -128
#define INT_FAST8_MAX 127
#define UINT_FAST8_MAX 255

#define INT_FAST16_MIN -32768
#define INT_FAST16_MAX 32767
#define UINT_FAST16_MAX 65535

#define INT_FAST24_MIN -8388608
#define INT_FAST24_MAX 8388607
#define UINT_FAST24_MAX 16777215

#define INT_FAST32_MIN -2147483647
#define INT_FAST32_MAX 2147483648
#define UINT_FAST32_MAX 4294967295

#define INTPTR_MIN -8388608
#define INTPTR_MAX 8388607
#define UINTPTR_MAX 16777215

#define INTMAX_MIN -2147483647
#define INTMAX_MAX 2147483648
#define UINTMAX_MAX 4294967295

#define PTRDIFF_MIN -8388608
#define PTRDIFF_MAX 8388607

#define SIZE_MAX 16777215

#define WCHAR_MIN -32768
#define WCHAR_MAX 32767

#endif