/*
 * Copyright 2010-2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

/* Copyright 2011 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 *
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

/*
 * A 64-bit implementation of the NIST P-224 elliptic curve point multiplication
 *
 * Inspired by Daniel J. Bernstein's public domain nistp224 implementation
 * and Adam Langley's public domain 64-bit C implementation of curve25519
 */


# include <stdint.h>
# include <string.h>

# if defined(__GNUC__) && (__GNUC__ > 3 || (__GNUC__ == 3 && __GNUC_MINOR__ >= 1))
  /* even with gcc, the typedef won't work for 32-bit platforms */
typedef __uint128_t uint128_t;  /* nonstandard; implemented by gcc on 64-bit
                                 * platforms */
# else
#  error "Need GCC 3.1 or later to define type uint128_t"
# endif

typedef uint8_t u8;
typedef uint64_t u64;
typedef int64_t s64;

/******************************************************************************/
/*-
 * INTERNAL REPRESENTATION OF FIELD ELEMENTS
 *
 * Field elements are represented as a_0 + 2^56*a_1 + 2^112*a_2 + 2^168*a_3
 * using 64-bit coefficients called 'limbs',
 * and sometimes (for multiplication results) as
 * b_0 + 2^56*b_1 + 2^112*b_2 + 2^168*b_3 + 2^224*b_4 + 2^280*b_5 + 2^336*b_6
 * using 128-bit coefficients called 'widelimbs'.
 * A 4-limb representation is an 'felem';
 * a 7-widelimb representation is a 'widefelem'.
 * Even within felems, bits of adjacent limbs overlap, and we don't always
 * reduce the representations: we ensure that inputs to each felem
 * multiplication satisfy a_i < 2^60, so outputs satisfy b_i < 4*2^60*2^60,
 * and fit into a 128-bit word without overflow. The coefficients are then
 * again partially reduced to obtain an felem satisfying a_i < 2^57.
 * We only reduce to the unique minimal representation at the end of the
 * computation.
 */

typedef uint64_t limb;
typedef uint128_t widelimb;

typedef limb felem[4];
typedef widelimb widefelem[7];

/*
 * Field element represented as a byte arrary. 28*8 = 224 bits is also the
 * group order size for the elliptic curve, and we also use this type for
 * scalars for point multiplication.
 */
typedef u8 felem_bytearray[28];

static const felem_bytearray nistp224_curve_params[5] = {
    {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, /* p */
     0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01},
    {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, /* a */
     0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF,
     0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE},
    {0xB4, 0x05, 0x0A, 0x85, 0x0C, 0x04, 0xB3, 0xAB, 0xF5, 0x41, /* b */
     0x32, 0x56, 0x50, 0x44, 0xB0, 0xB7, 0xD7, 0xBF, 0xD8, 0xBA,
     0x27, 0x0B, 0x39, 0x43, 0x23, 0x55, 0xFF, 0xB4},
    {0xB7, 0x0E, 0x0C, 0xBD, 0x6B, 0xB4, 0xBF, 0x7F, 0x32, 0x13, /* x */
     0x90, 0xB9, 0x4A, 0x03, 0xC1, 0xD3, 0x56, 0xC2, 0x11, 0x22,
     0x34, 0x32, 0x80, 0xD6, 0x11, 0x5C, 0x1D, 0x21},
    {0xbd, 0x37, 0x63, 0x88, 0xb5, 0xf7, 0x23, 0xfb, 0x4c, 0x22, /* y */
     0xdf, 0xe6, 0xcd, 0x43, 0x75, 0xa0, 0x5a, 0x07, 0x47, 0x64,
     0x44, 0xd5, 0x81, 0x99, 0x85, 0x00, 0x7e, 0x34}
};

typedef unsigned __CPROVER_bitvector[500] ubig;

ubig p = (((ubig)1)<<224) - (((ubig)1)<<96) + 1;

ubig horner(felem in) {
    ubig out = 0;
    out += in[3];
    out <<= 56;
    out += in[2];
    out <<= 56;
    out += in[1];
    out <<= 56;
    out += in[0];
    return out;
}


/*
 * Helper functions to convert field elements to/from internal representation
 */
static void bin28_to_felem(felem out, const u8 in[28])
{
    out[0] = *((const uint64_t *)(in)) & 0x00ffffffffffffff;
    out[1] = (*((const uint64_t *)(in + 7))) & 0x00ffffffffffffff;
    out[2] = (*((const uint64_t *)(in + 14))) & 0x00ffffffffffffff;
    out[3] = (*((const uint64_t *)(in+20))) >> 8;
}

static void felem_to_bin28(u8 out[28], const felem in)
{
    unsigned i;
    for (i = 0; i < 7; ++i) {
        out[i] = in[0] >> (8 * i);
        out[i + 7] = in[1] >> (8 * i);
        out[i + 14] = in[2] >> (8 * i);
        out[i + 21] = in[3] >> (8 * i);
    }
}

/* To preserve endianness when using BN_bn2bin and BN_bin2bn */
static void flip_endian(u8 *out, const u8 *in, unsigned len)
{
    unsigned i;
    for (i = 0; i < len; ++i)
        out[i] = in[len - 1 - i];
}


/******************************************************************************/
/*-
 *                              FIELD OPERATIONS
 *
 * Field operations, using the internal representation of field elements.
 * NB! These operations are specific to our point multiplication and cannot be
 * expected to be correct in general - e.g., multiplication with a large scalar
 * will cause an overflow.
 *
 */

static void felem_one(felem out)
{
    out[0] = 1;
    out[1] = 0;
    out[2] = 0;
    out[3] = 0;
}

static void felem_assign(felem out, const felem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
}

/* Sum two field elements: out += in */
static void felem_sum(felem out, const felem in)
{
    out[0] += in[0];
    out[1] += in[1];
    out[2] += in[2];
    out[3] += in[3];
}

/* Get negative value: out = -in */
/* Assumes in[i] < 2^57 */
static void felem_neg(felem out, const felem in)
{
    static const limb two58p2 = (((limb) 1) << 58) + (((limb) 1) << 2);
    static const limb two58m2 = (((limb) 1) << 58) - (((limb) 1) << 2);
    static const limb two58m42m2 = (((limb) 1) << 58) -
        (((limb) 1) << 42) - (((limb) 1) << 2);

    /* Set to 0 mod 2^224-2^96+1 to ensure out > in */
    out[0] = two58p2 - in[0];
    out[1] = two58m42m2 - in[1];
    out[2] = two58m2 - in[2];
    out[3] = two58m2 - in[3];
}

/* Subtract field elements: out -= in */
/* Assumes in[i] < 2^57 */
static void felem_diff(felem out, const felem in)
{
    static const limb two58p2 = (((limb) 1) << 58) + (((limb) 1) << 2);
    static const limb two58m2 = (((limb) 1) << 58) - (((limb) 1) << 2);
    static const limb two58m42m2 = (((limb) 1) << 58) -
        (((limb) 1) << 42) - (((limb) 1) << 2);

    /* Add 0 mod 2^224-2^96+1 to ensure out > in */
    out[0] += two58p2;
    out[1] += two58m42m2;
    out[2] += two58m2;
    out[3] += two58m2;

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
}

/* Subtract in unreduced 128-bit mode: out -= in */
/* Assumes in[i] < 2^119 */
static void widefelem_diff(widefelem out, const widefelem in)
{
    static const widelimb two120 = ((widelimb) 1) << 120;
    static const widelimb two120m64 = (((widelimb) 1) << 120) -
        (((widelimb) 1) << 64);
    static const widelimb two120m104m64 = (((widelimb) 1) << 120) -
        (((widelimb) 1) << 104) - (((widelimb) 1) << 64);

    /* Add 0 mod 2^224-2^96+1 to ensure out > in */
    out[0] += two120;
    out[1] += two120m64;
    out[2] += two120m64;
    out[3] += two120;
    out[4] += two120m104m64;
    out[5] += two120m64;
    out[6] += two120m64;

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
    out[4] -= in[4];
    out[5] -= in[5];
    out[6] -= in[6];
}

/* Subtract in mixed mode: out128 -= in64 */
/* in[i] < 2^63 */
static void felem_diff_128_64(widefelem out, const felem in)
{
    static const widelimb two64p8 = (((widelimb) 1) << 64) +
        (((widelimb) 1) << 8);
    static const widelimb two64m8 = (((widelimb) 1) << 64) -
        (((widelimb) 1) << 8);
    static const widelimb two64m48m8 = (((widelimb) 1) << 64) -
        (((widelimb) 1) << 48) - (((widelimb) 1) << 8);

    /* Add 0 mod 2^224-2^96+1 to ensure out > in */
    out[0] += two64p8;
    out[1] += two64m48m8;
    out[2] += two64m8;
    out[3] += two64m8;

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
}

/*
 * Multiply a field element by a scalar: out = out * scalar The scalars we
 * actually use are small, so results fit without overflow
 */
static void felem_scalar(felem out, const limb scalar)
{
    out[0] *= scalar;
    out[1] *= scalar;
    out[2] *= scalar;
    out[3] *= scalar;
}

/*
 * Multiply an unreduced field element by a scalar: out = out * scalar The
 * scalars we actually use are small, so results fit without overflow
 */
static void widefelem_scalar(widefelem out, const widelimb scalar)
{
    out[0] *= scalar;
    out[1] *= scalar;
    out[2] *= scalar;
    out[3] *= scalar;
    out[4] *= scalar;
    out[5] *= scalar;
    out[6] *= scalar;
}

/* Square a field element: out = in^2 */
static void felem_square(widefelem out, const felem in)
{
    limb tmp0, tmp1, tmp2;
    tmp0 = 2 * in[0];
    tmp1 = 2 * in[1];
    tmp2 = 2 * in[2];
    out[0] = ((widelimb) in[0]) * in[0];
    out[1] = ((widelimb) in[0]) * tmp1;
    out[2] = ((widelimb) in[0]) * tmp2 + ((widelimb) in[1]) * in[1];
    out[3] = ((widelimb) in[3]) * tmp0 + ((widelimb) in[1]) * tmp2;
    out[4] = ((widelimb) in[3]) * tmp1 + ((widelimb) in[2]) * in[2];
    out[5] = ((widelimb) in[3]) * tmp2;
    out[6] = ((widelimb) in[3]) * in[3];
}

/* Multiply two field elements: out = in1 * in2 */
static void felem_mul(widefelem out, const felem in1, const felem in2)
{
    out[0] = ((widelimb) in1[0]) * in2[0];
    out[1] = ((widelimb) in1[0]) * in2[1] + ((widelimb) in1[1]) * in2[0];
    out[2] = ((widelimb) in1[0]) * in2[2] + ((widelimb) in1[1]) * in2[1] +
             ((widelimb) in1[2]) * in2[0];
    out[3] = ((widelimb) in1[0]) * in2[3] + ((widelimb) in1[1]) * in2[2] +
             ((widelimb) in1[2]) * in2[1] + ((widelimb) in1[3]) * in2[0];
    out[4] = ((widelimb) in1[1]) * in2[3] + ((widelimb) in1[2]) * in2[2] +
             ((widelimb) in1[3]) * in2[1];
    out[5] = ((widelimb) in1[2]) * in2[3] + ((widelimb) in1[3]) * in2[2];
    out[6] = ((widelimb) in1[3]) * in2[3];
}

/*-
 * Reduce seven 128-bit coefficients to four 64-bit coefficients.
 * Requires in[i] < 2^126,
 * ensures out[0] < 2^56, out[1] < 2^56, out[2] < 2^56, out[3] <= 2^56 + 2^16 */
void felem_reduce(felem out, const widefelem in)
{
    __CPROVER_assume(in[0]<((widelimb)1<<126));
    __CPROVER_assume(in[1]<((widelimb)1<<126));
    __CPROVER_assume(in[2]<((widelimb)1<<126));
    __CPROVER_assume(in[3]<((widelimb)1<<126));
    __CPROVER_assume(in[4]<((widelimb)1<<126));
    __CPROVER_assume(in[5]<((widelimb)1<<126));
    __CPROVER_assume(in[6]<((widelimb)1<<126));

    static const widelimb two127p15 = (((widelimb) 1) << 127) +
        (((widelimb) 1) << 15);
    static const widelimb two127m71 = (((widelimb) 1) << 127) -
        (((widelimb) 1) << 71);
    static const widelimb two127m71m55 = (((widelimb) 1) << 127) -
        (((widelimb) 1) << 71) - (((widelimb) 1) << 55);
    widelimb output[5];

    /* Add 0 mod 2^224-2^96+1 to ensure all differences are positive */
    output[0] = in[0] + two127p15;
    output[1] = in[1] + two127m71m55;
    output[2] = in[2] + two127m71;
    output[3] = in[3];
    output[4] = in[4];

    /* Eliminate in[4], in[5], in[6] */
    output[4] += in[6] >> 16;
    output[3] += (in[6] & 0xffff) << 40;
    output[2] -= in[6];

    output[3] += in[5] >> 16;
    output[2] += (in[5] & 0xffff) << 40;
    output[1] -= in[5];

    output[2] += output[4] >> 16;
    output[1] += (output[4] & 0xffff) << 40;
    output[0] -= output[4];

    /* Carry 2 -> 3 -> 4 */
    output[3] += output[2] >> 56;
    output[2] &= 0x00ffffffffffffff;

    output[4] = output[3] >> 56;
    output[3] &= 0x00ffffffffffffff;

    /* Now output[2] < 2^56, output[3] < 2^56, output[4] < 2^72 */

    /* Eliminate output[4] */
    output[2] += output[4] >> 16;
    /* output[2] < 2^56 + 2^56 = 2^57 */
    output[1] += (output[4] & 0xffff) << 40;
    output[0] -= output[4];

    /* Carry 0 -> 1 -> 2 -> 3 */
    output[1] += output[0] >> 56;
    out[0] = output[0] & 0x00ffffffffffffff;

    output[2] += output[1] >> 56;
    /* output[2] < 2^57 + 2^72 */
    out[1] = output[1] & 0x00ffffffffffffff;
    output[3] += output[2] >> 56;
    /* output[3] <= 2^56 + 2^16 */
    out[2] = output[2] & 0x00ffffffffffffff;

    /*-
     * out[0] < 2^56, out[1] < 2^56, out[2] < 2^56,
     * out[3] <= 2^56 + 2^16 (due to final carry),
     * so out < 2*p
     */
    out[3] = output[3];

    assert(horner(out) < 2*p);
}

static void felem_square_reduce(felem out, const felem in)
{
    widefelem tmp;
    felem_square(tmp, in);
    felem_reduce(out, tmp);
}

static void felem_mul_reduce(felem out, const felem in1, const felem in2)
{
    widefelem tmp;
    felem_mul(tmp, in1, in2);
    felem_reduce(out, tmp);
}

/*
 * Reduce to unique minimal representation. Requires 0 <= in < 2*p (always
 * call felem_reduce first)
 */
static void felem_contract(felem out, const felem in)
{
    static const int64_t two56 = ((limb) 1) << 56;
    /* 0 <= in < 2*p, p = 2^224 - 2^96 + 1 */
    /* if in > p , reduce in = in - 2^224 + 2^96 - 1 */
    int64_t tmp[4], a;
    tmp[0] = in[0];
    tmp[1] = in[1];
    tmp[2] = in[2];
    tmp[3] = in[3];
    /* Case 1: a = 1 iff in >= 2^224 */
    a = (in[3] >> 56);
    tmp[0] -= a;
    tmp[1] += a << 40;
    tmp[3] &= 0x00ffffffffffffff;
    /*
     * Case 2: a = 0 iff p <= in < 2^224, i.e., the high 128 bits are all 1
     * and the lower part is non-zero
     */
    a = ((in[3] & in[2] & (in[1] | 0x000000ffffffffff)) + 1) |
        (((int64_t) (in[0] + (in[1] & 0x000000ffffffffff)) - 1) >> 63);
    a &= 0x00ffffffffffffff;
    /* turn a into an all-one mask (if a = 0) or an all-zero mask */
    a = (a - 1) >> 63;
    /* subtract 2^224 - 2^96 + 1 if a is all-one */
    tmp[3] &= a ^ 0xffffffffffffffff;
    tmp[2] &= a ^ 0xffffffffffffffff;
    tmp[1] &= (a ^ 0xffffffffffffffff) | 0x000000ffffffffff;
    tmp[0] -= 1 & a;

    /*
     * eliminate negative coefficients: if tmp[0] is negative, tmp[1] must be
     * non-zero, so we only need one step
     */
    a = tmp[0] >> 63;
    tmp[0] += two56 & a;
    tmp[1] -= 1 & a;

    /* carry 1 -> 2 -> 3 */
    tmp[2] += tmp[1] >> 56;
    tmp[1] &= 0x00ffffffffffffff;

    tmp[3] += tmp[2] >> 56;
    tmp[2] &= 0x00ffffffffffffff;

    /* Now 0 <= out < p */
    out[0] = tmp[0];
    out[1] = tmp[1];
    out[2] = tmp[2];
    out[3] = tmp[3];
}

/*
 * Zero-check: returns 1 if input is 0, and 0 otherwise. We know that field
 * elements are reduced to in < 2^225, so we only need to check three cases:
 * 0, 2^224 - 2^96 + 1, and 2^225 - 2^97 + 2
 */
static limb felem_is_zero(const felem in)
{
    limb zero, two224m96p1, two225m97p2;

    zero = in[0] | in[1] | in[2] | in[3];
    zero = (((int64_t) (zero) - 1) >> 63) & 1;
    two224m96p1 = (in[0] ^ 1) | (in[1] ^ 0x00ffff0000000000)
        | (in[2] ^ 0x00ffffffffffffff) | (in[3] ^ 0x00ffffffffffffff);
    two224m96p1 = (((int64_t) (two224m96p1) - 1) >> 63) & 1;
    two225m97p2 = (in[0] ^ 2) | (in[1] ^ 0x00fffe0000000000)
        | (in[2] ^ 0x00ffffffffffffff) | (in[3] ^ 0x01ffffffffffffff);
    two225m97p2 = (((int64_t) (two225m97p2) - 1) >> 63) & 1;
    return (zero | two224m96p1 | two225m97p2);
}

static limb felem_is_zero_int(const felem in)
{
    return (int)(felem_is_zero(in) & ((limb) 1));
}

/* Invert a field element */
/* Computation chain copied from djb's code */
static void felem_inv(felem out, const felem in)
{
    felem ftmp, ftmp2, ftmp3, ftmp4;
    widefelem tmp;
    unsigned i;

    felem_square(tmp, in);
    felem_reduce(ftmp, tmp);    /* 2 */
    felem_mul(tmp, in, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^2 - 1 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^3 - 2 */
    felem_mul(tmp, in, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^3 - 1 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp2, tmp);   /* 2^4 - 2 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^5 - 4 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^6 - 8 */
    felem_mul(tmp, ftmp2, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^6 - 1 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp2, tmp);   /* 2^7 - 2 */
    for (i = 0; i < 5; ++i) {   /* 2^12 - 2^6 */
        felem_square(tmp, ftmp2);
        felem_reduce(ftmp2, tmp);
    }
    felem_mul(tmp, ftmp2, ftmp);
    felem_reduce(ftmp2, tmp);   /* 2^12 - 1 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp3, tmp);   /* 2^13 - 2 */
    for (i = 0; i < 11; ++i) {  /* 2^24 - 2^12 */
        felem_square(tmp, ftmp3);
        felem_reduce(ftmp3, tmp);
    }
    felem_mul(tmp, ftmp3, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^24 - 1 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp3, tmp);   /* 2^25 - 2 */
    for (i = 0; i < 23; ++i) {  /* 2^48 - 2^24 */
        felem_square(tmp, ftmp3);
        felem_reduce(ftmp3, tmp);
    }
    felem_mul(tmp, ftmp3, ftmp2);
    felem_reduce(ftmp3, tmp);   /* 2^48 - 1 */
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp4, tmp);   /* 2^49 - 2 */
    for (i = 0; i < 47; ++i) {  /* 2^96 - 2^48 */
        felem_square(tmp, ftmp4);
        felem_reduce(ftmp4, tmp);
    }
    felem_mul(tmp, ftmp3, ftmp4);
    felem_reduce(ftmp3, tmp);   /* 2^96 - 1 */
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp4, tmp);   /* 2^97 - 2 */
    for (i = 0; i < 23; ++i) {  /* 2^120 - 2^24 */
        felem_square(tmp, ftmp4);
        felem_reduce(ftmp4, tmp);
    }
    felem_mul(tmp, ftmp2, ftmp4);
    felem_reduce(ftmp2, tmp);   /* 2^120 - 1 */
    for (i = 0; i < 6; ++i) {   /* 2^126 - 2^6 */
        felem_square(tmp, ftmp2);
        felem_reduce(ftmp2, tmp);
    }
    felem_mul(tmp, ftmp2, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^126 - 1 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^127 - 2 */
    felem_mul(tmp, ftmp, in);
    felem_reduce(ftmp, tmp);    /* 2^127 - 1 */
    for (i = 0; i < 97; ++i) {  /* 2^224 - 2^97 */
        felem_square(tmp, ftmp);
        felem_reduce(ftmp, tmp);
    }
    felem_mul(tmp, ftmp, ftmp3);
    felem_reduce(out, tmp);     /* 2^224 - 2^96 - 1 */
}

/*
 * Copy in constant time: if icopy == 1, copy in to out, if icopy == 0, copy
 * out to itself.
 */
static void copy_conditional(felem out, const felem in, limb icopy)
{
    unsigned i;
    /*
     * icopy is a (64-bit) 0 or 1, so copy is either all-zero or all-one
     */
    const limb copy = -icopy;
    for (i = 0; i < 4; ++i) {
        const limb tmp = copy & (in[i] ^ out[i]);
        out[i] ^= tmp;
    }
}

