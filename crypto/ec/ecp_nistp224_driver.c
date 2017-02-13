#define __CPROVER_assume_limbs_fit_57bit(in) \
    __CPROVER_assume(in[0]<(((limb)1)<<57)); \
    __CPROVER_assume(in[1]<(((limb)1)<<57)); \
    __CPROVER_assume(in[2]<(((limb)1)<<57)); \
    __CPROVER_assume(in[3]<(((limb)1)<<57)); \


typedef unsigned __CPROVER_bitvector[500] ubig;

ubig p = (((ubig)1)<<224) - (((ubig)1)<<96) + 1;

ubig horner(felem in) {
    int l=4;
    ubig out = in[--l];
    while(--l>=0) {
        out <<= 56;
        out += in[l];
    }
    return out;
}

ubig widehorner(widefelem in) {
    int l=7;
    ubig out = in[--l];
    while(--l>=0) {
        out <<= 56;
        out += in[l];
    }
    return out;
}


/*
    __CPROVER_assume(__CPROVER_DYNAMIC_OBJECT(in));
    __CPROVER_assume(!__CPROVER_invalid_pointer(in));
    __CPROVER_assume(__CPROVER_DYNAMIC_OBJECT(out));
    __CPROVER_assume(!__CPROVER_invalid_pointer(out));
*/

//----------------------------------------------------------------------

void check_felem_neg(void) {
    felem in;
    __CPROVER_assume_limbs_fit_57bit(in);
    felem out;
    felem_neg(out, in);
//    assert((horner(in)+horner(out))%p==0);
    assert((horner(in)+horner(out))==4*p);
}

//----------------------------------------------------------------------

void check_felem_diff(void) {
    felem in;
    __CPROVER_assume_limbs_fit_57bit(in);
    felem out;
    __CPROVER_assume_limbs_fit_57bit(out);
    ubig out_old = horner(out);
    ubig in_old = horner(in);
    felem_diff(out, in);
//    assert((in_old+horner(out)-out_old)%p==0);
    assert((in_old+horner(out)-out_old)==4*p);
}

//----------------------------------------------------------------------

#define WIDEBOUND ((widelimb)1<<3)

void check_felem_reduce(void) {
    widefelem in = { 2, 7, 0, 0, 0, 0, 0 };
    __CPROVER_assume(in[0]<WIDEBOUND);
    __CPROVER_assume(in[1]<WIDEBOUND);
    __CPROVER_assume(in[2]<WIDEBOUND);
    __CPROVER_assume(in[3]<WIDEBOUND);
    __CPROVER_assume(in[4]<WIDEBOUND);
    __CPROVER_assume(in[5]<WIDEBOUND);
    __CPROVER_assume(in[6]<WIDEBOUND);
    felem out;
    felem_reduce(out, in);
    printf("%ull %ull %ull %ull\n", out[3], out[2], out[1], out[0]);
    assert(horner(out) < 2*p);
}


