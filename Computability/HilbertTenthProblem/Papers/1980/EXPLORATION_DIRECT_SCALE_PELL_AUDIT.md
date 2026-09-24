# Independent audit: supply the squared history scale directly

Audit result: PASS. The completed checker
`../verification/round43_1980_direct_history_length.py` was read in full
and independently rerun. It preserves the fixed-input/fixed-output
finite-history relation of round42. It does not establish a universal
certificate below 90. The complete companion proof is
`EXPLORATION_DIRECT_HISTORY_LENGTH.md`.

## The change and the necessary order of decoding

Remove the instruction Q=q*q and use the supplied positive q wherever
the old schedule used Q. Keep

    q=v*quot, W=v^2, q-1=hrow*(W-1),
    L=q^8, n2=q^12,
    U=w*n2, Y=s*n2.

The four products Q2=q*q, Q4=Q2*Q2, L=Q4*Q4 and n2=L*Q4 construct
all required large powers. No variable exponent has become free.

Positivity of lambda in 3lambda=L-1 implies q>1. The row geometry
then forces v>=2 and q>=v^2=W>=4. All bounds in
`EXPLORATION_IMPLICIT_BOUND_PELL_AUDIT.md` therefore apply with Q=q:
the implicit packing bound gives P<L, and

    q^6<r<q^16<(q^6)^3,
    U,Y>=q^12, E=UY>=q^24>2r+1,
    a=Y(U+1)>q^24, 4r/a<4/q^8<1/2.

The retained kernel recovers U=2^(2r+1) and n2 dividing the central
binomial coefficient. Since U=w*q^12, q is a power of two. Write
q=2^b. The retained equation q=v*quot makes v=2^a for some a>=1.
The geometric equation gives

    2^(2a)-1 divides 2^b-1.

Write b=2at+s with 0<=s<2a. Reducing modulo 2^(2a)-1 shows that
this positive modulus divides 2^s-1, which lies between zero and
the modulus minus one. Hence s=0. Since q>=W, t>=1, and therefore

    q=W^t=4^(at),
    hrow=1+W+...+W^(t-1).

This deduction must occur before extracting separately shifted
Boolean fields from the packed integer. Whole-word periodic-mask
decoding is already valid when q is merely a power of two, because
L=q^8 is then a power of four; the individual q-spaced field boundaries
require the stronger conclusion just proved. No Boolean hypothesis
about hrow or any history field was used to obtain it.

## Exact equivalence of positive witnesses

For clarity denote the old round42 variables by q_old and quot_old.
Given any complete old solution, set

    q_new=q_old^2,
    quot_new=q_old*quot_old.

Keep every other unknown and both endpoint parameters unchanged.
The old equality q_old=v*quot_old gives q_new=v*quot_new. Every other
numeric register and source equation agrees because q_new is precisely
the old Q. All changed witnesses are positive integers.

Conversely, the preceding decoding proves that every complete new
solution has q_new=W^t=v^(2t), t>=1. Set

    q_old=v^t,
    quot_old=v^(t-1).

Again keep every other unknown and both endpoint parameters unchanged.
Then q_old^2=q_new and q_old=v*quot_old, so all old source equations
hold. The quotient is positive even at t=1, when it equals one.
This proves equivalence for all complete positive witnesses, beyond
just a new choice of canonical witnesses.

## Independent arithmetic check

An independent transformation of the actual round42 register list
removed only Q=q*q and replaced Q operands by q. It passed 81
operations: 44 multiplications and 37 additions/subtractions, with
the same 30 positive unknowns and 20 source equations. The retained
Pell kernel remains 43 operations; the outer schedule has 38.

All 20 transformed source residuals expanded exactly, including the
unchanged triangular correction from source 17 into source 18.
The power registers were separately checked as L=q^8 and n2=q^12.
Under the forward witness substitution the first new source polynomial
is exactly

    q_old*(q_old-v*quot_old),

while the other 19 become their old source polynomials identically.
These are exact symbolic checks; no large Pell witnesses need to be
materialized for the witness-equivalence argument.
