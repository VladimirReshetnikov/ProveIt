# The program bound alone suffices: 116 operations

The separate occurrence of T in the merged bound is redundant in the
complement-zero117 system. Replace

    T+TC+TV+beta_old=q

by

    TC+TV+beta=q.                                (1)

This removes one evaluated addition and gives **116 operations: 56
products and 60 additions/subtractions**, with the same 43 positive
unknowns and 31 equations. The names and domains of the supplied
variables are unchanged; beta has a different value in the explicit
witness correspondence.

The complete source is
`../verification/explore_program_only_serial_bound.py/.json`.
The predecessor
`EXPLORATION_COMPLEMENT_ZERO_SERIAL_COMPOSITION.md` remains frozen.
The proof below establishes every bound in the required order. In
particular it never uses T<=J before the zero flags have been decoded.

## 1. Retained source and the initial polynomial bounds

Retain all other source equations, including

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    2x+alphaI=R,
    FKplus+FKminus=2J+H,
    FZ+FZbar=2J+H,
    6(J-T)=(R-3)(FZbar-J),
    G0=F0+T, G1=F1+T,
    W(A+delta)=A-2x,

where A=F0+F1-2J and delta=FKplus-FKminus. The same paid fixed
threshold gives R>=9, and q>=R^3>=729. Thus H<=J/4. All these are
integer-equation consequences before power recovery.

Both complementary flag pairs give positive fields less than 3J.
The time equation and x>=1 give the established bound

    A<=[W(3J-2)-2]/(W-1)<=9J/2-4,
    F0+F1<=13J/2-4, F0,F1<4q.                    (2)

The complementary top source and positive FZbar now give a weaker
bound than the deleted one, but an adequate bound for starting the
kernel:

    6T=(R+3)J-(R-3)FZbar<(R+3)J,
    0<T<(R+3)J/6.                               (3)

Since R<=q, (2),(3) imply

    G_i<4q+(q+3)q/12<q^2.                       (4)

The last inequality holds for q>=9. Let P6 be the original low six
fields in their unchanged order FKplus,G0,F0,G1,F1,FKminus. Using
(2),(4) and FKplus,FKminus<3q/2 gives

    q^5<P6<(3/2)q^6+5q^5+5q^3+(3/2)q<2q^6.     (5)

For the last inequality it suffices that q>=27: twice the gap is
q^6-10q^5-10q^3-3q, which has strictly positive coefficients after
substitution q=t+27 with t>=0. Our q>=729 is stronger.

The unchanged support equations imply C<TC and V<TV before typing,
using the paid R>2S+1. Equation (1) gives TC+TV<=q-1 and both are
positive, so each is at most 2J-1. Consequently all four native program
fields are at most 3J-1. The two zero flags have the same upper bound.
Appending these six fields to P6 therefore gives the same strict full
window used by the implicit-aggregate-bound121 proof:

    q^11<P
      <2q^6+(3J-1)q^6(1+q+...+q^5)
      <3(q^12-1)/2.                             (6)

The last gap is explicitly

    [2q^12-(q+1)q^6-3q+3]/[2(q-1)]>0.

Its numerator has positive coefficients after q=t+9. Thus r=P and
D0=q^12 satisfy all general-scale43 kernel hypotheses. The kernel
recovers q as a power of three and the required central-binomial
divisibility without assuming parity. The enlarged direct unit-two
mask makes P<q^12 and all twelve normalized q-chunks native, with
unit digit two.

This establishes the whole-word mask, not yet the equality of each
supplied field with its chunk. That distinction is essential below.

## 2. Decode the first sign and use the exact time equation

Write c_i for the carry into field i, numbered from zero, so c_0=0.
Because FKplus<3J, it cannot overflow its native first chunk: its
remainder on subtracting q would be at most J-2. Therefore c_1=0 and
FKplus>=J. The sign-pair equation then gives

    delta=2(FKplus-J)-H>=-H,
    FKminus<=J+H.

The time identity now strengthens (2) to

    A<WH/(W-1)<=9J/32<J,
    F0+F1<3J, F0,F1<3J.                         (7)

For the middle estimate use W/(W-1)<=9/8 and H<=J/4. This argument
uses no typing of either numerical track and no bound T<=J.

## 3. Reach the two zero flags without assuming T<=J

Combining (3),(7), for either guard we have

    G_i+1<3J+(R+3)J/6+1<Rq.                     (8)

Indeed the difference between Rq and the middle expression is
[(11R-21)q+R+9]/12, positive for R>=9. Thus the first guard has
c_2<=R-1. Since q>=R^3 and R>=9,

    F_i+(R-1)<3J+R<2q.                         (9)

It follows that c_3<=1. Applying (8) to G1+c_3 gives c_4<=R-1;
then (9) gives c_5<=1. This is an induction through both guard/base
pairs, not an assumption that either pair has no carry.

The carry entering FKminus is therefore at most one. But

    FKminus+c_5<=J+H+1<=5J/4+1<q.

Consequently c_6=0: no carry reaches the first zero field FZ.
That field is less than 2J+H. If it overflowed, its native remainder
would be less than H-1<J, impossible. Hence c_7=0 and FZ>=J.
The zero-pair equation then gives FZbar<=J+H<q. With no incoming
carry, FZbar is also its native chunk and is at least J, and c_8=0.

Only now use the complementary top source. Since R-3>0 and
FZbar-J>=0, it forces

    T<=J.                                      (10)

This closes the bootstrap without importing the deleted bound.

## 4. Recover the other fields and the complete labelled history

With (7),(10), the original adjacent guard/base proof applies to the
low six fields. If G0 carried once, its native remainder would require
G0>=q+J. The next field F0+1 could not overflow, because its resulting
remainder would be less than J. Thus F0<=q-2, contradicting
G0=F0+T<=q+J-2. So that guard does not carry, and neither does F0.
The same argument handles G1,F1. The supplied FKminus is consequently
its own chunk as well. The zero fields were already recovered.

All four remaining program fields have no incoming carry and are at
most 3J-1. An overflow would again leave a remainder below J, so they
also equal their native chunks. Every field in the source is now typed.

At this point the individual old slacks q-2T and q-TC-TV are positive:
the former follows from T<=J and q=2J+1, and the latter is beta in (1).
Thus the predecessor's decoding lemmas under the individual bounds
apply. The full merged-bound117 theorem is not invoked until its
stronger slack is recovered in the next section.

The predecessor's remaining proof applies unchanged: the two zero
flags type complementary head words, the complement equation gives
the true-zero guard, both numerical tracks have zero top bits and
vanish exactly on required source-zero blocks, and the exact time
equation proves the nonnegative numerical chains. Their even initial
values and zero endpoints force complete three-register banks. The
fixed ROM count marker, state edges, signs and complemented zero labels
give precisely the original graph path and its source tests. Cyclic
entry has the same first-positive-return meaning as before.

No missing program or counter condition is inferred from the scalar
bounds alone: all are recovered only after the typed-field stage.

## 5. The old positive slack is recovered at the same width

The source program and its paid fixed threshold are unchanged. In any
decoded accepting history, the last source counter is one, its sign
is minus and its true zero request is zero. Thus its emitted complement
is one and the highest T block is R/3. The exact previous estimates give

    T<=q/3+q/(2R)-1/2,
    TC<=J, TV<(KS+Zall)H,
    R>12(KS+Zall+1).

They imply T+TC+TV<q at this very width. By (1), beta=q-TC-TV, so

    beta_old=beta-T>0.                          (11)

Replacing beta by beta_old restores the complete117 source with all
other witnesses, including the width, packed word and every Pell
coordinate, unchanged. Conversely any117 solution yields a new116
solution by beta=beta_old+T, which is positive. This is an exact
positive-witness bijection; no widening is required for this reduction.

The first use of the final-source condition occurs here, after the
complete path is decoded. It is not used to start the kernel or to
prove (10).

## 6. Count, universality and evidence scope

The schedule deletes exactly

    combined_sum=program_bound_sum+T

and evaluates program_bound=program_bound_sum+beta. All other
instructions, fixed program numerals and fields are unchanged. Only
one expanded source residual changes, by the explicit slack
substitution (11); the norm correction keeps its old index. The
complete count is 116=56M+60A, with 43 positive unknowns and31 free
equations.

The fixed ordinary-input compiler and cyclic first-return argument
therefore give the same universal family with one fewer operation.
The existing universal90 construction remains smaller.

The checker proves the polynomial bounds and source substitution
symbolically and tests the new carry bootstrap on its own stated
finite ranges. Full canonical coordinates and valuations from117 are
inherited unchanged under (11); any archived canonical receipt is
identified as inherited evidence, not represented as a fresh numerical
Pell construction. The original117 positive-converse proof supplies
the full unbounded witness correspondence.

The maintained regression checks 4,895 preliminary tuples, including
2,937 with T>J. A stage-wise filter retains 70 native first chunks,
including 42 with T>J; 28 also have both zero chunks native and exercise
the deduction T<=J. That coarse sampler has no complete native words,
which is recorded explicitly. A separate targeted test supplies 54
complete native raw/zero prefixes with exact numerical histories,
three digit-split variants and all/no/selective legal zero requests.
Their four program chunks are native placeholders, so these test the
new carry argument and its exact central valuation, not the full ROM.
The two complete117 controller examples remain separately identified
as inherited evidence under the exact symbolic slack substitution.
