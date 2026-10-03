# Restricted noncommuting NAND relations in 72 and 71 operations

The reviewed [73-operation relation](native_controller_noncommuting73.md)
has a sound **72=37M+35A** restriction: use a positive, unshifted tail
rotation quotient and retain the explicit tail-word bound. Fixing that
quotient to its minimum positive value gives a further sound
**71=36M+35A** restriction. Both have an admitted word on which their two
position permutations fail to commute.

These are complete finite relations with progressively narrower
projection predicates. They supply neither a universal compiler nor
ordinary-input initialization or acceptance. The established complete
universal bound remains76. In particular, the sound72 source here is
different from the invalid72 source obtained by deleting the bound from73.

## 1. The exact 72 source

Retain the complete 54-operation selector module and its positive
parameters q,F0,F1,F2. It proves

    q=3^t, H=(q-1)/2, Fi=H+Ti,
    Ti Boolean ternary words, T0+T1+T2=H,
    the first selected label is0.

Use its already paid register `twice_H=2H` and set

    D=2H-F2, S=H+F2-F0.

Thus D is Boolean with units digit1. The digits of S are the two input
counts0,1,2, whose NAND values are the corresponding digits of D.

In addition to q,F0,F1,F2, the positive parameters are R0,R1. Supply
positive E,Q,C,J,B,K0,K1,Z0,Z1 and impose

    D=3E+1,                 q=3Q,
    Q=R0*Z0,                C+J=Q,
    R0*C=E+(Q-1)*K0,
    A=C+Q,                  A+B=S,
    R1*B=D+(q-1)*K1,        q=R1*Z1.                     (1)

A is a computed register, not another supplied coordinate. These are the
same eight new comparisons as in73, except that its shifted tail equation
is replaced by the third line of (1). The explicit positive slack J is
retained.

For d=(1,d1,...,d_(t-1)), define the position permutations

    P_a(d)=rotate_right_a(d1,...,d_(t-1)) followed by(1),
    Q_b(d)=rotate_right_b(d).

When applying P_a to an arbitrary word, append that word's actual initial
digit. This extension makes P_a a permutation, which is the meaning used
when composing P_a and Q_b below.

**Exact projection.** The72 source has positive witnesses precisely when
the selector predicate holds, D has at least two one digits, and there
are offsets a,b with

    R0=3^a, 1<=a<=t-1; R1=3^b, 1<=b<=t;
    E=(D-1)/3, E mod R0>0;
    d=NAND(P_a(d),Q_b(d));
    the digitwise sum of these two input words is S.        (2)

The final line retains the exact selector labels. In particular both
input units digits must be zero. No unrestricted Boolean fixed-point
predicate is substituted for that condition.

## 2. Soundness and positive converse

As in73, E>0 and D=3E+1 imply

    t>=2, Q=3^(t-1), 1<=E<=(Q-1)/2.

The positive factorization Q=R0*Z0 gives R0=3^a with0<=a<=t-1.
The retained slack gives1<=C<=Q-1. The unique representative in this
range satisfying R0*C=E modulo Q-1 is

    C=floor(E/R0)+(Q/R0)*(E mod R0).                     (3)

Indeed (3) is a nonzero Boolean rotation, at most(Q-1)/2, and R0 is
invertible modulo Q-1. Therefore C is typed before using the NAND
constraint. Substitution into the exact routing equation gives

    K0=E mod R0.

Its strict positivity is precisely the extra restriction in (2); in
particular it excludes a=0. The identity tail rotation a=t-1 remains
available because its quotient is E>0.

Now A=C+Q is a Boolean word with top digit1. Positivity and A+B=S<=q-1
give0<B<q-1. The other positive factorization and residue equation
therefore recover the unique Boolean rotation B=Q_b(d), with1<=b<=t
and K1=D mod R1>0. Both ports are typed before A+B=S is decoded digit
by digit. This proves (2).

Conversely, given (2), use (3), put J=Q-C, take B=Q_b(D), and set

    Z0=Q/R0, K0=E mod R0,
    Z1=q/R1, K1=D mod R1.

Every listed number is a positive integer. The rotation identities give
all equations (1), and the reviewed selector theorem supplies every
positive Pell witness. This proves the entire stated positive projection.

## 3. The 71 specialization

Set K0=1 in (1), remove that supplied coordinate, and impose instead

    R0*C=E+(Q-1).                                        (4)

The proof above applies unchanged, with the prefix condition strengthened
to

    E mod R0=1.                                          (5)

Thus71 is complete for exactly the predicate (2) with its positive-prefix
condition replaced by (5). Both offsets are still variable. This is a
restriction of the finite relation, not a claim that an arbitrary73 or72
solution can be converted to71. The bound C+J=Q remains part of the source.

## 4. Exact schedules

The [checker](native_controller_noncommuting72.py) imports the frozen73
schedule. For72 it deletes only

    lhs0=RA0+(Q-1)

and compares RA0 directly with the existing E+(Q-1)*K0 register.
For71 it additionally deletes

    guard0=(Q-1)*K0

and uses the already computed Q-1 in that addition. No source expression
is obtained by treating multiplication by a variable or fixed numeral as
free.

| Relation | M | A | Operations | Equations | Positive auxiliaries |
|---|---:|---:|---:|---:|---:|
| Positive tail prefix |37|35|72|21|27|
| Tail prefix exactly1 |36|35|71|21|26|

Both use six positive parameters q,F0,F1,F2,R0,R1. The source audit expands
all21 comparisons independently in each case, including the inherited
auxiliary-norm correction. All supplied coordinates occur in the source.

## 5. One positive noncommuting point for both relations

Take

    q=243, H=121, (F0,F1,F2)=(122,205,157),
    Q=81, E=28, C=36, J=45,
    R0=3, Z0=27, K0=1,
    R1=27, Z1=9, K1=4.

Then D=85, A=117, B=39, S=156, with low-to-high trit words

    d=(1,1,0,0,1),
    P_1(d)=(0,0,1,1,1), Q_3(d)=(0,1,1,1,0).

Their digitwise NAND is d and their input-count labels are(0,1,2,2,1),
exactly those of the fields. All displayed supplied numbers are positive,
the tail prefix is exactly1, and

    P_1 Q_3(d)=(1,1,0,1,0),
    Q_3 P_1(d)=(1,1,0,0,1).

Thus the position permutations do not commute on this admitted word.
The full positive selector converse supplies the remaining Pell
coordinates. Those huge coordinates are not numerically materialized.

## 6. Why the retained bound cannot simply be dropped

Deleting the bound from72 still admits the old untyped example, now with
the unshifted K0 value:

    q=243, Q=81, H=121, (F0,F1,F2)=(122,133,229),
    D=13, S=228, E=4, C=108, A=189, B=39,
    R0=3, Z0=27, K0=4; R1=81, Z1=3, K1=13.

Every retained equation holds, while C>=Q and A has a trit2. These valid
selector fields again extend through the complete positive kernel.

Even the prefix-one specialization does not by itself imply C<Q. Without
that bound it admits

    q=243, Q=81, H=121, (F0,F1,F2)=(122,157,205),
    D=37, S=204, E=12, C=92, A=173, B=31,
    R0=1, Z0=81, K0=1; R1=9, Z1=27, K1=1.

Again every other equation holds and A is untyped. This is why the valid
71 source retains the bound despite fixing its tail quotient.

One can restrict geometry further: if R0 is fixed to3 as well as K0=1,
then3C=E+Q-1 implies C<Q, and3 divides Q because t>=2. Both the slack and
the separate factorization witness can then be removed. This illustrates
that fixed-geometry slices can keep shrinking. No additional counted
slice is promoted here without a substantive computation compiler for it.

## 7. A uniform structural restriction for every71 solution

The prefix-one condition makes the finite-defect estimate uniform even
when t,a,b vary. Write R_s for full right rotation by s, so
`(R_s v)_j=v_((j+s) mod t)`. Every71 solution satisfies the sharp bound

    Hamming(d,R_(a+b+1)d)<=4.                            (6)

Here Hamming counts unequal positions. This is a consequence of the
actual word restrictions, stronger than bounding the number of positions
where the underlying permutations differ.

First, a=0 is impossible because E mod1=0. The other identity-tail
endpoint a=t-1 is also impossible: then E mod R0=E=1, its rotation
C=1 has units digit1, whereas the fixed first selector requires A=C+Q
to have units digit0. Hence1<=a<=t-2. The prefix equation and the units
condition give

    d0=d1=1,             d2=...=d_(a+1)=0.               (7)

Put P=P_a, Qrot=Q_b and R=R_(a+1). For an arbitrary Boolean word v,
P and R agree except possibly at the last a+1 output positions. On
those positions, in increasing order, their outputs are respectively

    (v1,v2,...,va,v0),       (v0,v1,...,va).

Thus `Hamming(Pv,Rv)` is the number of changes around the cyclic
prefix `(v0,...,va)`.

For v=d, prefix (7) has at most two such changes: when a=1 it is(1,1),
and otherwise it is(1,1,0,...,0). Consequently

    Hamming(Pd,Rd)<=2.                                  (8)

For v=Qrot d, its initial digit is0 because the second input has units
digit0. At every j=2,...,a, equation (7) and the NAND relation force
both input digits to be1. Its prefix is therefore

    (0,beta,1,...,1),       beta in {0,1},

with the evident two-entry interpretation when a=1. This also has at
most two cyclic changes, so

    Hamming(P Qrot d,R Qrot d)<=2.                      (9)

For completeness, the population argument works with these word-specific
errors. NAND substitution gives

    d=(P^2d AND P Qrot d) OR (Qrot P d AND Qrot^2d)
      <= P Qrot d OR Qrot P d.

Set T=R Qrot d. Full rotations commute, so (8) also bounds the Hamming
distance from Qrot P d to T by2; (9) does the same for P Qrot d.
Each of these words has T's population, hence has at most one one-bit
outside T. Their union contains at most two such positions. The
displayed inequality implies that d has at most two one-bits outside T.
Since d and T have equal populations, their Hamming distance is at most4.
This proves (6).

In particular, traverse each orbit of the rotation by a+b+1. There are
at most four bit changes in total over all these cyclic orbits; at most
two orbits can be nonconstant. The number of constant orbits need not
be bounded by this argument. This orbit description is a necessary
uniform restriction, not a complete classification or a decidability
theorem for the varying parameters.

The bound4 is attained by the exact71 semantic point

    t=8, a=b=2,
    d=(1,1,0,0,1,1,1,0),
    P_a(d)=(0,1,1,1,0,1,0,1),
    Q_b(d)=(0,0,1,1,1,0,1,1).

The inputs have units digit0 and NAND to d; the tail prefix is1.
Rotation by a+b+1=5 gives `(1,1,0,1,1,0,0,1)`, differing at four
positions. Taking selectors from the displayed input counts and applying
the positive converse supplies a full positive71 point. Thus the example
proves sharpness, without materializing its Pell coordinates.

There is also an explicit family with an arbitrary number of independent
binary choices. For any k>=0 let t=10k+5, a=1 and b=t-2. Choose U by
concatenating k independently selected blocks `01011` or `01101`, and
define the cyclic length-t word

    w = 1 U 0 11 0 (11010)^k.

In cyclic order its zeros are isolated and all its runs of ones have
length1 or2; this holds within each listed block and across every displayed
boundary. Hence `w_j=NAND(w_(j-1),w_(j+1))`. Since t is odd, define d
bijectively by

    d_(2j mod t)=w_j.

Writing m=(t-1)/2, the construction gives w0=1, w1=w_(t-1)=0,
and w_m=w_(m+1)=1. Thus

    d0=d1=d_(t-1)=1,          d2=d_(t-2)=0.

It follows that P_1d=R_2d and Q_b d=R_(-2)d. The neighbor NAND equation
for w therefore gives the required NAND equation for d, with both input
units digits zero and E mod3=1. Its input counts determine valid selector
fields, so the positive71 converse applies. Moreover Q_b d begins `(0,1)`.
Consequently P_1 Q_b d differs from R_2 Q_b d=d at exactly two positions,
whereas Q_b P_1d=d. Every constructed point is noncommuting on its word.

For each k the different block choices give2^k distinct words d and thus
distinct semantic71 points. Here the composed rotation R_(a+b+1) is the
identity, so the family is compatible with (6). The independently chosen
blocks form a regular family; this construction proves neither universal
computation nor undecidability. It shows why the uniform Hamming bound
must not be interpreted as a bounded number of admissible words or a
complete complexity classification.

## 8. Evidence and scope

The [receipt](native_controller_noncommuting72.json) is checked by default.
The author replay verifies the two exact schedules and1,126,810 arbitrary
positive-port candidates through length6. It finds9 admitted72 cases and
2 admitted71 cases, checks the common noncommuting point, and checks both
invalid bound deletions. The finite enumeration supports the separately
proved projection; it is not a universality test.

The additional checker enumerates prefix-one Boolean words directly,
independently of the arithmetic port enumeration, through length17. It
checks the exact cyclic-prefix comparisons, the word-specific population
bound and the sharp example in Section7. This is separate finite evidence
for the proved structural lemma, not a universality or decidability test.
It also checks all511 free-block choices for0<=k<=8, including their
positive outer coordinates, through length85. The general family is
proved above; this finite check is separate corroboration.

No full complexity classification for the variable offsets has been
established. Noncommutation, a smaller
operation ledger, and a nonempty relation do not by themselves implement
arbitrary circuit incidence or an accepting computation. The author audit
and an independent full scoped proof/source/default-receipt review pass,
including both positive projections and both bound-deletion counterexamples.
The Section7 uniform bound and arbitrary-block family also have an
independent full proof/source/default review pass, including all511
finite block choices and the exact failure of commutation.
