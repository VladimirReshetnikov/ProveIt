# Product-bound helper encoding and half-parameter Pell: 91 operations

This gives a universal system with **91 operations: 49 multiplications
and 42 additions**, 34 positive unknowns, and 22 equations. The supplied
fixed index has three components, in addition to the queried input x.
Fixed numerals and equality tests are free. Start from the 92-operation
half-parameter Pell system and replace its coding equations by

    sigma=(e-ell)*C^2>0,
    ell+sigma+alpha=q,

in place of

    Omega=lambda-e>0, sigma=Omega*(q-C^2)>0,
    ell+e+alpha=q.

The discarded equations supplied a positive unknown Omega. The new
product equation itself implies e-ell>0, since sigma>0 and C=x+g>0.
Consequently Omega is now notation for the computed difference, rather
than a supplied unknown. Eliminating its free equality and supplied
value is exact in both directions: any positive solution of the reduced
system extends uniquely by Omega=e-ell>0.

All other source expressions, including the factored packed mask and
half-parameter Pell block, are unchanged. Relative to
`round35_1980_half_parameter_pell_certificate.py`, the coding change
deletes one subtraction and the now-redundant supplied positivity
equality. This reduces 92 operations, 35 positive unknowns, and 23
equations to the stated counts. The argument below describes a new
admissible fixed index; it does not assert that the old coefficient
index works after the coding source changes.

The finite regression `round36_1980_product_bound_encoding.py` checks the exact
symbolic targets and sparse carries of one compiled circuit. Its receipt
is supplementary evidence, not a substitute for this general argument.

## 1. Why the new positive bound is sufficient

Write C=x+g as before. Since every supplied unknown is positive, C>=2.
Positivity of sigma=(e-ell)C^2 implies that the integer Omega=e-ell is
positive. Thus, without a separate Omega input, the new equations give

    ell<q, sigma<q, C^2<=sigma<q,
    e=ell+Omega<=ell+sigma<q.

Thus S2=ell+e*q<q^2, and g<C<q. No middle-block overflow argument
is needed. This is stronger than the preliminary bound in the published
affine-radix proof. The remaining packing expressions are

    B=H+b+4, H=H0-3, theta=B-4, b=x+beta,
    lambda*(B-1)=q^2-1,
    S2=ell+e*q=V+t*theta,
    S=g+q^2*(S2+q^2*sigma), n=q^8,
    Tplus=q^2*(1+theta*lambda)+ell*(theta*q^4-b),
    r=S*(n^2-n)+Tplus*(n^2-1).

Here H0 is a sufficiently large fixed power of two. Geometry gives
B<=q^2 and 3L<=B<=n. Also theta*lambda>b. Exactly the elementary
inequalities in `AFFINE_RADIX_95_PROOF.md`, Section 3, therefore give

    0<S,Tplus<q^7<n, n^2-1<=r<2n^3.

The retained half-parameter Pell block can now be applied in the order
proved in `HALF_PARAMETER_PELL_92_PROOF.md`, before any coefficient
test: it proves the binomial divisibility condition,
U=4^(2r+1), q=B^L, and that B,q,n are powers of two. Its source equations
have not changed. The proof uses only the displayed packing/growth
bounds, not the discarded formula for sigma.

After this Pell step, b<B<q and ell<q remove the first-block borrow.
The three masks are the same masks as in the affine-radix construction,
with the third one now applied directly to sigma=(e-ell)C^2. The first
mask requires the H0 bit of every permitted coordinate digit to be zero;
the second requires the base-B digits of S2 to be at most three. Since
ell,e<q, its low and high q-blocks are the actual codes ell and e.
The fixed congruence modulo B-4 and the large interpolation threshold
then recover exactly ell=ell0(B), e=e0(B). The third mask requires the
sigma digit to be at most three at every indicator position.

The coefficient construction below deliberately arranges

    e0(T)=ell0(T)+D(T).

It therefore converts the third mask into a direct signed-polynomial
test of D(T)C(T)^2. The main difficulty is that every negative coefficient
of D must occur at an indicator position. Extra positive coefficients,
together with two independently encoded copies of the input, make all
these additional tested positions harmless for true solutions.

## 2. Two helper values and ordinary logical rows

The actual positive input x has weight zero and is not split. Keep the
homogeneous unit delta as one physical coordinate. Every other logical
value is represented by the sum of three distinct nonnegative physical
coordinates; distinct logical values have disjoint physical groups.
The forbidden-bit decomposition is the published one: a value z whose
H0 bit is zero is (z,0,0), otherwise it is

    (z-H0,H0/2,H0/2).

Introduce two reserved logical helpers V0,V1, each represented by its
own three physical coordinates. Neither helper group shares physical
coordinates with any other group. All ordinary circuit and normalization
rows use V0 in place of the actual input. They never mention V1 or x.
Fresh-copy conventions ensure that their expanded square coefficients
are +/-1, and their expanded cross coefficients are +/-2. In particular,
each monomial has exactly two non-input physical factors. Copies are
square differences; repeated gate operands and unit operands get fresh
copies as in the affine-radix compiler.

Before these ordinary rows, introduce four helper rows. For each i=0,1:

* the seed row has base polynomial -x^2, but its intended tested value
  will be Vi^2-x^2 after augmentation by Vi;
* the reverse row has base and intended polynomial x^2-Vi^2, augmented
  by the other helper V(1-i).

The seed is the only case in which a negative base monomial has weight
zero. Its augmentation changes the desired target, intentionally. All
other augmentations preserve their desired row targets.

For each ordinary zero row include both signs. Use the normalization
rows

    X^2-V0^2, Y^2-V0^2, Z^2-V0^2,
    delta_copy^2-delta^2,
    2V0*X-2delta*delta_copy-2u*delta,

with disjoint groups and both signs. Finish with the three unpaired
delta-squared rows from the affine-radix proof. Their last two preceding
positions will be padded by 5x^2 and 7x^2 after the copy equations have
been recovered. These three unit rows are positive and receive no
negative-coefficient augmentation.

## 3. Support, positive augmentations, and coefficient collisions

Give the m true non-input physical coordinates distinct weights

    v_i=8*7^i, 0<=i<m, M=8*7^(m-1).

After division by eight, sums of at most six true-coordinate weights
have base-seven digits below seven. Equality of any such sums is
therefore exactly equality of the corresponding multisets. In
particular, formal degree two cannot equal formal degree four.
The input weight is zero; the seed exception is handled explicitly.

Let s be the number of main rows, including the four helper rows and
the three final unit rows. Put

    d=12M+8,
    t_j=(s+2)d+8M+j*d, 0<=j<s,
    t_last=(2s+1)d+8M, K=t_last+3.

Start with the usual complementary polynomial: a divided coefficient a
of a physical monomial of weight w in row j gives a*T^(t_j-w).
Every nonzero divided coefficient is +1 or -1.

For each negative term at r=t_j-w, choose its helper: V1 for an
ordinary row, its own Vi for seed i, and V(1-i) for reverse i. If the
helper has physical group P, add the six positive terms

    sum_(h<=h' in P) T^(r-v_h-v_h').

The cross multiplicities in C(T)^2 then recover the square of the
logical helper. Mark both every main target and every negative base
exponent r as a tested start. The seed's negative exponent and main
target are the same start.

Here are the exact isolation facts within one row band.

1. At an ordinary or reverse main target t_j, every augmentation has
   complement weight w_negative+w_helper of formal degree four. It
   cannot be completed by a degree-at-most-two monomial of C^2.
   Thus it leaves the original target polynomial unchanged.
2. At a negative position r=t_j-w_negative, the original negative
   term contributes -x^2. Another base term would require
   w_base=w_negative+w_C. Since the non-input base monomials have
   degree two, this forces w_C=0 and the identical monomial. No
   distinct base term contributes.
3. A helper augmentation contributes at r only when
   w_negative_other+w_helper=w_negative+w_C. The helper group is
   disjoint from every negative factor in this row. Multiset
   uniqueness forces the identical negative monomial and w_C equal
   to the helper monomial. The total target is consequently
   Vhelper^2-x^2.
4. In a seed row, there is only the term -x^2 at t_j and its own
   degree-two helper complements. The actual target is exactly
   Vi^2-x^2, as specified.

The same multiset argument proves that positive augmentation
coefficients do not accumulate. The group partition into a negative
pair and a helper pair is unique because their coordinate sets are
disjoint. Within a seed, the six helper monomials have distinct weights.
Ordinary base exponents have degree-two complement, so cannot collide
with degree-four augmentations. Different row bands are separated by
d>12M; all their complementary and relevant product supports are
separated through the last tested position.

Let R be the set of tested starts. Add the positive reset polynomial

    sum_(r in R) T^(r-4).

Each distinct start contributes only once. Finally, at the last two
unit targets t5,t7, add respectively

    T^(t5-1)+sum_(h in P(X) union P(Y)) T^(t5-1-v_h),
    T^(t7-1)+sum_(h in P(X) union P(Y) union P(Z)) T^(t7-1-v_h).

Call the resulting polynomial D. Its main and helper terms are zero
modulo eight, its reset terms are four modulo eight, and its padding
terms are seven modulo eight. These three parts cannot collide. Reset
exponents are distinct; padding exponents are distinct within their
disjoint final row bands. Thus every nonzero D coefficient is +/-1.
All negative coefficients are the original negative terms at starts.

Define ell0 to have digit one at every true-coordinate weight and at
each r,r+1,r+2 for r in R. These positions are distinct apart from the
intentional identification of a seed start with its main target. Set

    e0=ell0+D.

Every negative D coefficient is canceled by an ell0 digit one, and
all remaining coefficients of e0 are zero, one, or two. The highest
nonzero D coefficient is the positive padding term at t_last-1, so
D(B)>0 for every integer B>=2. Both codes are supported below K.

The non-input indicator positions at or above the first row band also
permit dummy C digits. They do not affect any low test: the least D
exponent is at least t_0-4M, the least dummy is at least t_0-2M, and

    2t_0-6M>t_last+2.

The least D exponent is also greater than M, so every true-coordinate
indicator position has zero raw coefficient and zero carry.

## 4. Fixed constants and zero incoming carries

Let c_* count x, all true physical coordinates, and all permitted
dummies. Let D1 be the sum of absolute D coefficients. Choose a power
of two L>3K+2 and then a power of two H0 such that

    H0>max(2*4^(2L+1), 128*max(1,D1)*c_*^2, 3L, 1024).

The supplied fixed index is

    H=H0-3,
    V=ell0(4)+4^L*e0(4),
    Tindex=psi_4(L).

Every construction here is independent of the queried input x. The
same interpolation proof as in the published affine-radix construction
applies: all candidate combined-code digits are at most three, and
the fixed threshold dominates their evaluation at four.

After decoding, every C digit is less than B. Since B is a power of
two and B=H0+1+b>H0, it is at least 2H0. Each raw coefficient of
D(T)C(T)^2 therefore has absolute value at most

    D1*C(1)^2 < D1*c_*^2*B^2 < B^3/256.

The usual signed carry recurrence consequently keeps every incoming
carry in absolute value below B^2/128. No dummy contributes through
t_last+2, so every raw exponent in that range is congruent to zero,
four, or seven modulo eight.

At a tested start r, the two positions r-6 and r-5 are empty. They
reduce the carry entering r-4 to -1 or zero. The raw coefficient at
r-4 is a nonnegative polynomial that contains x^2: its own reset
contributes x^2, and any additional reset contributions are positive.
The other D parts are excluded by residue class. Thus the outgoing
carry from r-4 is nonnegative and below B^2. The empty positions
r-3 and r-2 reduce it to zero.

At every start except t5,t7 the position r-1 is empty. At t5-1 and
t7-1 its exact raw coefficient is respectively

    x^2+2xX+2xY,
    x^2+2xX+2xY+2xZ.

There are no padding contributions at extra negative starts in other
row bands. The two unit rows have no such extra starts. The next two
raw positions r+1,r+2 are always empty.

Every ordinary, helper, and extra negative-position test therefore
receives zero incoming carry and tests its raw coefficient modulo
B^3. A negative nonzero coefficient has top digit greater than three,
by the B^3/256 bound, and fails. In particular, the seed and reverse
tests give both Vi^2>=x^2 and Vi^2<=x^2, hence

    V0=V1=x.

All extra negative-position targets are now zero. Both signs of every
ordinary row must pass, so every such row is exactly zero. The
normalization rows give X=Y=Z=x, delta_copy=delta, and

    x^2=delta^2+u*delta.

Thus 0<delta<=x<B. The three remaining unit tests are precisely the
published affine-radix unit tests: delta^2, delta^2+floor(5x^2/B),
and delta^2+floor(7x^2/B), with two empty following positions. Section
6 of `AFFINE_RADIX_95_PROOF.md` proves from these three tests that
delta=1. Its proof only uses the just-established inequalities and
the exact zero carries/padding coefficients, so applies unchanged.
The homogeneous circuit then gives the represented system at x.

## 5. Necessity and positivity

Given a represented solution, assign both helpers the logical value x.
Use delta=delta_copy=1, X=Y=Z=x, and u=x^2-1. Supply all circuit
values and fresh copies, and split every logical coordinate other than
x and delta by the fixed forbidden-bit decomposition. Set dummies to
zero. Every ordinary/helper/extra-negative target has raw value zero;
the three unit targets have raw value one.

Now choose B to be an arbitrarily large power of two, after all these
physical values and the fixed index have been chosen. Require
B>H0+1+x, every raw coefficient in absolute value below B/4, and
7x^2<B/4. Put

    b=B-H0-1, beta=b-x,
    C=C(B), g=C-x, ell=ell0(B), e=e0(B),
    q=B^L, n=q^8, Omega=D(B), sigma=D(B)*C^2.

The highest coefficient of D is positive, so Omega and sigma are
positive. The encoded delta=1 gives g>0. The degree bound
deg(D*C^2)<3K<L lets B be chosen still larger so that

    alpha=q-ell-sigma>0.

All first-mask digits have the fixed bit clear, both middle-code
digits are at most two, and every third-mask test has digits (0,0,0)
or (1,0,0). This includes all added indicator positions, not merely
the original equation targets. The positive congruence quotient

    t=(ell+e*q-V)/(B-4)

exists because ell0(T)+e0(T)T^L is a nonconstant polynomial with
nonnegative coefficients. Geometry supplies positive lambda. The
binary packing lemma supplies the required binomial divisibility for
the resulting r, and Section 1 gives its growth bounds.

Construct the non-auxiliary Pell witnesses as in Section 7 of
`AFFINE_RADIX_95_PROOF.md`: choose U=4^(2r+1), the binomial ratio value
Y, the main and first Pell coordinates, and the second index L with
fixed psi_4(L). Their hypotheses are the powers of two, binomial
divisibility, and packing/growth bounds already verified.

For the retained half-parameter auxiliary block, write A=a+4 and
D_pell=A^2-1, distinguishing the Pell coefficient from the encoding
polynomial D(T). Its necessity does
require even r, although its sufficiency proof does not. Every true
non-input weight and every indicator position in the new construction
is positive, so B divides g=C-x and ell=ell0(B). Since q is even,
the displayed S and Tplus are both even. Consequently their defining
combination r is even and J=2r+1 is one modulo four.

The auxiliary construction in `HALF_PARAMETER_PELL_92_PROOF.md`,
Section 6, therefore applies: choose m=2cJ, f=chi_A(m),
i=D_pell*psi_A(m)/c^2, and R=i*c^2. Set

    y_aux=psi_R(J), u_aux=chi_R(J)/R,
    o=(u_aux-c)/f, j=(u_aux-J)/c.

That proof establishes the divisibility and strict positivity of
these quantities using J=1 modulo four. It gives exactly

    K*(u_aux^2-y_aux^2)=1-y_aux^2,
    u_aux=c+o*f=2r+1+j*c,
    K=D_pell*(f^2-1)=(i*c^2)^2.

The remaining positive coding witnesses alpha and sigma were
constructed explicitly above. Omega is only the positive computed
value e-ell and is not part of the supplied witness list. This proves
necessity for all 34 positive unknowns of the combined system.

## 6. Exact source and straight-line verification

The complete fresh source residuals and all primitive instructions
are in `round36_1980_product_bound_certificate.py`; the matching JSON
contains their full expanded polynomials. Relative to the predecessor
schedule, replace

    t2=lambda-e             by t2=e-ell,
    bound_sum=ell+e         by bound_sum=ell+sigma,
    S3=t2*code_gap          by S3=t2*C2,

and delete code_gap=q-C2. The subtraction t2 remains one operation.
The bound and product each retain their previous operation counts.
Exactly one subtraction disappears, giving 49 multiplications and
42 additions. The free equality t2=Omega and supplied Omega are
removed for the positivity reason proved at the start of this note.

For a direct comparison of the full source equations, write

    P_old=(lambda-e)*(q-C^2), P_new=(e-ell)*C^2.

Delete predecessor residual 21 (zero-based), the old positive-factor
condition. After aligning the remaining 22 residuals, their only
changes are

    residual 0:  +(sigma-e),
    residual 6:  -q^4*(n^2-n)*(P_new-P_old),
    residual 20: +(P_new-P_old).

These are respectively the bound, the full packed-r equation, and
the positive-product equation. The final auxiliary congruence moves
from old index 22 to new index 21 without any algebraic change.

The certificate checks every equality against its fresh source
residual. Three inherited corrections are triangular. If F_j denotes
source residual j, A=a+4, B=H+b+4, and u=2r+1+j*c, they are

    correction 2  = -lambda*F_3,
    correction 16 = F_15*(u^2-y_aux^2),
    correction 17 = F_3*(kappa+rho*(F_3-2*(A-B))).

Residuals 3 and 15 are independently exact, so these corrections
vanish on the source system without circular reasoning. The checker
also verifies that all retained registers except the product, bound,
and their packed-source dependents are identically unchanged. It
checks all 91 primitive instructions, the precise 49/42 histogram,
all 22 equalities, and participation of every supplied positive input.

## 7. Independent checks and evidence boundary

The finite sparse experiment passes exact symbolic recovery of every
main and extra target in a sample with 35 true coordinates, 25 main
rows, 128 tested starts, 418 indicator digits, and 976 nonzero D
coefficients. It checks all coefficient values and the exact padding
identities. Six canonical assignments and four wide signed-carry
assignments pass; wide tests also reject every negative target.

The general compiler proof received an independent complete review,
including the seed exception, all extra tested positions, carry
clearing, normalization, and positive necessity. The half-parameter
Pell proof is independently reviewed as well; its extra necessity
parity hypothesis has been explicitly verified here. The full
combined arithmetic checker passes with 91 operations and all 22
source equalities. The finite sparse regression supplements these
proofs and does not claim exhaustive coverage of circuit layouts or
integer witnesses. This is an upper bound, with no optimality claim.
