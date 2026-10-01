# Six-dimensional affine-input mortality with a cone guard

The fixed universal paired-vector substrate has a **six-dimensional**
unrestricted mortality adapter with one affine input matrix loaded in
**2=1M+1A** operations. A two-dimensional guard replaces the three guard
coordinates of the [7D construction](group_affine_weighted_mortality7.md).
The four physical coordinates, their strict separation bound, and their
whole-run estimates remain unchanged.

The new guard has the same zero language, `TTF*`, but different scalar
values. Consequently the prior lower bounds for a particular
[rank-three guard and rank-nine scalar series](group_guarded_mortality_rank_obstruction.md)
do not apply. We prove only a scoped one-dimensional guard obstruction,
not a global lower bound for mortality dimension. The numerical75/88
Diophantine bounds are unchanged; Section6 states the uniform-certificate
interface and its limitations.

## 1. Fixed group data and four physical coordinates

Import the exact universal endpoint contract of the
[projective group theorem](group_projective_zero_mortality6.md).
There is one finite signed alphabet of paired matrices `(P_i,Q_i)` in
`Gamma × Gamma`, generating a fixed subgroup K_U. Matrices in Gamma have
diagonal entries1 modulo4 and lower-left entry0 modulo4. For fixed
program p and ordinary positive input x, put

    alpha=12*2^(p+1), beta=12*2^p,
    t=alpha*x+beta+1, v=(-1,t).

Then x is accepted exactly when some paired word has both first
coordinates zero:

    (P_word v)_1=(Q_word v)_1=0,
    equivalently P_word v=Q_word v=e2.                 (1)

The matrix construction below needs t>=3. Its universal corollary retains
the compatible constants and subgroup in (1); an arbitrary affine input
or an arbitrary pair of SL2 matrices does not supply this contract.

For the maximum absolute row-sum norm, precompute the fixed positive
integers and matrices

    lambda_i=||P_i||_infinity,
    F_i=diag(P_i,lambda_i Q_i),
    mu_i=2||F_i||_infinity=2||P_i||_infinity||Q_i||_infinity.

Define

    A_t=[0,-1;1,t], B_t=[0,-1;t,t], T4(t)=diag(A_t,B_t),
    z4=(1,0,1,0), u4=(1,0,1,0).

All matrices are integral. A_t and B_t have determinants1 and t. Every
F_i has determinant lambda_i^2 and is invertible over Q. Each signed
original group letter is encoded separately with its own positive
lambda_i; inverse group letters are not represented by inverting the
scaled F_i.

Later chronological letters multiply on the left. Direct multiplication
gives `T4(t)^2 z4=(v,tv)`. Hence a chronological word `TTF*` has scalar

    s=(P_word v)_1+t Lambda*(Q_word v)_1,
    Lambda=product(lambda_i) over its fixed letters.  (2)

If the first row of P_word is (p,q), then p is1 modulo4, so p!=0. Thus

    |(P_word v)_1|=|-p+tq|
       <=|p|+t|q|<t(|p|+|q|)
       <=t||P_word||_infinity<=t Lambda.              (3)

Since the second coordinate tested in (2) is an integer, (2) vanishes
exactly when both coordinates in (1) vanish. This strict bound prevents
signed cancellation. Without the subgroup condition it fails: the pair
`P=[0,-1;1,0]`, `Q=-I` has lambda=1 and first coordinates `(-t,1)`, so
(2) is zero while both are nonzero.

We also retain the proved whole-run estimates from the 7D packet,
valid for every t>=3 and k>=0:

    ||T4(t)^k||_infinity<=2t^k,
    ||T4(t)^k z4||_infinity<=t^k.                     (4)

Its proof uses the two exact second-order power recurrences, with the
boundary `B_3^6=-27I` handled separately. The false inequality
`||T4(t)||<=t` is not assumed. For an arbitrary chronological word write
its runs as `T^k0 F_i1 T^k1 ... F_im T^km`. Use the initial-column bound
on the first run and charge the factor2 of each later operator bound to
the preceding fixed letter via mu_i. Even zero-length runs are allowed.
Therefore, for every word, including invalid loading orders,

    rho=t^(number of T letters)*product(mu_i),
    ||physical_word z4||_infinity<=rho,
    |u4 physical_word z4|<=2rho.                      (5)

All lambda_i and mu_i are fixed compiler numerals. Lambda and rho are
properties of the word, not free untyped arithmetic witnesses.

## 2. A two-dimensional guard with exactly the required zeros

Take

    C_T=[1,1;0,1], C_F=[1,0;2,1],
    c=(-2,1), ell=(1,0).

Both matrices are integral and have determinant1. Write
`g(w)=ell C(w)c`, with the same chronological multiplication convention.
We claim

    g(w)=0 iff w is T T F*.                          (6)

Before any deviation from this language the successive states are

    c=(-2,1), C_T c=(-1,1), C_T^2 c=(0,1).

The last state is fixed by C_F. If the first F arrives before the second
T, the state becomes either

    C_F(-2,1)=(-2,-3), or C_F(-1,1)=(-1,-1).

Both are in the strict negative quadrant, which is preserved by each
of C_T and C_F. If a further T arrives after `TTF*`, it sends `(0,1)` to
`(1,1)`, in the strict positive quadrant, also preserved by both letters.
These are all possible first deviations. The prefixes with zero or one
T have first coordinates-2 and-1. Thus every invalid word has a nonzero
integer first coordinate, and every `TTF*` word has coordinate zero.
This proves (6) for all finite words, with no length restriction.

The guard itself has exact linear-series rank2: the Hankel minor using
prefixes and suffixes `(empty,T)` is

    [-2,-1; -1,0],

whose determinant is-1. More generally a one-dimensional linear-letter
guard with every letter invertible cannot recognize this zero language.
Its nonzero empty scalar forces both its initial vector and output row
to be nonzero; multiplying nonzero one-dimensional letter entries can
never create a zero scalar. The language `TTF*` has such zeros.

This is only a lower bound within that invertible linear guard model.
It is not a lower bound on a whole mortality construction. Nor is the
new guard the old scalar `number(T)-2+3*(F-before-T pairs)`: on the word
`FT` those two values are respectively-5 and2. The rank-three obstruction
for the old exact series therefore imposes no restriction here.

## 3. Six-dimensional scalar and unrestricted resets

Use the full letters and fixed boundaries

    D_T(t)=diag(T4(t),t C_T),
    D_i=diag(F_i,mu_i C_F),
    z6=(z4,-2,1), u6=(u4,4,0), R=z6 u6.             (7)

For every word in the non-reset alphabet the exact identity is

    u6 D(word) z6 = u4 physical_word z4 + 4rho g(word). (8)

If the word is invalid, (6) makes `|g|>=1`; (5) bounds the first term by
2rho, strictly below the second term's absolute value. The scalar is
nonzero and has the sign of g, including the cases of zero or one T and
negative g. If the word is valid, its guard term vanishes and (2)-(3)
show that (8) is zero exactly for a common paired witness to (1). The
empty fixed suffix after TT gives scalar `-(t+1)` and is not accepted.

The non-reset determinants are

    det(D_T)=t^3, det(D_i)=lambda_i^2*mu_i^2,

so all these letters are invertible over Q. The reset satisfies

    u6 z6=-6, R^2=-6R.                               (9)

For any product with at least two resets, use `R M R=(u6 M z6)R` on
each intervening non-reset segment. The resulting matrix is a nonzero
exterior column times a nonzero exterior row, multiplied by all the
interior scalar factors (8). The exterior vectors are nonzero because
their non-reset products are invertible. Thus the product is zero iff
one interior scalar is zero. A product with zero resets is invertible;
one with one reset is nonzero. Conversely a zero scalar gives a zero
product `R D(word) R`. Empty interior segments contribute-6 by (9).

Consequently arbitrary reset counts and positions cannot synchronize
separate one-block zero words incorrectly. Combining (1), (6) and (8),

    x is accepted by program p
      iff {D_i,R,D_T(alpha*x+beta+1)} generates the zero matrix. (10)

For an inherited signed alphabet of size s, this is s+1 fixed integer
matrices and exactly one input-dependent matrix, all of dimension6.
No regular-language constraint is left on the mortality word itself.

## 4. Literal two-operation input interface

Every entry of the full36-entry matrix D_T uses only0,-1,1,t. Its source is

    scaled=alpha*x, t=scaled+(beta+1).

This costs exactly **2=1M+1A**, with zero existential witnesses or
comparisons. Repeated entries are copies of the same register. Fixed
signed integer numerals are allowed, as in the parent packets.
Computing beta+1, lambda_i, mu_i and the entries2mu_i of fixed D_i is
compilation of fixed data. In particular C_T has only0/1 entries, so its
scaled block requires no hidden multiplication to form2t.

The construction reduces the 7D affine-loader2 interface to6D at the
same cost. At the dimension of the older6D quadratic-loader3 adapter,
it now uses affine matrix entries and one fewer loading gate. This is
an interface improvement, not a proof of minimal dimension or a lower
operation count for the complete universal Diophantine polynomial.

## 5. Finite checks and their scope

The [source](group_affine_cone_mortality6.py) and
[receipt](group_affine_cone_mortality6.json) exhaust all65,535 binary guard
words through length15 against an independent five-state recognizer,
checking the two strict quadrants and the rank-two minor. They replay
2,080 inherited exact power/column bounds and check48 ordinary-input
loaders, full determinants and the36-entry affine template.

Another1,536 exact arbitrary-word calculations compare the new scalar
with its physical-plus-guard formula and the 7D zero set, including393
valid prefixes and1,143 invalid-word nonzeros. They include96 dense
two-reset and64 dense three-reset matrix factorizations. Twelve actual
finite one-relator accepting words have wrong-input, wrong-order and
missing-input mutations rejected. Twenty-four pairs of the old separate
one-block bridges remain unable to kill the shared reset. The explicit
rotation counterexample checks the need for the subgroup hypothesis.

These finite alphabets illustrate the parametric theorem; they do not
instantiate a universal numerical alphabet. Run the checker normally to
compare its deterministic receipt, or with `--write-receipt` to regenerate
it. Universality follows from the inherited group theorem and (10).

## 6. Paid uniform arithmetic remains an endpoint import

Existence of a mortal word in (10) is exactly the paired-vector endpoint
already encoded by the paid four-history compiler. Thus no additional
arithmetic witnesses for the guard, Lambda or rho are required when
representing this existence predicate through that compiler. For a
stable named example, the
[shared-history/strong-unit compiler](group_projective_strong_unit_product.md)
supplies its279-operation, degree3502 illustration with42 positive
witnesses under the same fixed-table and padded-program hypotheses.
Later equivalent compiler refinements can be composed independently.

This transfers the existing endpoint theorem, not a new operation saving
in it. The [9D packet](group_affine_guarded_mortality9.md)'s paid
selected-duration certificates also remain applicable to the same paired
endpoint. Neither transfer certifies a separately supplied arbitrary6D
word, its duration, or its reset positions. Such an explicit word
interface still needs a paid selected-history encoding. The global
numerical75/88 claims are unchanged.

Independent and root proof/source reviews and fresh default receipt
replays passed. Reviews checked the first-deviation argument for every
word, the inherited physical bound, strict subgroup separation, all reset
positions, the exact affine loader and the restricted rank statement.
These finite checks do not replace the all-word and universality proofs.
