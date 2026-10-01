# Four-dimensional unrestricted mortality with a three-operation reset

A single varying rank-one reset turns the weighted paired-vector scalar
into **four-dimensional unrestricted mortality**. Its entire16-entry
matrix is loaded from the ordinary positive input in **3=2M+1A**
operations. The input dependence is quadratic. All other matrices belong
to one fixed finite alphabet inherited from the universal group theorem.

This improves the dimension of the
[6D quadratic-loader3 construction](group_projective_zero_mortality6.md)
at the same input cost. It complements the
[6D affine-loader2 construction](group_affine_cone_mortality6.md): it does
not supply a five-dimensional affine-loader2 construction. The reset
already contains the correctly loaded weighted vectors, so no separate
input letter, loading-word guard, or restriction on reset positions is
needed. The arithmetic reduction of the unbounded existence predicate
still uses the existing paired-vector compiler; its cost is not reduced
merely by reducing matrix dimension.

## 1. An exact separation inequality

For an integral determinant-one matrix

    P=[p,q;r,s], N=||P||_infinity=max(|p|+|q|,|r|+|s|),

and any real t>1,

    |-p+tq| <= t N.                                  (1)

Equality occurs **exactly** for the two signed rotations

    P=[0,1;-1,0] or P=[0,-1;1,0].                    (2)

Indeed if p!=0, the triangle inequality gives

    |-p+tq|<=|p|+t|q|<t(|p|+|q|)<=tN.

If p=0, determinant one forces q=-r=+1 or-1. The left side is t,
whereas `N=max(1,1+|s|)`. Equality therefore requires and is implied by
s=0. Each matrix in (2) has order4. In particular (1) is strict for
every element of every torsion-free subgroup of SL2(Z).

This last conclusion strengthens the separation lemma used by the
[7D weighted construction](group_affine_weighted_mortality7.md): a
nonzero first diagonal entry is sufficient, but not necessary. The
universal application below retains the specific inherited subgroup
contract; this inequality asserts no universality for arbitrary
torsion-free groups.

## 2. Fixed weighted letters and the universal endpoint

Import the [projective group theorem](group_projective_zero_mortality6.md).
It supplies one finite signed alphabet of pairs `(P_i,Q_i)` generating
a fixed subgroup K_U of `Gamma × Gamma`. Matrices in Gamma have diagonal
entries1 modulo4 and lower-left entry0 modulo4. For fixed program p and
ordinary positive integer input x, put

    alpha=12*2^(p+1), beta=12*2^p,
    t=alpha*x+beta+1, v=(-1,t).

The input is accepted exactly when a paired word satisfies

    (P_word v)_1=(Q_word v)_1=0,
    equivalently P_word v=Q_word v=e2.                 (3)

Only t>1 is needed for the construction's separation; (3) retains the
specified program constants, fixed alphabet and subgroup. Since every
first-block product has first diagonal entry1 modulo4, it avoids (2).

For each signed alphabet letter, precompute the positive integer

    lambda_i=||P_i||_infinity,
    F_i=diag(P_i,lambda_i Q_i).

All F_i are integer matrices, invertible over Q, with determinant
lambda_i^2. Later chronological letters multiply on the left. For a
word w write `Lambda=product(lambda_i)` along its letters. Its fixed
matrix product is `diag(P_word,Lambda Q_word)`, and
`||P_word||_infinity<=Lambda` by submultiplicativity.

Consequently, setting `a=(P_word v)_1` and `b=(Q_word v)_1`, (1) gives

    |a|<t Lambda,
    a+t Lambda b=0 iff a=b=0.                         (4)

The second assertion uses integer b: if b!=0 its weighted absolute value
is at least t Lambda and cannot cancel a. Every inverse group generator
is supplied as a signed alphabet letter with its own positive lambda_i;
its F_i is not the inverse of the scaled forward letter. Different words
for the same group element may therefore have different Lambda. Formula
(4) holds for each word and its own Lambda, which is all that is needed.

The subgroup restriction cannot be dropped. If P is the second rotation
in (2) and Q=-I, then lambda=1 and `(a,b)=(-t,1)`. The weighted scalar is
zero although neither projective coordinate is zero. Such P does not
satisfy the hypotheses of (4).

## 3. The single varying reset

Let

    C=diag(-1,1,-1,1), D_i=C F_i C,
    z_t=(1,t,t,t^2), u=(1,0,1,0), R_t=z_t u.          (5)

This is a fixed integral change of basis, followed by a harmless scalar
sign change of the rank-one reset. Explicitly,

    R_t=[1,0,1,0; t,0,t,0; t,0,t,0; t^2,0,t^2,0].  (6)

Since `z_t=C(v,tv)` and `uC=-u`, every fixed-letter word obeys the exact
identity

    u D(word) z_t = -(a+t Lambda b).                 (7)

Combining (3), (4) and (7) shows that an interior bridge scalar vanishes
exactly for a common paired witness. Unlike the older two-block reset,
R_t has rank one on the **whole four-dimensional space**, rather than a
separate rank-one reset in each block.

We now prove unrestricted mortality, including arbitrary exterior words
and repeated resets. All D_i are invertible over Q. Also

    u z_t=1+t>0, R_t^2=(1+t)R_t.                    (8)

Any matrix word with at least two resets can be written in algebraic
product order as

    M_k R_t M_(k-1) R_t ... R_t M_0,

where each M_j is an invertible product of fixed letters; empty segments
are allowed. Its value is

    [product over 1<=j<k of (u M_j z_t)]
       * (M_k z_t)(u M_0).                           (9)

Both exterior vectors are nonzero, so their outer product is nonzero.
Thus (9) is zero iff at least one interior scalar is zero. Empty interior
segments contribute1+t by (8). A word with no resets is invertible, and
a word with one reset is nonzero. Conversely any zero scalar in (7)
gives `R_t D(word) R_t=0`.

Therefore, for one fixed alphabet of size s,

    x is accepted by program p
      iff {D_1,...,D_s,R_(alpha*x+beta+1)}
          generates the zero matrix.                 (10)

There are s fixed integer matrices and one varying integer matrix of
dimension4. The varying matrix is nonnegative and rank one. The fixed
matrices may have signed entries. No reset count, loading order or
regular-language constraint is imposed on the mortality word. Independent
one-block bridge witnesses cannot erase the blocks separately: their
nonzero whole-space scalar factors simply multiply in (9).

## 4. Literal input arithmetic and remaining certificate boundary

The full matrix (6) has the literal source

    scaled=alpha*x, t=scaled+(beta+1), t2=t*t.

It costs exactly **3=2M+1A**, with zero existential witnesses and
comparisons. Every matrix entry is a copy of0,1,t or t2. Its degree in
the ordinary input is exactly2. Precomputing beta+1, lambda_i and the
fixed conjugated matrices D_i is compilation of fixed data. Fixed signed
integer numerals are permitted, as in the parent matrix constructions;
the varying matrix itself needs no input-dependent negation.

The gain here is a dimension/input-cost tradeoff: unrestricted mortality
now has a4D quadratic-loader3 interface as well as a6D affine-loader2
interface. There is no assertion of globally minimal mortality dimension
or a new numerical75/88 bound. In particular (10) transfers the same
unbounded paired-vector existence predicate used by the paid compiler;
it does not add untyped arithmetic witnesses for Lambda or a matrix word.

For a stable named example, the
[shared-history/strong-unit compiler](group_projective_strong_unit_product.md)
provides its existing279-operation, degree3502 illustration with42
positive witnesses under its fixed-table and padded-program hypotheses.
Later equivalent compiler refinements compose independently. This is an
import of the same endpoint theorem, not a new uniform operation saving.
An arithmetic certificate for a separately supplied arbitrary4D word,
its duration, or its reset positions would still require its own paid
selected-history encoding.

## 5. Exact finite checks

The [source](group_weighted_reset_mortality4.py) and
[receipt](group_weighted_reset_mortality4.json) enumerate the sharp SL2
inequality (1) over bounded entries and several t, checking that its only
equalities are exactly (2). A separate infinite-order cyclic matrix with
zero first diagonal entry illustrates why that entry's nonvanishing is
not necessary. This fixture is not a universal group.

The checker verifies48 ordinary program-input loaders, all16 matrix
entries, every2-by-2 minor and (8). It checks1,536 exact word scalars and
dense two-reset factorizations, and512 full products with arbitrary
invertible exterior words and zero to six resets. Sixteen actual finite
one-relator accepting words have wrong-input mutations rejected and
remain zero inside larger words with extra resets and exterior letters.
Thirty-two pairs of the older separate one-block bridges remain nonzero
with the new shared reset. The rotation counterexample verifies the
missing-group-hypothesis failure explicitly.

These finite alphabets illustrate the parametric proof; the universal
numerical alphabet is not instantiated. Run the checker normally to
compare its deterministic receipt, or with `--write-receipt` to regenerate
it. Universality follows from the inherited theorem and the exact
parametric equivalence (10).

Independent and root proof/source reviews and fresh default receipt
replays passed. A separate matrix implementation also verified192
torsion-free cyclic word/bridge cases and64 dense four-reset zero
products with nonempty exterior words. These tests supplement the
sharp inequality and unrestricted factorization proofs above.

Two independent full proof/source reviews and fresh default replays passed
without findings. They checked the sharp separation lemma, full reset
factorization, fixed-alphabet scope and literal loader. Additional
independent matrix arithmetic checked192 torsion-free cyclic first-block
word/bridge identities and64 dense four-reset zeros with nonempty
exterior words.
