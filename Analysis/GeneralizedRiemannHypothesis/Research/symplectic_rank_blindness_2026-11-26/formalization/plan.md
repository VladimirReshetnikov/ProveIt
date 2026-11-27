# Lean formalization plan

Status: design and proof decomposition only. The new theorem has not been
compiled in Lean. No imported theorem, axiom, or placeholder is being represented
as a completed formal proof.

## 1. Finite algebraic model

Work over a finite field F with cardinality q, using finite coordinate types.
Represent an alternating form as a bilinear form together with its alternating
property; in characteristic two, do not replace alternation by skew symmetry.

Define:

- `Frame H`: injective linear maps F^n -> F^(2n) pulling the ambient standard
  alternating form back to H.
- `topProjection`: the first-coordinate projection of a frame.
- `Isotropic H K`: the form vanishes on K x K.
- `Radical H`: the kernel of the induced map to the dual.
- `Fiber H A`: the finite set of bottom blocks B for which (A;B) is a frame.

Use counting measures initially. Defining probabilities only after the counts
avoids repeated conversions between integers and real or rational numbers.

## 2. Fiber count: the central algebraic obligation

Prove the following sequence of equivalences/bijections.

1. Normalize A by an invertible row map P and source basis change T. Transform
   B to inverse-transpose(P) B T and H to transpose(T) H T. This preserves the
   Gram equation, frame injectivity, kernel dimension, and radical-intersection
   dimension.
2. In A = diag(I_r, 0_k), the Gram equation is equivalent to a prescribed
   alternating difference for B11, fixed B12=H12, and unrestricted B21/B22.
3. The B11 solution set is affine over symmetric r by r matrices. Give an
   explicit coordinate parametrization by diagonal and upper-triangular entries;
   its cardinality is q^(r(r+1)/2) in every characteristic.
4. Under H|K=0, ker(H12) equals K intersect Radical(H). The full frame is
   injective iff B22 is injective on this prescribed t-dimensional subspace.
5. Restriction to that subspace has a fiber of cardinality q^(k(k-t)). Count
   injective restrictions by the ordered-frame product.

Conclude the exact integer fiber count from Lemma 3.3 of the paper. Prefer the
polynomial expression using products (q^k-q^i) before converting to the compact
normalized product with negative exponents.

## 3. Total frame count and uniform orbit model

First count frames without group theory: put H in a symplectic-plus-radical
basis and choose symplectic pairs, then isotropic radical vectors. Prove the
count using induction on the dimension and exact finite cardinalities of
affine linear equation sets.

Separately bridge uniform frames to a uniform symplectic transformation. This
needs the precise finite-dimensional alternating-form version of Witt extension
and equal cardinalities of fibers of the orbit map. If an appropriate existing
Mathlib theorem is unavailable, establish that lemma before claiming the group
sampling interpretation. The probability theorem can first be formalized for
uniform `Frame H`, where this bridge is unnecessary.

## 4. Kernel-type enumeration

Define finite Grassmannians or use submodule counts. Formalize:

- the Gaussian binomial count;
- the isotropic ordered-frame count and its quotient by basis changes;
- the bijection between subspaces K of type (k,t) and triples consisting of
  T <= Radical(H), an isotropic (k-t)-subspace in the quotient, and a graph map
  from that quotient subspace to Radical(H)/T.

These yield the formula N_(n,s)(k,t). A basis-dependent implementation is
acceptable if the equivalence is explicit and the count is independent of the
basis.

## 5. Exact finite probability and TV theorems

Use rational finite probability masses. Formalize total variation as half the
finite L1 difference and prove its equivalent positive-discrepancy and overlap
formulas. This layer then follows from finite sums of the counts:

- all-form likelihood;
- arbitrary-form nullity and full-TV formulas;
- for nonsingular H, all supported likelihoods exceed one;
- nullity likelihood exceeds one exactly at k=0,1;
- exact rank-TV and full-TV identities;
- optimal distinguishing event: non-isotropic kernel;
- optimal rank-only event: nullity <= 1.

The key rank-sign inequality reduces to finite products in [0,1], the product
union bound, and elementary rational inequalities for q>=2. No analytic RH
infrastructure is needed.

## 6. Analytic layer

After the finite theorems, prove positivity and convergence of a_infinity and
B_q, the uniform nullity tail bound from the first kernel moment, and convergence
of finite sums using a truncation argument. This yields the positive delta_q.

For the sharp rank asymptotic, bound products of at least two small factors by
the square of their total sum. For the arbitrary-form rate, formalize the two
kernel moments, the line-count union bound, and the telescoping majorant from
Section 7. The explicit numerical enclosures can then be supplied as rational
certificates checked by computation, with their tail inequalities proved once.

## 7. Suggested integration layout

If later integrated into ProveIt, a suitable new directory would be
`Analysis/GeneralizedRiemannHypothesis/Research/symplectic_rank_blindness/`.
The finite-algebra modules can be developed independently of the large upstream
GRH import graph. No repository write has been performed in this task.

Possible module decomposition:

1. AlternatingFrames
2. ProjectionFiberCount
3. KernelTypeCounts
4. ExactProjectionLaw
5. RankVersusMatrixTV
6. GrowingFormRank
7. LimitConstantCertificates

These are proposed modules, not existing compiled files.
