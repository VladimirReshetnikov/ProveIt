# Formalization plan — mathematical outline, not a checked Lean proof

The new theorems are proved in the report. This file describes a finite
formalization route. It does not contain Lean source, assert exact current
Mathlib API names, or claim that a compiler checked these results.

## Definitions

Work over an arbitrary finite field F of cardinality q.
Use a finite-dimensional vector space V with a nondegenerate alternating
bilinear form. An isometric embedding is an injective linear map preserving
the form. A frame is a linear map from F^d; uniform random frames can first
be expressed as normalized cardinalities of finite types.

Represent source and target forms H,S by matrices, their radicals by
linear-map kernels, and mixed pairings by B^T J X. In characteristic two,
alternation is a separate hypothesis, not just skew symmetry.

## Finite proof chain

1. Alternating-space decomposition: split off a symplectic basis of the
   nondegenerate part; the complement is the radical. Prove even rank.
2. Embedding count: count each symplectic pair, then independent isotropic
   radical vectors. Derive E_m(d,r), including all impossible and
   zero-dimensional cases.
3. Transitivity: extend an isometry of subspaces to the ambient
   nondegenerate alternating space. A direct completion of symplectic
   bases is sufficient.
4. Transverse-subspace count: for disjoint P,T, use a complement W.
   Classify K by K intersect (P+T), its projection L to W, and a graph
   map from L to (P+T)/K0. Count each finite fiber and sum.
5. Joint-kernel equivalence: construct a bijection between source frames
   with a fixed mixed Gram matrix and pairs consisting of an admissible
   K in the radical of the joint Gram form and an embedding of the
   quotient extending the fixed target.
6. Restriction fibers: transitivity proves that the number of embeddings
   extending each target frame is constant. Use cardinal multiplication,
   avoiding division until the final probability statement.
7. Support: combine the maximum transverse-kernel dimension with the
   quotient embedding condition. Prove minimum ambient dimension by
   choosing a maximum kernel.

## Boundary theorem

1. Define the additive group of alternating matrices via upper entries.
2. Prove character orthogonality for finite fields and the one-pair
   identity E psi(u^T Z v)=q^(-rank Z).
3. Multiply Fourier coefficients for independent symplectic row pairs.
4. Derive finite Fourier inversion, the pointwise relative bound, and
   the Parseval total-variation bound.
5. Express conditioning as finite probability ratios. Prove the exact
   observed likelihood before conditioning on injectivity.
6. Use projective-line union bounds for noninjectivity and the
   data-processing inequality for total variation under projection.
7. Establish the explicit error bound and rank-law estimate. Require
   source feasibility s+c >= a-h in every finite statement; the
   Fourier error condition alone does not guarantee feasibility.
8. Obtain convergence by elementary exponential estimates.

## Plane theorem

This is a small independent formalization target: count pairs with
prescribed pairing, derive the two-valued likelihood, and sum positive
and negative discrepancies. It does not need the general quotient law.

## Arithmetic dependencies and trust boundary

No RH, GRH, number-theoretic axiom, infinite-dimensional spectral theorem,
or analytic L-function library is needed. Finite-dimensional linear algebra,
finite field counting, and elementary finite Fourier analysis suffice.
The asymptotic statements additionally use standard real limits.

The Python verifier is supplementary evidence. Its assertions are not
proof terms accepted by a theorem-prover kernel.
