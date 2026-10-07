# Formalization plan and certificate interfaces

No Lean file is included: the interfaces below are mathematical specifications,
not compiled code or new axioms. All proposed theorem names are provisional.

## 1. Finite-field algebra

Use an alternating bilinear map on a finite-dimensional vector space over a
field. Do not replace alternation by symmetry in characteristic two.

Suggested concepts:

- `AlternatingPencil A0 A1`: the matrix/form `s*A0+t*A1`.
- `genericHalfRank`: half the rank after extension to `RatFunc k`.
- `directionHalfRank`: half the rank at a point of `ProjectiveSpace k (Fin 2 → k)`.
- `commonIsotropic`: a subspace on which both forms vanish.
- `rankDefect S`: the sum of tested half-ranks minus `(S.card-1)*genericHalfRank`.

Important lemma boundaries:

1. Alternating rank is even.
2. A rank-2r alternating form has maximal isotropic dimension n-r.
3. Common isotropy survives scalar extension.
4. Generic rank cannot be inferred from rational evaluations over finite fields.

A six-dimensional regression test must encode the blocks `s*J`, `t*J`,
`(s+t)*J` over F_2. Their generic rank is six and all three rational ranks are
four. Any rank routine that gives four for the generic rank is unsuitable.

## 2. A small optimality certificate

Input:

- Two alternating n-by-n matrices A0 and A1.
- An n-by-(n-r) matrix U of full column rank.
- A principal index set I of size 2r.

Check:

    transpose(U)*A0*U = 0
    transpose(U)*A1*U = 0
    Pfaffian((A0 + z*A1)[I,I]) != 0  in k[z]

Conclusion: U spans a common isotropic subspace of minimum codimension r.
The dimension lower bound follows by extending scalars and using symplectic
linear algebra. This verification theorem does not require an implementation
of the full pencil canonical form.

## 3. Pfaffian degree budget

The key local lemma is that a 2r-by-2r alternating pencil whose evaluated
rank at a projective point is 2u has Pfaffian vanishing multiplicity at least
r-u there. Prove this by a constant congruence and the matching expansion of
the Pfaffian. It is important that the proof works in characteristic two
without dividing an exterior power by r!.

Distinct projective points correspond to pairwise nonassociate homogeneous
linear factors. Their total multiplicity cannot exceed degree r. This yields
all subset rank-budget inequalities and, by sorting, the unequal-budget bound.

The sharpness constructor only needs the integer lemma:

    R <= floor(sum(K_i for i in I)/(card(I)-1)) for every card(I)>=2
    implies sum(max(0,R-K_i)) <= R.

Distribute the remaining multiplicity arbitrarily and build scalar planes.

## 4. Full existence and defect stability

The normal-form existence theorem is a substantive separate dependency:
regular primary blocks, infinite blocks, singular Kronecker blocks, and the
common radical. The article's common-isotropic existence theorem and the
unconditional defect-stability theorem depend on it.

A certificate-first alternative is to accept a proposed invertible congruence
matrix and block decomposition, check the two congruence identities, and
verify each block's rank profile and chosen restriction. This avoids trusting
the constructor. It does not eliminate the mathematical existence dependency
from a universal theorem without certificates.

For a root-in-S regular Jordan block of length ell, retain its first ell
coordinate vectors and one eigenvector in the second half. Explicitly check
that the surviving pencil is one rooted scalar plane plus radical. The cost
ell-1 equals the block's defect.

## 5. Boolean cubic integration

Definitions:

- Symmetric trilinear tensor over `ZMod 2` on a finite vector space.
- Obstruction `T a a b + T a b b`.
- Torus-valued polynomial using additive differences.

A primitive needs values in `(1/8) Z / Z`; a `ZMod 2`-valued polynomial would
be an incorrect target type. The displayed primitive formula is certified by
coordinate differences modulo eight, followed by the identity
`Delta_(u+v) = Delta_u + Delta_v + Delta_u*Delta_v`.

Coherence is literal addition of chosen primitives but only vector-space
linearity modulo lower-degree polynomials. In particular `2*P` need not be zero.

## 6. Analytic layer

Use normalized counting measure throughout. Prove:

- Fourier square equals a selected cubic cube average.
- Exact phase removal and restriction to a coset on a fixed common space.
- Twisted translations have the prescribed alternating commutator.
- Every invariant nonzero eigenspace has dimension at least 2^r.
- The positive orbit-averaged rank-one operator has trace ||g||_2^2.
- The Boolean shear, valid for functions with zero/nonunit values.

These give the credited scalar energy bound, then the simultaneous theorem.
An actual lower energy certificate needs exact values or rigorous intervals;
unverified numerical logarithms must not be fed into the integer floor bound.

## 7. Scope boundaries

The existing cyclic `proposition_17_2` interface has factorial invertibility
and classical phases. Add a finite-vector-space theorem rather than silently
changing that statement. No common-coset energy lower bound follows merely
from the algebraic restriction theorem. That is a separate research question.
