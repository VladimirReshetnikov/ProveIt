# Proposed formalization plan

This is a plan, not a Lean implementation or build report. No placeholder
axioms are supplied. Suggested declaration names below are interfaces to
prove, not assertions that the declarations already exist in ProveIt.

## 1. Ambient objects and conventions

Use a finite additive commutative group, normalized complex averages, and the
additive circle R/Z. Work with homogeneous symmetric multiadditive tensors.
For V over F_p, include the explicit embedding of F_p into the p-torsion of
the circle. Do not use the repository's multiaffine predicate without first
proving the required interface.

Keep additive polynomial degree distinct from ordinary coordinate degree.
Rational polynomials on integer coordinates descend to finite groups only
after a separately proved periodicity lemma. A primitive on a cover is not
a primitive on the original group.

Suggested objects:

- `cubeProduct`, `normalizedTwistedEnergy`, `topDerivative`;
- `HomogeneousSymmetricTensor`, `IntegrableTensor`;
- `FiniteAbelianCover`, `integratesOnCover`;
- `firstTransferDefect`, `commonIsotropicSubspace`;
- `minimumCoverKernel`, `minimumRepairCodimension`.

## 2. Finite-difference algebra

Prove the full cube expansion for arbitrary complex functions, including
zeros. Prove commutation of differences, pullback invariance, the selected
Fourier-square identity, and the gauge identity with explicit signs and powers.

For circle-valued additive polynomials, prove that the top derivative is
symmetric and multiadditive. Establish the identity
`Delta_(a+b)=Delta_a+Delta_b+Delta_a Delta_b` and the nilpotent operator argument
showing that multiplication by p lowers degree by p-1, down to a constant.
The operator inverse has integral coefficients and is finite on a bounded
polynomial-degree space; no division in the circle group is permitted.

## 3. Two routes to cover primitives

First formalize the universal `M*d!` construction, checking denominator
integrality and the top-derivative coefficient for every multiplicity pattern.
Then formalize the binomial `p^e>d` construction using Vandermonde and the
mod-p binomial theorem.

These yield a finite-group cover primitive in all degrees. The sharper
first-obstruction construction uses only r lifted coordinates and the
polynomial `sum binomial(z_i,p)*y_i/p`. Both periodicity directions and the
full top derivative must be proved. Do not derive its optimality from the
formula alone; the universal lower bound is a separate argument.

## 4. The analytic interface

Use the established ordinary Gowers norm and mixed Gowers–Cauchy–Schwarz.
Prove the exact norm realization on a cover and injectivity of the twisting
pullback map. This gives the twisted triangle inequality and mixed estimate.

For subgroup comparison, first prove the ordinary quotient-profile lemma.
The quotient section need not be a homomorphism: retain the vertex-dependent
carry in the subgroup and remove it by translation invariance of the norm.
Then apply this lemma to the cover and the full preimage of the subgroup.

Formalize the equality examples separately: a globally integrable phase,
and a phase supported on one coset, with probability |G/H|^(-(d+1)).

The full-polydisc maximum reduces to the torus by convexity of a norm power.
The separate assertion that energy one implies a global primitive follows
from equality in an average of unit-disc numbers, including all-zero-direction
cubes. These should not be conflated with stability theorems.

## 5. First-obstruction algebra

Prove bilinearity and alternatingness of
`B_T(a,b)=T(a^p,b)-T(a,b^p)` over F_p. Establish necessity from the order-p
translation relation. Prove sufficiency using the explicit binomial primitive
for odd p and the depth-two Boolean formula for p=2.

This is a formalization of the needed special case of a known theorem
(Tidor's nonclassical integration criterion), not a novelty claim about
that criterion. Prove the exact sequence with alternating forms and the
canonical tensor block normal form.

## 6. Minimum-cover lower bound

This is an especially attractive finite-algebra milestone:

1. Given a surjection `pi:A -> V`, let `K=ker pi`, `U=pi(A[p])`.
2. A primitive on A pulls back along a linear section `U -> A[p]`, so U is isotropic.
3. Define `delta:V -> K/pK` by multiplying a lift by p.
4. Prove lift independence and prove the kernel is exactly U, in both directions.
5. Obtain `V/U -> K/pK` injectively and compare finite cardinalities.
6. Combine isotropic dimension with `|K| >= |K/pK|` to prove `|K| >= p^r`.

The lower bound must quantify over arbitrary finite abelian A, not only
extensions of exponent p^2. Equality forces `pK=0`, `pA=K`, and `p^2A=0`.
The adapted-basis classification then identifies minimum cover classes with
maximum isotropic subspaces. Separately formalize the Lagrangian count.

## 7. Joint and simultaneous repair

Prove rank loss at most twice the restriction codimension. Combine with the
minimum-cover theorem to get the exact single-tensor frontier.

For families, define the maximum common isotropic dimension. The same
lower bound applies to all tensors simultaneously. For the upper bound,
use coordinates adapted to a common isotropic subspace and orient every
nonzero wedge so that its first coordinate is one of the upgraded coordinates.
Check the primitive also when both coordinates have been upgraded.

The family theorem is a variational identity, not a complexity assertion.
For energy selection, preserve the distinction between a vector inequality
in the mean and a single coset preserving every coordinate.

## 8. Extremal reductions and finite computation

Normal form plus gauge invariance plus lossless subgroup comparison prove
rank-only dependence, exact removal of unused coordinates, and reduction
of the maximum over all nonintegrable tensors to one symplectic plane.
Do not assert tensor-product multiplicativity; only the proved product lower
bound and monotonic upper bound are available here.

For the ternary census, use an exact finite type for F_3^2 and all 9^5 cubes.
Accumulate Laurent exponents and coefficients in Z[zeta_3], represented by
integer pairs `(a,b)` with squared modulus `a^2-a*b+b^2`. Reconstruct the
coefficients rather than import an untrusted JSON total. Then prove the
triangle bound and use the convexity lemma to pass from unit phases to
arbitrary disc-valued functions.

A future proof of the conjectured value 11/27 should be a new theorem with
its own certificate. The numerical search must not enter the trusted chain.

## Completion criteria

Use a separate research namespace initially. Record the toolchain and
Mathlib/repository revision, remove all `sorry` and unproved research axioms,
and obtain a successful build. Only after checking the symmetry, codomain,
normalization, and localization interfaces should any result be exported to
the original Section 17 development or a proof ledger updated.
