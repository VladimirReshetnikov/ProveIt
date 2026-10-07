# Proposed formalization roadmap

This file is a dependency design, **not Lean source**, and makes no claim that
any proposed declaration already exists in Mathlib or the ProveIt project.
No theorem in this package has been checked by a Lean kernel.

## Recommended first milestone: the exact binary cubic upper bound

Work on a finite-dimensional F_2-vector space V, with normalized finite sums.
Separate abstract finite vector spaces from any later field-extension encoding.

Suggested mathematical declarations (names are proposals, not APIs):

1. `cubicObstruction(T)`:
   C_T(a,b) = T(a,a,b) + T(a,b,b) for symmetric trilinear T.
   Prove bilinearity and alternation directly.
2. `diagonalCubic_polar`:
   Q(a) = T(a,a,a) has polar form C_T.
3. `quadraticWalsh_sq`:
   For kappa(a)=(-1)^(Q(a)+L(a)), each normalized Walsh coefficient has square
   zero or 2^(-rank C_T). Prove by expanding its square and character orthogonality.
4. `quadraticConvolution_norm`:
   The L2 operator norm is 2^(-rank C_T/2), or formulate squared norms to avoid
   unnecessary square-root manipulations.
5. `twistedCube_reparametrize`:
   The bijection b=a+A, c=a+B, y=x+a separates even and odd vertices into
   two parallelograms. Check every vertex explicitly.
6. `mixedCubic_bound`:
   Apply the convolution bound and L2 Cauchy–Schwarz to those products.

This first milestone does not require nonclassical polynomial integration.

## Second milestone: sharpness and seven-function restriction

7. Constructive alternating-form decomposition into rank-two wedges and a
   maximal isotropic subspace of codimension rank/2.
8. Define the elementary symmetric trilinear S_(ell,m); compute its obstruction.
9. Verify the explicit binary residual integrator
   P(x)=sum r_i x_i/8 - sum r_ij x_i x_j/4 + sum r_ijk x_i x_j x_k/2 mod 1.
   It is reasonable first to encode numerators in ZMod 8 and map into circle phases.
10. Prove one symplectic block has bias 1/2 and independent blocks multiply.
11. Obtain the exact cube norm and common-function extremizer.
12. Express the Cauchy–Schwarz expansion of the seven-function correlation as a
    mixed cube; deduce rank <= 4 log_2(1/delta) and codimension <= 2 log_2(1/delta).
    A logarithm-free intermediate statement delta^2 <= 2^(-rank/2) is cleaner.

The exact agreement result then needs only the elementary inequality
Re E Z >= 2 Pr(Z=1)-1. The stability identity can be added after orthogonal
projections onto positive/zero/negative Walsh eigenspaces have been defined.

## Third milestone: scalar and trace algebra

- Scalar cyclic finite differences and the valuation recurrence.
- Optimal scalar root order, via interpolation over Z/p^R Z with unit Vandermonde.
- Coordinate integration at d<=p+1.
- Trace/Frobenius adjoint identity.
- Nondegeneracy of the finite-field trace pairing.
- Radical equation c^p a^(p^2)=c a.
- Root counting in the cyclic multiplicative group and gcd(p^2-1,p^n-1).
- Exact maximum isotropic dimension and trace classification.
- Elementary repair number; keep ordinary slice rank a separate definition.

## Certificate approach

A producer may output an obstruction matrix, symplectic basis, wedge pairs,
residual symmetric coefficients, and a phase numerator polynomial. A small
verifier should check matrix equalities and coefficient identities; the formal
lemmas would then turn those checks into conclusions about all cubes.

The current Python program illustrates certificate data but uses ordinary
runtime assertions, not proof terms. Its finite-field tables are only for
small examples. Avoid exporting an exponential truth table as the intended
large-dimensional mathematical representation: keep the cubic polynomial
coefficient list instead.

## Integration precautions

The repository already has Gowers-norm and phase-absorption material. Search
its actual current declarations before choosing final names or imports.
Do not assume a file named `Section17.lean` exists at the top project level;
the inspected project layout is nested and includes wrapper files.

Fix conjugation conventions first. The article uses forward binary cubes for
the sharp theorem and backward cubes for the all-characteristic untwisting
identity; in general characteristic an unnoticed parity sign is not harmless.
