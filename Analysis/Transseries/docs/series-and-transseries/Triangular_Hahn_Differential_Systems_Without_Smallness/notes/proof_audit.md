# Proof audit and mathematical boundaries

## Status

This is a research manuscript with conventional proofs and completed finite
regression tests. It has not been checked by a proof assistant or independently
peer reviewed. No exhaustive publication-priority claim is made.

## Exact ambient field

H_n is the full Hahn field over the real coefficient field and real exponent
group R^(n+1), ordered lexicographically. Supports are reverse well ordered in
the monomial growth order. The theorem is not restricted to grid-based or
convergent transseries. The derivative is the strong monomial derivative.
Each greater finite-depth field embeds the old field by zero new exponents.

The complex-coefficient extension keeps the exponent group real. Consequently,
residue coefficients of a split logarithmic derivative must be real, even though
the small remainder may be complex. Oscillatory monomials are not inserted by
an arbitrary order on complex phases.

## Infinite-support proof checkpoints

1. The derivative has only n+1 translated support branches. This establishes
   strongness and zero deepest residue without an infinite coefficient sum.
2. The normalized primitive is constructed blockwise. Noncritical outer blocks
   invert alpha + lower differentiation; each derivative decreases the next
   outer exponent by one. The critical block descends one logarithmic level.
3. In the dominant rank-one case, a^{-1}D decreases the outer x exponent by the
   positive amount d_x(a)+1. This proves Hahn summability of its inverse series.
4. At the critical outer exponent -1, a small tail is removed by a small
   exponential. The remaining operator is diagonal on x^alpha blocks and
   descends to the lower field. Each output fiber can be reconstructed
   independently while the outer support is merely translated.
5. A logarithmic derivative is exactly a real linear combination of the finite
   residue monomials plus a term below the deepest residue. This explicit
   characterization proves all-depth descent; dimension counting alone is not
   used to exclude missing nonpolynomial solutions.
6. Polynomial forcing has a polynomial particular solution after one additional
   logarithm. Any other tower solution differs by an old-field rank-one
   homogeneous solution. Coordinate back substitution therefore proves the
   full triangular all-depth assertion, not just existence of a polynomial ansatz.

The elementary Hahn field and Hahn–Neumann small-support calculus are classical
inputs. They are identified and credited, rather than independently reproved
from set-theoretic first principles.

## Finite-defect algebra checkpoints

D0 G = 1 - QP; G D0 = 1 - KE; EG = 0; GQ = 0; EK = PQ = 1.
The normalized primitive gives PRG = 0, and RK = Q gives GRK = 0 and PRK = 1.
The map G at a nonsplit coordinate is the genuine scalar inverse, not zero.

Strict coordinate triangularity makes (GN)^m vanish. It does not require
coefficient smallness. Formal parameter z acts as differentiation in T and
commutes with coefficient operators; those coefficient operators need not
commute with each other. The finite word formula keeps their order.

The residue matrix is upper triangular with diagonal exactly z. Hence det M=z^r.
Smith units and their inverses preserve polynomial degree. A path with q split
vertices gives the bound max(nu_i)<=q. The independent determinant identity
sum(nu_i)=r counts all split factors, including those in disconnected components.

## What finite certificates establish

Once the entries have been derived from the system, an exact rational solution
of the Toeplitz system certifies bounded degree. An exact left-nullvector with
nonzero pairing with the forcing certifies impossibility at that degree.
A positive certificate at d and a negative one at d-1 certify minimality.

A finite word bound does not make an arbitrary real or infinite Hahn input
computable. Scalar inverses, normalized primitives, multiplication, and residue
queries require exact operations on the chosen representation. The manuscript
states this effectiveness boundary explicitly.

## Mixed example

The middle equation D-a with a=1/(x sqrt(log x)) is nonsplit in all finite
logarithmic depths. Its inverse nevertheless sends -a to 1. This is the
nontrivial residue transfer that changes the effective upper-right entry from
c to c-1. The transfer's full derivative-parameter series has constant monomial
coefficient exactly one, so the effective residue matrix is the exact pencil
[[z,c-1],[0,z]], not only a first-order approximation.

The analytic realization comes from a convergent positive-axis Laplace integral.
Its signed remainders are obtained by a finite geometric identity under that
integral. The analytic homogeneous exponential mode exists outside the finite
logarithmic tower; it does not contradict the formal two-dimensional count.

## Computation boundaries

The exact test count is 1,413. Finite-dimensional models test algebraic splitting
and reconstruction, not the Hahn field itself. Random polynomial matrix-series
cases test Smith/Toeplitz algebra and are not claimed as differential realizations.
The 36 numerical examples use 75-digit mpmath calculations, not interval arithmetic.
General support claims and analytic inequalities rely on the written proofs.

## Claims not made

- No unrestricted nontriangular differential-system theorem.
- No decision procedure for finding a triangularizing gauge or scalar factorization.
- No classification of minimal exponential or oscillatory extensions.
- No analytic convergence or summability theorem for arbitrary Hahn coefficients.
- No componentwise minimum-degree theorem inferred from a whole-vector certificate.
- No Lean verification, independent refereeing, or established global priority.
