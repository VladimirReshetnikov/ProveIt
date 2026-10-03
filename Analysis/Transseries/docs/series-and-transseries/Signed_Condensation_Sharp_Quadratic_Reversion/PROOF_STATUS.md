# Proof status and dependency ledger

## Main assertion

The manuscript supplies a self-contained mathematical proof of the precise
quadratic inverse equivalent labeled `conj:quadratic-inverse` in the
repository's finite-core article. The statement is extended to arbitrary
nonnegative finite primitive perturbations and eventually polynomial
quadratic slopes. It is not a Lean proof and has not undergone external
peer review.

## Dependencies

1. Finite signed coefficient identity: ordinary Lagrange inversion, specialized
   and proved explicitly with an auxiliary marker.
2. Bare action sum: Stirling's formula, a strictly concave phase, explicit
   Gaussian curvature, and tail bounds; the weighted form is proved here.
3. Absolute localization: finite composition entropy, a quadratic fusion
   inequality, progressively finer excess/background windows, and a marked
   exponential majorant. The constant multiplying the cloud exponent is
   independent of the cutoff M. This gives arbitrarily accurate polynomial
   error bounds after choosing a sufficiently large fixed M.
4. One-action inverse response: finite analytic implicit inversion and
   formal marker differentiation. A coefficient majorant handles the signed
   analytic multiplier; no positivity of its Taylor coefficients is assumed.
5. Main inverse equivalent and eventual negativity: combine items 2--4.
6. Inverse Borel equivalent: follows from item 5 and a second, real positive
   saddle. Eventual signs permit uniform comparison with the reference sum.
7. Least inverse term: follows from item 5 and a convex continuous phase;
   the index precision proved is o(sqrt(m)), not O(1).
8. Forward-to-inverse cancellation ratio: additionally imports the forward
   equivalent from the repository source, explicitly identified in Section 7.
   This is not needed for items 1--7.

## Points meriting especially close independent review

- The macroscopic row localization and its uniform passage to the fine window.
- The estimate of all background configurations before signed cancellations.
- Independence from M of the cloud exponent constant in the marked-tail bound.
- The distinction between a first marked tail response and truncating the
  original primitive kernel.
- Uniformity of the analytic multiplier bound at the shrinking coefficient saddle.
- Global rather than merely local tail control in the Borel and least-term arguments.

## Computation

255 exact checks passed. Two independent finite formulas are compared, and
the exact marked-tail response is also checked. These are finite tests of
identities, not computer-assisted proofs of asymptotic localization.
The stored high-precision decimals are not directed-rounding enclosures.

## Not claimed

- A sharp smallest sufficient inverse core.
- Explicit finite-degree onset constants or a numerical relative-error certificate.
- A full higher-order inverse expansion.
- General subquadratic inverse asymptotics.
- Angular Borel growth, open-sector summability, or resurgence.
- Equality between a least formal term and an analytic truncation error.
- O(1) precision for the minimizing integer index.
- Formal verification in Lean, or a field-wide priority claim.

## Source scope

The repository snapshot is aab173a7ccdd48add72191d68ce6b0c12ffd72fe.
The source conjecture was explicitly read at that snapshot. The repository
inventory was inspected to distinguish the precise conjecture from existing
forward asymptotics, weighted-type results, and summability articles. This
is a targeted source audit, not a claim-by-claim audit of the entire repo.
