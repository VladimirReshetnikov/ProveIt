# Order jets: proof review and reconciliation, 12 October 2026

The delivered mathematical source has been read against the earlier shifted
q-factorial completion. Its original files remain unchanged. The conventional
proofs below are accepted for subsequent synthesis; this is not a Lean audit.

## Scope and analytic checks

- The parity sign is fixed before differentiating the entire order family.
  Mellin residues at the moving collision give the all-order finite jet
  polynomial; Bernoulli reflection removes its explicit Stieltjes residue,
  but does not remove every logarithm.
- The reflected functional equation identifies the actual analytic remainder
  as a convergent divisor/polylogarithm series. A zero base Borel kernel does
  not identify that remainder as zero. At m=1 this overlaps the host report;
  the first-jet completion is the extension to retain.
- The first derivative has a double-pole kernel with zero simple residues.
  Ordinary Cauchy principal value diverges there. Integration by parts gives
  the stated Hadamard finite part, and clockwise upper-minus-lower contours
  give the factor pi*i multiplying the hidden reflected block. The separately
  identified logarithmic dual block must also be retained in the exact jet.
- Off-lattice normal convergence, ray growth, and the differentiated Mellin
  product justify the operations; logarithmic differentiation is handled as
  the derivative of Gamma*zeta rather than by introducing false poles at
  zeta zeros. Real shifts strictly between 0 and 1 remain a hypothesis.
- Divisor inversion followed by a Vandermonde system gives the finite atomic
  detection statement. The midpoint grid proves sharpness. The finite-measure
  generating-function proof isolates Lebesgue measure as the simultaneous
  base/first-jet kernel. Formal Bernoulli moments need no extra endpoint
  hypothesis; integrating the actual functions requires the stated logarithmic
  integrability. Endpoint atoms and general complex shifts are not included.

## Correction to the proposed documentary correction

The delivery calls the host's Conjecture 5 equation locator a confirmed
mismatch. Live inspection of arXiv:2506.08265v2 shows a format distinction:
[HTML equations (60a)-(60b)](https://arxiv.org/html/2506.08265v2) and
[PDF equations (3.36a)-(3.36b), printed page 17](https://arxiv.org/pdf/2506.08265v2)
identify the same formulas. The existing 60a/60b locator is valid for HTML.
Accordingly, use both format-specific locators in future editing; do not
describe this as a mathematical error or an incorrect HTML reference.
Keep the existing internal labels eq:FR60a and eq:FR60b. The delivered
correction note is preserved as evidence, with this qualification beside it.

## Fresh evidence and integration

The unchanged verifier passed 732 exact assertions and 61 numerical
assertions on an isolated copy (Python 3.14.4, SymPy 1.14.0, mpmath 1.3.0).
Fresh results and logs are in intake-verification. Numerical agreements,
including rounded zero residuals, are not interval certificates.

The natural collective placement is the Hurwitz/order-derivative material
in Volume III, with a cross-reference from the Lambert completion discussion.
The all-order collision formula, first-jet completion and measure theorem
need an organic shared-notation synthesis. They have not yet been inserted
into the collective TeX or any rebuilt volume. Higher global jets, unknown
support recovery, complex shifts and nonlinear critical inversion remain
separate research problems.
