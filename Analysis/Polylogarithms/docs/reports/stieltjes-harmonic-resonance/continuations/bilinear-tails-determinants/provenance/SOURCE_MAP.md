# Source boundary and attribution

The user requested continuation of the ProveIt polylogarithm manuscript and
incoming research directory. The repository was cloned and inspected at
revision `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b` without modifications.

## Project sources inspected

- `Analysis/Polylogarithms/docs/manuscript/README.md` and the relevant
  unified manuscript chapters, especially `04-depth.tex` and
  `04-shuffle-parity.tex`.
- `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/bernoulli-tornheim-digamma/sections/03b_general_hankel.tex`.
- `docs/incoming/README.md` and these five incoming archives:
  - `ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11.zip`
  - `ProveIt_Finite_Difference_Determinants_2026-10-11.zip`
  - `ProveIt_Higher_Quadratic_Jets_2026-10-11.zip`
  - `ProveIt_Higher_Spectral_Defects_2026-10-11.zip`
  - `ProveIt_Quartic_Spectral_Reconstruction_2026-10-11.zip`

The incoming reports themselves refer to earlier snapshots in places. This
package records the actual container revision inspected and identifies each
inherited theorem by report/section, avoiding any claim that the new work
preceded those inputs.

## Inherited exact inputs in the verification directory

`verification/order10/rank_ten_certificate_grouped.json` losslessly regroups
the incoming alternating report’s integer numerator certificate. It contains
439 groups, equivalent to 10,403 expanded coefficients. The full verification
mode independently reconstructs the polynomial from its finite matrix.

`verification/order10/eventual_threshold.py` is the predecessor’s constructive
coefficient-norm calculation, rerun and audited at smaller order ten. The
article reproduces the order-ten threshold argument with explicit constants.
The new proof step is the modulus-2^17 Bernoulli polynomial, coefficientwise
substitution identity, unique residue class, and overlap completing all b.

## New derivations and their checks

The bilinear Gamma laws, rational certificate classification, complete cutoff
jet and translation formulas, real-rational degree theorem, shorter-stencil
rank/pole hierarchy, and order-ten completion were derived in this research
continuation. The project’s source-question map and exact restrictions are
in `integration/STATUS_UPDATES.md`.

The cyclotomic coefficient is deliberately attributed to an existing
manuscript implication. Its integral was checked by independent quadrature,
but its proof uses the printed exact inverse-color and height-one identities.

Primary literature metadata and prior-art limits for the alternating-tail
part are recorded in `literature_notes.md`. The article bibliography contains
the precise primary links used. No comprehensive global priority claim or
external peer-review claim has been established.
