# Proposed ProveIt integration

## Placement

Preserve this complete package as a new continuation under the existing
`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/`
spine, using a directory such as `ordered-hurwitz-cubic-stieltjes`.
Cross-link the cubic sections from `stieltjes-correlation-calculus`.
This follows the thematic division visible at the pinned source snapshot.
Placement is proposed; no repository files were changed by this delivery.

The modular section files support subsequent manuscript integration:

| Source | Suggested role |
|---|---|
| `02_ordered.tex` | Ordered extension of the harmonic/resonant-jet calculus. |
| `03_curves.tex` | Analytic curves, finite-part coordinate dependence, and reconstruction. |
| `04_harmonic_polylog.tex` | Strict/inclusive harmonic normalization, Lerch kernels, derivatives and primitives. |
| `05_cubic.tex` | Coincident-product chapter, following the existing quadratic completion. |
| `06_verification.tex` | Proof-status and verification reconciliation. |
| `07_questions.tex` | Revised exact-identity research agenda. |

Retain the complete authored PDF and sources as a report even if selected
results are merged into the unified manuscript. Regenerate the standalone
file with `build.py` after modifying the modular version.

## Specific status updates

- **Resonant Jets Q1:** answered for every transverse depth-three direction
  and every positive common shift, including the polar divisors and a
  normally convergent remainder. The all-depth one-distinguished-slope
  evaluation is a stronger specialization.
- **Resonant Jets Q3:** answered for every analytic curve whose prefix sums
  are not identically zero. State the exact pole order and the sharp jet
  order `Σν_j + max ν_j`. A curve entirely contained in a polar divisor
  still needs an additional prescription.
- **Coincident Stieltjes cubic target:** completed for all Stieltjes indices
  and all argument-derivative triples in completed Tornheim coordinates.
  The digamma cube is explicitly reduced to the one-variable diagonal
  constant `τ'''(0)`, defined independently by a convergent Mellin germ.
  Its reduction to an ordinary constant algebra remains open here.
- **Gaussian status:** make no change to the short `S6` or revised `S8`
  conjecture entries. Existing proximity and restricted-separator evidence
  retains its existing scope.

## Notation reconciliation

1. Preserve strict ordering `n_1 > … > n_d ≥ 0` and the common shift `a>0`.
2. Preserve `ζ(1+u,a)=1/u+Σ(-1)^m γ_m(a)u^m/m!`.
3. Distinguish the regular germ `R_d`, the Laurent constant on a specified
   spectral curve, and the unit-coordinate spatial Hadamard finite part.
4. The harmonic coefficient satisfies
   `η(a) = −γ_H(1,a) − ζ'(2,a)` in the cited inclusive convention.
5. In the cubic argument-derivative kernel, **both** the triple and pair
   Hurwitz kernels carry arguments `s_i=1+p_i+u_i`.
6. Cubic coefficients are extracted from the holomorphic completion as
   a whole. Unspecified partial derivatives of individual singular
   Tornheim summands at the multivariate origin are not valid substitutes.
7. The classical ordered Laurent and Tornheim inputs must retain the
   bibliography attribution. No first-publication claim accompanies the
   elementary constructions or their consequences.

## Proposed corrections

No newly established source erratum is claimed. Add the explicit
normalization identities and the resolved-question status notes above;
do not attribute an error to a source that was not shown to contain it.
The previous suggested Dougall extension is already addressed in the
incoming material and should not be reopened as if absent.

## Evidence

`claim_ledger.json` maps the article's claims to proof labels and scope.
The exact and independent numerical receipts are under `results/`.
`SOURCE_AUDIT.md` records targeted audit and prior-art limits. The proofs
have internal independent AI review, not external peer review or
proof-assistant certification. All computational evidence remains
supplementary to the analytic proofs.
