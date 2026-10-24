# Incoming-source audit guide

This folder records the source comparison used for the new consistency-equation iteration. The reviewed ProveIt snapshot is

`c1a102936aca437e9999530a0111e6ddab56dc6d`.

The scope is the current `Computability/DiophantineConsistency/con-zfc-diophantine-forms` collection and the five archives then present in `docs/incoming`. Immutable GitHub URLs, archive byte lengths, Git blob IDs and SHA-256 hashes are recorded in `audit_summary.json`.

## Incoming archives inspected

| Archive | Evidence available at the pin |
|---|---|
| `ConZFC_Structural_Reductions_Round11_2026-10-24.zip` | Complete report/component package with literal equations, proofs, fixed coefficients and replay tools. |
| `ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | Complete report/component package; source of the late integer projection family and explicit unresolved four-root obligations. |
| `con-zfc-budget-and-centering-2026-10-23.zip` | Complete report/component package with integer projections, positive equations and a direct-certificate source theorem. |
| `con-zfc-radical-guard-descent-2026-10-23.zip` | Complete report/component package with integer projections, radical majorants and Pell-descent improvements. |
| `report.zip` | Contains only `report.tex`; several referenced `\input` files and literal equation/checker artifacts are absent. |

The first four packages are replayable in principle from their supplied artifacts. This audit did **not** replay all four release roots. It read the relevant mathematical interfaces and literal declarations, replayed Joint Guards' `joint/check_projections.py` successfully, and independently checked the shared six-numeral coefficient values. A package's submitted receipt is distinguished from a replay performed in this iteration.

The tiny `report.zip` can support claims about what its prose proposes. Its claimed twelve-positive-variable degree-70/100-operation and nine-positive-variable degree-1,158,240/811-operation constructions are **not** described here as independently reproduced complete artifacts. In particular, their absence from a literal comparison is not evidence that their prose mathematics is false.

## What was already present

The incoming queue already includes integer variable/degree points 37/4, 30/6, 25/8, 24/10, 23/12, 22/14, 21/20, 20/32 and 19/88, as well as a ten-integer high-degree construction. The eleven-positive-variable degree-277/111-operation improvement and the degree-257/114-operation tradeoff were already delivered. Signed-power/determinant compositions, adjacent-coefficient Pell descent, descending coefficient budgets and a four-root suggestion must therefore receive prior credit.

## Boundary of the current contribution

The current report proves the new ten-positive-variable four-root reduction, of degree 1,152 in 131 binary operations. Its substantive new steps repair the previously unresolved subset-cancellation and mixed-residue problems; it does not impose an unproved extra divisibility condition on canonical witnesses.

The integer component combines the existing transport pivot with later projections, then supplies a new scaled root merger giving 17 unrestricted integers at degrees 112 and 110, and a separate 18-integer degree-80 companion. The pure pivot companions have 21/16, 20/20, 19/32 and 18/88. Domains are part of every comparison. These are new measured constructions relative to the inspected snapshot, not global minima or worldwide novelty claims.

The native/compiler and syntactic-refutation calibration remains an explicitly named inherited ordinary theorem. New algebraic and arithmetic proofs are distinguished from finite literal checks and from an end-to-end Lean/Rocq or encoded object-ZFC derivation.

## Files in this folder

- `audit_summary.json`: immutable incoming-source ledger, comparison points, incomplete-artifact qualifications, coefficient sizes and verification scope.
- `MATHEMATICAL_AUDIT.md`: ordinary proof review of the late transport pivot, surviving exact-degree witnesses, coherent coefficient tuple and inherited semantic boundary.
- `README.md`: this guide.

The final equation components separately contain `independent_review.py` and `certificates/INDEPENDENT_REVIEW.json` for the integer constructions, and `INDEPENDENT_MATHEMATICAL_REVIEW.md` for the ten-positive-variable proof. These are independent implementations/reviews within the AI collaboration, not external human peer review.

No duplicate extraction of an incoming ZIP is needed in this audit folder. The report's actual dependency components retain the source proofs and coefficients needed for their own reproducibility.
