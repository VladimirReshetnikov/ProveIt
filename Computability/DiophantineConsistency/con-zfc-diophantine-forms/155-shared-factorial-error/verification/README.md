# Verification receipts

These receipts distinguish exact finite checks from the unbounded mathematical
argument in the report. They are records of this release, not external signatures.

- `release_rebuild_normal.json`: complete parent/core/final verification and a
  seven-step reconstruction in a temporary directory. All 35 selected JSON
  outputs reproduced byte for byte.
- `release_optimized.json`: the same finite verification with Python `-O`.
  Rejection checks remain active when ordinary Python assertions are disabled.
- `parent_replay.json`: an additional direct replay of the retained parent.
- `pdf_qa.json`: PDF pagination, page bounds, render review, and exact parsing
  of all 177 printed quadratic residuals back into their coefficient data.
- `latex_build.log`: the final clean compilation log.
- `INDEPENDENT_MATHEMATICAL_REVIEW.md`: an internal AI-assisted review of the
  new signed-radius, signed-base, digit, and nearest-factorial arguments.
- `SIGNED_POWER_AND_BETA_REVIEW.md`: a second internal review. Its opening
  note distinguishes exploratory history from the final approved construction.

The final equations also have their own recorded checks under `equations/`.
These validate restoration maps, source-row pullbacks, expansions, coefficient
metrics, integral inverses, and deliberate corruption controls. The report
proves the universal arithmetic implications; they are not inferred from
finite tests. No new end-to-end proof-assistant formalization is asserted.
