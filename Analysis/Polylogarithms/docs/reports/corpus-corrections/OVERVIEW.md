# Corpus corrections: overview of the sources

Reconciliation note, 2026-10-09. `README.md` here is the base delivery's own
README (12's), kept as delivered; this file says how the merged report's
sources fit together. Delivered files are not edited. All sources are
AI-assisted, unrefereed research drafts; nothing is formalized. Placement
`06039f4794`.

**The current status of every correction is kept in one place**: the project
README,
[Status of claims, and known defects](../../../README.md#status-of-claims-and-known-defects)
(commit `58b50f89bf`), which sorts them into false as printed, proposed and
not re-derived, conditional, numerical evidence, and proved since intake. The
registers below are the delivered evidence for it.

## Files by source

**12 `polylogarithms_research`: the base** (unprefixed manuscript; register
`C01`-`C22`)

- `article.tex`: *Real Zeros and Exact Relation Spaces in the
  Polylogarithm–Stieltjes Programme*, generated from `sections/` by
  `code/12-relation-spaces-assemble_article.py`
- `README.md` (delivered)
- `sections/audit_introduction.tex`, `sections/bibliography.tex`,
  `sections/bridge_completion.tex`, `sections/corrections_additional.tex`,
  `sections/corrections_gamma.tex`, `sections/corrections_polylogs.tex`,
  `sections/distribution_ranks.tex`, `sections/gaussian_reduction.tex`,
  `sections/introduction.tex`, `sections/preamble.tex`,
  `sections/research_questions.tex`, `sections/stieltjes_zeros.tex`,
  `sections/verification.tex`
- `12-relation-spaces-CORRECTIONS.md` (the register `C01`-`C22`)
- `code/12-relation-spaces-BUILD.sh`,
  `code/12-relation-spaces-assemble_article.py`,
  `code/12-relation-spaces-run_checks.py`,
  `code/12-relation-spaces-verify_bridge.py`,
  `code/12-relation-spaces-verify_corrections.py`,
  `code/12-relation-spaces-verify_cubic_class_numbers.py`,
  `code/12-relation-spaces-verify_gaussian.py`,
  `code/12-relation-spaces-verify_jet_ranks.py`,
  `code/12-relation-spaces-verify_polylog_corrections.py`,
  `code/12-relation-spaces-verify_ranks.py`,
  `code/12-relation-spaces-verify_shuffle_audit.py`,
  `code/12-relation-spaces-verify_stieltjes_zeros.py`
- `data/12-relation-spaces-ENVIRONMENT.json`,
  `data/12-relation-spaces-PROVENANCE.json`,
  `data/12-relation-spaces-VALIDATION.json`,
  `data/12-relation-spaces-bridge_checks.json`,
  `data/12-relation-spaces-corrections_checks.json`,
  `data/12-relation-spaces-cubic_class_number_certificates.json`,
  `data/12-relation-spaces-gaussian_checks.json`,
  `data/12-relation-spaces-gaussian_shuffle_audit.json`,
  `data/12-relation-spaces-jet_rank_checks.json`,
  `data/12-relation-spaces-polylog_correction_checks.json`,
  `data/12-relation-spaces-rank_checks.json`,
  `data/12-relation-spaces-requirements.txt`,
  `data/12-relation-spaces-stieltjes_zero_checks.json`
- `figures/12-relation-spaces-stieltjes_profiles.pdf`,
  `figures/12-relation-spaces-stieltjes_profiles.png`

**Registers of the other deliveries**

- 06: `06-zero-geometry-AUDIT.md` (`C1`-`C4`),
  `06-zero-geometry-proposed_replacements.tex`
- 10: `10-exact-structure-CORRECTIONS.txt` (`X1`-`X17`, numbered by its
  sections)
- 11: `11-reflection-transition-PROPOSED_CORRECTIONS.md` (seven items),
  `11-reflection-transition-replacement_parity_statement.tex`,
  `code/11-reflection-transition-apply_goncharov_fix.py`
- 13: `13-tower-bundle-stieltjes-zeros-distribution-duality-review.md`,
  `13-tower-bundle-stieltjes-zeros-distribution-duality-corrections.tex`
- 09: its register (`H`, `S`, `CM`, `B`, `EXT` ids) stays with its report,
  [`../herglotz-cyclotomic-obstructions/data/proposed_corrections.json`](../herglotz-cyclotomic-obstructions/data/proposed_corrections.json).

## Corrections found more than once

Base: 12's register, the most systematic one (`C01`-`C22`, with proofs in
its sections). Credit the other registers for the same findings (the intake
dossier's matching, dossier138_POLYLOG §3):

| Correction | 12 | Also found by |
|---|---|---|
| Goncharov letter orientation | C07 | 10 X3, 11 item 3 |
| `S₀` diverges | C06 | 10 X7, 11 item 6 |
| `sec:atoms` "independent atoms" (failed PSLQ ≠ independence) | C03 | 06 C1, 10 X12a, 13 C2 |
| scope of `thm:rank` (now proved, formally) | C04 | 06 C2, 10 X9, 11 item 7, 13 C1 |
| Herglotz criteria, `J(1/2)`, derivative law, Stark field and regulator | C15-C19 | 09 H001, H005, H006/H007, S001, S002 (09 is the base) |
| Clausen parity of the polygamma grid | — | 09 B001, 10 X13, 13 C6 |
| "elementary" remainder in `γ₁″(1/4)` | — | 06 C4, 10 X16d, 13 C4 |

The intake found no proposed correction wrong.

## 12's theorems, credited to the other reports

12 is an omnibus manuscript; its theorems belong to the spines based
elsewhere and are credited there:

- zero theorem and the half-unit bracket `e^{H_{k−1}} < α_k < e^{H_{k−1}} + 1/2`
  (`sections/stieltjes_zeros.tex`) and the trivial-zero bridge with the
  factor `1/2` (`sections/bridge_completion.tex`):
  [`../stieltjes-derivative-zeros/`](../stieltjes-derivative-zeros/) (base
  13; also 06, and for the bridge 10). Cite the half-unit bracket: 13's
  `α_k ≤ e^{H_k}` is weaker.
- rank theorem (`sections/distribution_ranks.tex`):
  [`../rational-grid-distribution-ranks/`](../rational-grid-distribution-ranks/)
  (base 10; also 13).
- `S_{2m−1}` at every weight (`sections/gaussian_reduction.tex`):
  [`../alternating-harmonic-polylogarithms/`](../alternating-harmonic-polylogarithms/)
  (base 11; also 10).

## Caveats

- The prefixed scripts still name their delivered paths; rerun on copies in
  a scratch directory under the delivered names.
- `code/11-reflection-transition-apply_goncharov_fix.py` patches a
  historical draft in place; it has not been run, and must not be applied
  without Vladimir's decision.

## Later corrections (batch 139, 9 October 2026)

Dated note, 2026-10-09. The four continuations of batch 139
([`../gaussian-parity-reductions/`](../gaussian-parity-reductions/), sources 14–17)
deliver no correction register; their integration guides
(`14-exact-reductions-integration_register.*`, `15-parity-ranks-integration_notes.md`,
`16-gaussian-certified-INTEGRATION.md`, `17-gap-reductions-INTEGRATION.md`) map the
manuscript's labels to proofs and stay with that report. Two consequences for the
historical drafts are recorded in the project README's "Status of claims":

- `articles/gaussian-multiple-polylog-depth.tex`, "A sporadic relation: the generator
  space is three-dimensional" (lines 284–292): there is a second, independent
  shuffle relation, `g₂₃ = −6g₄₁ − 3g₃₂ − (3/32)Gζ(3) − π⁵/1536`, so the four
  weight-five generators span at most two directions modulo `π⁵, Gζ(3), β(4)log2`
  (14, 15, 17; checked at intake).
- `reports/binet-malmsten-lambert-bridge__a3c91e07f5d2.md`, section 2 ("The cubic
  moment is open"): 14 cites a published Tornheim-derivative evaluation
  (Bailey–Borwein–Borwein 2015, Theorem 6); not checked at intake.
