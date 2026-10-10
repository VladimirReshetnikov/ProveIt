# Herglotz cyclotomic obstructions: overview

Reconciliation note, 2026-10-09. `README.md` here is the delivery's own
README (09's `README.txt`), kept as delivered. Delivered files are not
edited. The source is an AI-assisted, unrefereed research draft; nothing is
formalized. Placement `06039f4794`; the status of every claim and correction
of the PolyLog programme is kept in the project README,
[Status of claims, and known defects](../../../README.md#status-of-claims-and-known-defects).

## Files

Single source, **09 `herglotz_research`**, unprefixed in its delivered
`code/`, `data/`, `figures/` layout:

- `article.tex`: *Cyclotomic Obstructions and Optimal Truncation for the
  Herglotz–Zagier Function*; `README.md` (delivered `README.txt`);
  `MANIFEST.sha256` (as delivered)
- `code/build.py`, `code/certified_intervals.py`, `code/dilogarithm_cores.py`,
  `code/reproduce_figures.py`, `code/truncation_coefficients.py`,
  `code/verify_J_evaluations.py`, `code/verify_cyclotomic.py`,
  `code/verify_derivative_correction.py`,
  `code/verify_interval_cross_checks.py`, `code/verify_recurrences.py`,
  `code/verify_truncation.py`
- `data/J_evaluation_checks.json`, `data/cyclotomic_checks.json`,
  `data/derivative_correction_checks.json`, `data/dilogarithm_cores.json`,
  `data/document_validation.json`, `data/interval_cross_checks.json`,
  `data/proposed_corrections.json`, `data/rank_table.csv`,
  `data/rational_intervals.json`, `data/recurrence_checks.json`,
  `data/recurrence_pairs.csv`, `data/remainder_coefficients.txt`,
  `data/requirements.txt`, `data/source_snapshot.json`,
  `data/theorem_ledger.json`, `data/truncation_checks.json`,
  `data/truncation_quick_checks.json`, `data/verification_run.json`
- `figures/cyclotomic_rank.pdf`, `figures/cyclotomic_rank.png`,
  `figures/optimal_correction.pdf`, `figures/optimal_correction.png`

## Overlap with other deliveries

The theorems here (all-conductor kernel of `β_q(a)`, the five-term reduction
criterion, the `J(2/q)` classification, optimal truncation with rational
certificates for `F(2), F(4), F(8), F(16)`) arrived once. Only the
**corrections** overlap: five of 09's 25 (`data/proposed_corrections.json`)
were also found independently by 12, whose register in
[`../corpus-corrections/`](../corpus-corrections/) lists them as
C15-C19 (`C15`-`C19` ≡ `H001`, `H005`, `H006`/`H007`, `S001`, `S002`, the
intake dossier's matching). 09 is the base for them; credit 12. Their
status is recorded in the project README.

## Caveats

- The relation and reduction results are formal (rational-linear relations
  among the symbols), not transcendence or independence statements.
- The scripts were staged in the delivered layout; rerun on a copy of the
  report directory so that regenerated records do not overwrite the staged
  ones.

## Later sources (batch 141, 9 October 2026)

Dated note, 2026-10-09. Source 23 (`polylogarithms_research_2026-10-10`), placed in
[`../gaussian-parity-reductions/`](../gaussian-parity-reductions/) (placement
`3b0bae5f5a`), has a Herglotz section (`sec:herglotz`) beside this
report's spine. It treats a different limit: derivative order `r → ∞` at fixed `x`, not the
large-`x` truncation of `thm:remainder` and `thm:sharp` here. It gives a finite
Bernoulli–Hurwitz evaluator of `F^{(r)}(p/q)` (a constructive form of Radchenko–Zagier's
rational closure, which it credits), an effective remainder for
`E_r(x) = D_r(x) − ζ(2) − (x/r)(log x − H_{r−1})`, its exact divisor-weighted expansion, a
two-term oscillatory asymptotic of size `x^{3/4} r^{−3/4} e^{−2√(πr/x)}`, and infinitely
many sign changes (`thm:rational-jets`, `thm:herglotz-bound`, `thm:herglotz-sectors`,
`thm:herglotz-oscillation`, `cor:herglotz-signs`). It does not cite this report. Not
re-derived at intake. Files in that report: `code/23-sharp-remainders-verify_herglotz.py`,
`data/23-sharp-remainders-herglotz_checks.json`,
`figures/23-sharp-remainders-herglotz_oscillation.{pdf,png}`.
