# Square-root degree bound

Merged research report on finite observations of `N` uniform signs: cell
Fourier degree against retained variance `Var E[H_N | F]` on the Boolean
cube, refining openai/math family 192 ("Unbounded Violations of the
Square-Root Degree Bound"). Four AI-assisted, unrefereed manuscripts;
nothing is formalized. The report's article/README write is still pending;
this README is a short file list with dated reconciliation notes. Delivered
files are not edited.

## Sources and files

**01 `Fourier_Codimension_Research`: the base** (placed `97f51e381a`;
unprefixed manuscript, `01-codimension-` code and data)

- `fourier_codimension.tex`; `sections/codimension.tex`,
  `sections/context.tex`, `sections/explicit_gaussian.tex`,
  `sections/minimality.tex`, `sections/observations.tex`,
  `sections/quantitative.tex`, `sections/references.tex`,
  `sections/reporter.tex`, `sections/research.tex`, `sections/witness.tex`
- `figures/exceptional_cell.pdf`, `figures/parity_bounds.pdf`
- `code/01-codimension-enumerate_reporters.py`,
  `code/01-codimension-enumerate_two_leaf_integer.py`,
  `code/01-codimension-make_figures.py`,
  `code/01-codimension-run_verification.py`,
  `code/01-codimension-verify_constants.py`,
  `code/01-codimension-verify_witness.py`
- `data/01-codimension-constant_certificate.json`,
  `data/01-codimension-minimality_certificate.json`,
  `data/01-codimension-minimality_n6_independent_integer.json`,
  `data/01-codimension-provenance.json`,
  `data/01-codimension-verification_summary.json`,
  `data/01-codimension-witness_certificate.json`

**02 `Boolean_Fourier_Correlations`** (placed `97f51e381a`; manuscript not
staged, retrievable from `933cf7f7b`)

- `02-correlations-PROVENANCE.txt`
- `code/02-correlations-Makefile`,
  `code/02-correlations-verify_bias_transfer.py`,
  `code/02-correlations-verify_binomial_reporter.py`,
  `code/02-correlations-verify_restriction_transfer.py`
- `data/02-correlations-bias_transfer_certificate.json`,
  `data/02-correlations-binomial_reporter_certificate.json`,
  `data/02-correlations-restriction_transfer_certificate.json`

**03 `parity_moment_cancellation`** (placed `d2ccfed6de`; manuscript not
staged, retrievable from `d96a456d2`)

- `code/03-parity-moments-Makefile`, `code/03-parity-moments-make_figures.py`,
  `code/03-parity-moments-verify.py`
- `data/03-parity-moments-SOURCE_PROVENANCE.json`,
  `data/03-parity-moments-VALIDATION.json`,
  `data/03-parity-moments-finite_variance_table.tex`,
  `data/03-parity-moments-mellin_errors_table.tex`,
  `data/03-parity-moments-verification_results.json`
- `figures/03-parity-moments-profile_and_support.pdf`

**04 `effective_fourier_growth`** (placed `18abb81b20`; manuscript
*Effective Power-Law Fourier Growth from Low-Degree Observations* not
staged, retrievable from `fcfe6ef6a`)

- `04-effective-growth-CLAIMS.md`, `04-effective-growth-FORMALIZATION.md`,
  `04-effective-growth-PROVENANCE.md`
- `code/04-effective-growth-Makefile`, `code/04-effective-growth-verify.py`
- `data/04-effective-growth-SHA256SUMS`,
  `data/04-effective-growth-build_report.json`,
  `data/04-effective-growth-parameters.json`,
  `data/04-effective-growth-verification.json`

The prefixed scripts still name their delivered paths; rerun them on copies
in a scratch directory under the delivered names, never in the report.

## Dated notes

**2026-10-09, manuscript 04 duplicates manuscript 01.** 04 re-derives 01
without citing it (it was written against the same openai/math release). Its
20-bit witness (622 cells, cell degree 16, retained variance
`16 + 9/34816`, exceptional cell of 8704 points) is 01's, identical up to a
sign flip `x ↦ −x` and a relabelling of the leaves (reversed leaf order);
the intake checked the cell-for-cell correspondence. 01 and 02 had
already constructed this witness independently, on 7 October. 04's amplifier (one batch
size at every stage) is 01's fixed-count amplifier idea, with a different
transfer: a Stein/Wasserstein coupling with an absolute error over
hyperplane boundaries, instead of 01's Berry–Esseen transfer with relative
error. As a result 04's bound `α − 1/2 > 2^(−2^74)` is far weaker than
01's `2^(−7,784,628,387)`; nothing of 01 is superseded, and 04 answers none
of 01's twelve questions. Within ProveIt the witness is credited to 01 and
02, placed a day earlier.

What 04 adds, all small: the hyperplane transfer lemma; a balanced
all-budget statement `Λ_bal(d) ≥ c₀ d^α` with explicit `c₀`; the explicit
corollary that the dimension overhead `d^(1+γ)` can be made arbitrarily
small for every `γ > 0`; and a distinct-singleton search whose new row
`(r, m) = (4, 5)` (24 bits) has maximum gain `9/557056`. Its questions Q4
(sharper discontinuous-test transfer), Q5 (the optimal exponent
`ρ* ∈ (1/2, 1]`) and Q6 (joint dimension/correlation optimum) are new; Q1,
Q2, Q3 and Q7 restate 01's "Useful numerical exponents", "Global minimum
dimension", "A direct discrete amplifier" and "A compact formal
certificate".

These are the intake dossier's (dossier138_COMB) findings and the placement
message's; they are not re-proved in this note.
