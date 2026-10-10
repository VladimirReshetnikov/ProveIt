# Gaussian parity reductions: overview of the sources

Reconciliation note, 2026-10-09. `README.md` here is the base delivery's own
README, kept as delivered; this file says how the merged report's sources
fit together. Delivered files are not edited. All four sources are unrefereed
research continuations (16 says AI-assisted; none claims peer review), and
nothing is formalized. Placement `<placement commit>`; the status of every claim and
correction of the PolyLog programme is kept in the project README,
[Status of claims, and known defects](../../../README.md#status-of-claims-and-known-defects).

All four continue the unified manuscript under `../../manuscript/` (pinned at
`afed07429d` (14, 17) or `0599fe867a` (15, 16); the manuscript is unchanged from
both pins to the placement). They cite its labels (`gauss:eq:*`, `mixed:*`,
`bloch:eq:sgP3`, `integral:neg:cubic`, `stieltjes:prop:jetrank`, `tower:thm:rank`).
That manuscript is maintained separately; nothing here edits it.

## Files by source

**14 `polylogarithms_exact_reductions_20261009`: the base** (unprefixed manuscript)

- `article.tex` (delivered `article/polylogarithms_exact_reductions.tex`):
  *From Polylogarithm Conjectures to Exact Reductions*; `references.tex`;
  `sections/01_scope.tex` … `sections/07_research.tex`
- `README.md` (delivered)
- `code/14-exact-reductions-*` (the `run_checks.py` driver, `shuffle_certificates.py`,
  `verify_s4_candidate.py`, `make_moment_figure.py`, the `Makefile`, and the
  components `depth-`, `ladders-`, `moments-` with their READMEs)
- `data/14-exact-reductions-*` (shuffle normal forms, validation reports, the
  integration register as CSV and JSON, the source manifest, the 112-digit cubic
  certificate, the Gaussian table through weight 12, figure data and caption)
- `figures/14-exact-reductions-moment_asymptotics.{pdf,png}`
- `14-exact-reductions-analytic_cross_review.md`,
  `14-exact-reductions-loggamma_sources.md`

**Members**, prefixed; their manuscripts and READMEs are not staged (retrievable
from their arrival commits):

- **15** `polylogarithm_research_20261009` (`cbe9e9b599`), *Parity Reductions and
  Rational Distribution Ranks*: `15-parity-ranks-integration_notes.md`,
  `code/15-parity-ranks-*`, `data/15-parity-ranks-*`.
- **16** `ProveIt_Gaussian_Polylogarithms_Research` (`eaad5886ed`), *Gaussian
  reductions and certified polylogarithm evaluation*:
  `16-gaussian-certified-INTEGRATION.md`,
  `16-gaussian-certified-editorial-ledger-addendum.md`, `code/16-gaussian-certified-*`
  (with the delivered `.gitignore`, inert under its prefixed name),
  `data/16-gaussian-certified-*` (the exact weight-8 and weight-10 tables are
  `weight8.tex`, `weight10.tex`).
- **17** `proveit_polylog_gap_reductions_2026-10-09` (`eaad5886ed`), *Mixed-Point
  Elimination and Certified Parity Reductions*: `17-gap-reductions-INTEGRATION.md`,
  `17-gap-reductions-manuscript_supplement.tex` (a proposed manuscript fragment,
  `gapcont:` labels), `code/17-gap-reductions-*`, `data/17-gap-reductions-*`
  (`MANIFEST.sha256` staged as delivered; the compiled `parity_tables.pdf` is not
  staged, its source `parity_tables_document.tex` and `parity_tables.tex` are).

## What was delivered more than once

| Result | 14 | 15 | 16 | 17 | Note |
|---|---|---|---|---|---|
| depth-two parity formula on the unit circle, every weight (a specialization of Panzer 2017) | ✓ `thm:binomial-parity` | ✓ `thm:gaussian` | ✓ `thm:parity` | ✓ `thm:parity` (solver, determinant `2^⌊w/2⌋`) | four derivations; all credit Panzer |
| the five weight-six Gaussian doubles `gauss:eq:g51` … `g15` | ✓ | ✓ | ✓ | ✓ | coefficients unchanged |
| the weight-five relation `gauss:eq:wt5-sporadic` = 960·(1,4)-shuffle − 224·(2,3)-shuffle | ✓ | ✓ | ✓ | ✓ | |
| both shuffle rows: the four weight-five `g` span at most two directions mod `π⁵, Gζ(3), β(4)log2` | ✓ | ✓ | (uses both rows only in the `π`-free combination, for every odd weight: `thm:oddfamily`) | ✓ | |
| infinite height-one family `g_{2m−1,1}` | | ✓ `cor:edge` | ✓ `cor:heightone` | ✓ (all angles, `thm:allangle`) | |
| Gaussian tables at higher weight | through 12 (JSON, TeX) | through 12 (66 formulas) | 8 and 10 (16 rows) | 2–8, Gaussian and Eisenstein (56) | |
| `Li₁,₁(z,1/z) = −Li₂(z/(z−1))` (`mixed:eq:gauss-w2`, `mixed:eq:eis-w2`) | | ✓ `prop:Li11` | | ✓ (`D₁₁ = F₁₁ + Li₂`, Landen) | the `a = b = 1` case of the batch-138 formula (X1) |
| the four mixed constants `Re Li₄,₁`, `Im Li₅,₁` at `(i,−i)`, `(ρ²,ρ)` | ✓ (labelled inherited) | ✓ `thm:four` | | ✓ | **repeat** of 10 (batch 138, X1), see below |
| all-weight reduction of `Li_{a,b}(z,1/z)` to `Li_{r,s}(z,1)` | (inherited) | ✓ `thm:mixed` (a parity form) | | ✓ `thm:gap`, plus `T² = I` | `thm:gap` is 10's formula term for term |
| `S₄` reduction (`gauss:eq:S4-closed`) | open; equivalent short form | open; `S_p = Im Li_{p,1}(i,1) + Im Li_{p,1}(i,−1)` | open; residual enclosure | – | **open in all** |

Single-source parts: 14's formal shuffle count at every weight and depth
(`thm:witt`, generalizing the weight-six rank seven of `corpus-corrections` C11),
the three weight-four Gaussian triples and the index family `(2,1,…,1)`
(`thm:one-two`), the supergolden and `x⁴+x−1` trilogarithm ladders with the
complementary-power theorem, and the log-gamma moment analysis (late-coefficient
asymptotic, divergence, effective remainder, 112-digit cubic certificate);
16's Chebyshev-moment evaluator (geometric error uniform through `xy = 1`, sharp
kernel rate, 89 interval certificates) and its infinite odd-weight shuffle family;
17's integral involution, all-angle last-index-one identities and positive-measure
midpoint evaluator (six rational rectangles below `10⁻⁷⁰`); 15's weighted
distribution presentation (below).

**Base: 14.** The parity formulas are equally general (every weight, every
point of the unit circle but 1, boundary cases included); 14 proves the most of
the manuscript's numerical candidates (eleven: the six above, three triples, two
ladders), alone gives the all-depth formal count, and alone credits the batch-138
results it re-derives. Credit all four for the shared results.

## Repeats of results already placed

- The four mixed constants and the all-weight reduction of `Li_{a,b}(z,1/z)` were
  proved by 10 (batch 138; `../corpus-corrections/10-exact-structure-CORRECTIONS.txt`
  item 1; `thm:mixed` in `../rational-grid-distribution-ranks/article.tex`,
  section `sec:mixed`). 14 says so; 15 and 17 do not cite it. 17's `thm:gap` with
  its correction `C_{a,b}` (`eq:Cdef`) is 10's formula term for term. Intake checked
  that the printed constants agree (identical up to `ζ(2) = π²/6`, `ζ(4) = π⁴/90`)
  and recomputed all four.
- 15's rank theorems (`thm:jet-rank`, `cor:stieltjes-rank`, `cor:parameter-rank`)
  are a fourth proof of the ranks of `../rational-grid-distribution-ranks/`. Its
  primitive-residue `Q`-basis for nonzero integer exponents is the rational form
  of that report's top-denominator basis (`thm:dist-normal-form` and the paragraph
  after `eq:dist-top-coordinate`), with explicit rational elimination certificates.

## Caveats

- Every source says it proves no independence, transcendence or minimal depth;
  formal quotient dimensions are not numerical dimensions; numerical residuals
  (including 16's enclosure of the `S₄` residual) are not proofs.
- `S₄` stays open; see also question 1 of `../alternating-harmonic-polylogarithms/`.
- 14 attributes the cubic log-gamma moment to Bailey–Borwein–Borwein (Ramanujan J.
  36 (2015), Thm 6) and the fixed-order moment expansion to Amdeberhan et al.
  (Proc. AMS 139 (2011), Thm 8.1); these literature statements were not checked
  at intake.
- The prefixed scripts still name their delivered paths and write their outputs
  in place; `article.tex` expects `figures/moment_asymptotics.pdf` under its
  delivered name. Rerun on copies in a scratch directory under the delivered names.
