# Weak and Difference Ascent Sequences

**Factorial growth, the logarithmic-square correction, weighted levels, sharp remainders and bounded-error inverses for OEIS A336070 and its difference-ascent family**

This is a research report built on 5 October 2026 (write batch 102) from
three manuscripts of one external research session, Reports 105, 107 and 108
of the session bundle of Reports 1–243, all dated 2 October 2026. They form
one chain on one spine: the count `a_n` of weak ascent sequences
(Bényi–Claesson–Dukes; OEIS [A336070](https://oeis.org/A336070),
`1, 1, 2, 6, 23, 106, 567, …`) and of difference ascent sequences with a
fixed parameter `d` (Dukes–Sagan; a `d`-ascent is an index with
`x_{i+1} > x_i − d`; `d = 0` gives the Fishburn numbers, `d = 1` A336070).
Throughout `μ = 6/π²` and `T = log n`.

- **Part I** (Report 105, the base): for every fixed `d ≥ 0`,
  `(a_n^{(d)}/n!)^{1/n} → μ`, `a_{n+1}^{(d)}/((n+1)a_n^{(d)}) → μ` and
  exponential concentration of the ascent count at `μn`; for `d = 1`,
  `log(a_n/(n!μⁿ)) = ½T² + O(T²/log T)` and a signed Lambert-W threshold
  inverse.
- **Part II** (Report 107): each level (equal adjacent pair) weighted by
  `w > 0`: `log H_n(w) = log n! + n log μ + (w/2)T² + O(T²/log T)`
  compact-uniformly in `w`, and a full large-deviation principle for the number
  of levels at speed `T²` with rate `x log(2x/w) − x + w/2`, the exact zero-level
  rate, and a weighted inverse.
- **Part III** (Report 108): both remainders reduced to `O(log n)`; the
  correction `(d/2)T²` with remainder `O_d(log n)` for every fixed integer
  `d ≥ 1`; threshold inverses with bounded additive error; sharper moment
  bounds for the level count.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Weak Ascent Sequences and Fixed Difference Ascent Growth: Factorial growth, concentration, and a sharp logarithmic square correction* (base); author line "Research report 105 / Prepared for Vladimir" | 105 | `A336070_Weak_Ascent_Logarithmic_Correction_Source.zip` (616,671 bytes, 16 files; `report105.tex`, 1,040 lines, 24 pp.) | none | `6ab1f1979` | Part I, Sections 1–12 |
| *Weighted Weak Ascent Levels and Their Probability Law: Logarithmic square growth and large deviations*; author line "Research report 107 / Prepared for Vladimir" | 107 | `A336070_Weighted_Levels_and_Large_Deviations_Source.zip` (523,954 bytes, 153 files; `report107.tex`, 870 lines, 18 pp.) | none (pins Report 105's TeX, PDF and archive by SHA-256; all three match the delivery) | `6ab1f1979` | Part II, Sections 13–22, plus the write's Section 23 |
| *Sharp Logarithmic Remainders and Bounded Error Inverses: Weighted weak ascents and fixed difference ascents*; author line "Research report 108 / Prepared for Vladimir" | 108 | `Ascent_Sequences_Sharp_Remainders_and_Bounded_Inverses_Source.zip` (680,726 bytes, 341 files; `report108.tex`, 1,058 lines, 24 pp.) | none (pins Report 107's TeX and PDF, both matching, and nine internal notes that were not delivered) | `6ab1f1979` | Part III, Sections 24–37 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `6ab1f1979` (batch 102, cluster A336070) removed them from
`docs/incoming/`. The write is batch 102's "Write batch 102
(a336070-weak-ascents): new report, weak and difference ascent sequences".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author or a tool, says it is
AI-assisted, or carries "prepared for private review" wording; each says
"Prepared for Vladimir". Report 108's `validation/proof_review.json` records
"passed" mathematical audits and its `quality_review.json` a visual review:
these are the delivering session's reviews of itself, not an assessment by a
referee or by this repository. Every result, proof, example, remark, question
and limitation of the three manuscripts is printed (Report 108's Sections 3–4
once, in Part II, because they are Report 107's Sections 3–4 word for word).

## Files

The directory holds 200 files: 5 at the root, 19 in `code/`, 176 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 105, prefix `105-growth-`**: 12 files besides the article (6 in
`code/`, 6 in `data/`); its `report105.tex` is the base of `article.tex`.
`code/`: the exact verifier and its finite models, the certificate builder,
the normal/optimized runner with its corruption tests, the optional mpmath
sanity script and the PDF build script. `data/`: the exact rational
certificate, the 501 self-generated terms `a_0..a_500` (not an OEIS b-file),
the recorded exact and floating results, provenance and validation records.

```
code/105-growth-build.sh
code/105-growth-build_certificate.py
code/105-growth-exact_models.py
code/105-growth-run_checks.py
code/105-growth-sanity_moving_bounds.py
code/105-growth-verify_exact.py
data/105-growth-PROVENANCE.json
data/105-growth-VALIDATION.json
data/105-growth-exact_certificate.json
data/105-growth-exact_check_results.json
data/105-growth-floating_sanity_results.json
data/105-growth-weak_ascent_terms.txt
```

**Report 107, prefix `107-levels-`**: 81 files (1 at the root, 5 in `code/`,
75 in `data/`). Root: the guide to its exact-rational check suite. `code/`:
the verifier, the fixture builder, the corruption runner, the build and replay
scripts. `data/`: fixtures, expected summary, corruption results, standalone and
payload replay records, provenance and validation, and the 68 non-empty run
records of its campaign.

```
107-levels-checks-README.md
code/107-levels-build.sh
code/107-levels-build_fixtures.py
code/107-levels-replay.sh
code/107-levels-run_checks.py
code/107-levels-verify_exact.py
data/107-levels-PROVENANCE.json
data/107-levels-REPLAY_RESULT.json
data/107-levels-VALIDATION.json
data/107-levels-corruption_results.json
data/107-levels-expected_summary.json
data/107-levels-fixtures.json
data/107-levels-standalone_replay.json
```

plus 68 run records, each name in both a `normal` and an `optimized` version:

```
data/107-levels-logs-baseline.{normal,optimized}.stdout
data/107-levels-logs-duplicate_key.{normal,optimized}.stderr
data/107-levels-logs-equation_q0_lambda_endpoint.{normal,optimized}.stderr
data/107-levels-logs-equation_signed_mixture_plus.{normal,optimized}.stderr
data/107-levels-logs-equation_tracker_sign.{normal,optimized}.stderr
data/107-levels-logs-equation_transition_level_shift.{normal,optimized}.stderr
data/107-levels-logs-equation_weighted_eigen_drop_w.{normal,optimized}.stderr
data/107-levels-logs-equation_weighted_poisson_sign.{normal,optimized}.stderr
data/107-levels-logs-equation_zero_transform_index.{normal,optimized}.stderr
data/107-levels-logs-final_baseline.{normal,optimized}.stdout
data/107-levels-logs-fishburn_value.{normal,optimized}.stderr
data/107-levels-logs-geometric_probability.{normal,optimized}.stderr
data/107-levels-logs-inverse_transform_sign.{normal,optimized}.stderr
data/107-levels-logs-missing_case.{normal,optimized}.stderr
data/107-levels-logs-noncanonical_rational.{normal,optimized}.stderr
data/107-levels-logs-noninteger_json_number.{normal,optimized}.stderr
data/107-levels-logs-normalized_b.{normal,optimized}.stderr
data/107-levels-logs-normalized_c.{normal,optimized}.stderr
data/107-levels-logs-normalized_h.{normal,optimized}.stderr
data/107-levels-logs-primitive_value.{normal,optimized}.stderr
data/107-levels-logs-q0_normalized_limit.{normal,optimized}.stderr
data/107-levels-logs-q0_weighted_data.{normal,optimized}.stderr
data/107-levels-logs-signed_delta.{normal,optimized}.stderr
data/107-levels-logs-standalone_replay.{normal,optimized}.stdout
data/107-levels-logs-transition_coefficient.{normal,optimized}.stderr
data/107-levels-logs-unweighted_eigenvector.{normal,optimized}.stderr
data/107-levels-logs-unweighted_lambda.{normal,optimized}.stderr
data/107-levels-logs-weighted_denominator.{normal,optimized}.stderr
data/107-levels-logs-weighted_first_moment.{normal,optimized}.stderr
data/107-levels-logs-weighted_increment_moment.{normal,optimized}.stderr
data/107-levels-logs-weighted_lambda.{normal,optimized}.stderr
data/107-levels-logs-weighted_negative_entry.{normal,optimized}.stderr
data/107-levels-logs-weighted_positive_entry.{normal,optimized}.stderr
data/107-levels-logs-weighted_tracker_drift.{normal,optimized}.stderr
```

**Report 108, prefix `108-sharp-`**: 104 files (1 at the root, 8 in `code/`,
95 in `data/`). Root: the guide to its exact check suite. `code/`: the
verifier, fixture builder, corruption runner, standalone replay, package
verifier, archive replay, sealing script and build script. `data/`: fixtures,
expected summary, corruption results, standalone replay record, five
validation records (build environment, build quality, input provenance, proof
review, visual review), and the 86 non-empty run records of its campaign.

```
108-sharp-checks-README.md
code/108-sharp-build.sh
code/108-sharp-build_fixtures.py
code/108-sharp-replay.py
code/108-sharp-replay_standalone.py
code/108-sharp-run_checks.py
code/108-sharp-seal.py
code/108-sharp-verify_exact.py
code/108-sharp-verify_package.py
data/108-sharp-corruption_results.json
data/108-sharp-expected_summary.json
data/108-sharp-fixtures.json
data/108-sharp-standalone_replay.json
data/108-sharp-validation-build_environment.json
data/108-sharp-validation-build_quality.txt
data/108-sharp-validation-input_provenance.json
data/108-sharp-validation-proof_review.json
data/108-sharp-validation-quality_review.json
```

plus 86 run records, each name in both a `normal` and an `optimized` version:

```
data/108-sharp-logs-baseline.{normal,optimized}.stdout
data/108-sharp-logs-bool_inventory.{normal,optimized}.stderr
data/108-sharp-logs-capped_bound.{normal,optimized}.stderr
data/108-sharp-logs-capped_row_sum.{normal,optimized}.stderr
data/108-sharp-logs-clipped_index.{normal,optimized}.stderr
data/108-sharp-logs-clipped_shift.{normal,optimized}.stderr
data/108-sharp-logs-crossing_bound.{normal,optimized}.stderr
data/108-sharp-logs-crossing_q_order.{normal,optimized}.stderr
data/108-sharp-logs-crossing_slope_drop.{normal,optimized}.stderr
data/108-sharp-logs-d0_endpoint_count.{normal,optimized}.stderr
data/108-sharp-logs-difference_count.{normal,optimized}.stderr
data/108-sharp-logs-duplicate_key.{normal,optimized}.stderr
data/108-sharp-logs-equation_cap_geometric_sign.{normal,optimized}.stderr
data/108-sharp-logs-equation_cap_row_power.{normal,optimized}.stderr
data/108-sharp-logs-equation_crossing_denominator.{normal,optimized}.stderr
data/108-sharp-logs-equation_crossing_time_sign.{normal,optimized}.stderr
data/108-sharp-logs-equation_d0_endpoint.{normal,optimized}.stderr
data/108-sharp-logs-equation_normalizer_sign.{normal,optimized}.stderr
data/108-sharp-logs-equation_poisson_sign.{normal,optimized}.stderr
data/108-sharp-logs-equation_prefix_inverse.{normal,optimized}.stderr
data/108-sharp-logs-equation_prefix_threshold.{normal,optimized}.stderr
data/108-sharp-logs-equation_q0_actual_zero.{normal,optimized}.stderr
data/108-sharp-logs-equation_q0_uniform.{normal,optimized}.stderr
data/108-sharp-logs-equation_recurrence_index.{normal,optimized}.stderr
data/108-sharp-logs-equation_shift_off_by_one.{normal,optimized}.stderr
data/108-sharp-logs-equation_stars_bars_index.{normal,optimized}.stderr
data/108-sharp-logs-equation_tracker_shift_sign.{normal,optimized}.stderr
data/108-sharp-logs-equation_weak_row_index.{normal,optimized}.stderr
data/108-sharp-logs-extra_top_key.{normal,optimized}.stderr
data/108-sharp-logs-final_baseline.{normal,optimized}.stdout
data/108-sharp-logs-float_inventory.{normal,optimized}.stderr
data/108-sharp-logs-missing_case.{normal,optimized}.stderr
data/108-sharp-logs-missing_nested_key.{normal,optimized}.stderr
data/108-sharp-logs-negative_shifted_probability.{normal,optimized}.stderr
data/108-sharp-logs-noncanonical_rational.{normal,optimized}.stderr
data/108-sharp-logs-positive_shifted_probability.{normal,optimized}.stderr
data/108-sharp-logs-prefix_inversion_histogram.{normal,optimized}.stderr
data/108-sharp-logs-prefix_legal_histogram.{normal,optimized}.stderr
data/108-sharp-logs-prefix_stars_bars.{normal,optimized}.stderr
data/108-sharp-logs-q0_shifted_probability.{normal,optimized}.stderr
data/108-sharp-logs-shifted_drift_value.{normal,optimized}.stderr
data/108-sharp-logs-shifted_normalizer.{normal,optimized}.stderr
data/108-sharp-logs-shifted_poisson_value.{normal,optimized}.stderr
```

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs; Report
105's and 107's `MANIFEST.sha256` and Report 108's `manifest.json` (checksum
manifests, verified at placement: 15/15, 152/152 and 340 entries; repository
policy drops checksum manifests); the delivery READMEs (105's was staged and is
replaced by this guide; 107's and 108's were not staged); `report107.tex` and
`report108.tex` (printed as Parts II and III); Report 108's `source/*.tex`
(eight files whose deterministic concatenation is `report108.tex`, checked
byte for byte) and `assemble.py` (which only performs that concatenation);
Report 108's `checks/weak_*` files (its re-shipped copy of Report 107's suite:
byte copies, or copies differing only in the default file names
`weak_fixtures.json`, `weak_expected_summary.json`, `weak_logs/`; Report 107's
staged suite stands for them); and the **154 empty** `.stdout`/`.stderr` run
records of Reports 107 and 108 (68 and 86 of them). Every outcome those records
would show is in the staged `corruption_results.json` files, and a campaign
rerun regenerates them.

## Labels and numbering

Label prefix **`wasc:`**: Part I uses `wasc:gr:` (Report 105's 121 labels),
Part II `wasc:lv:` (Report 107's 107 labels), Part III `wasc:sh:` (91 of Report
108's 124 labels). Report 108's other 33 labels sit in its Sections 3–4, which
repeat Report 107's word for word; they resolve to Part II's labels
(`eq:mixture` of Report 108 is `wasc:lv:eq:mixture`). The front matter uses
`wasc:` (`wasc:sec:guide`, `wasc:sec:status`, `wasc:sec:notation`,
`wasc:sec:provenance`, `wasc:sec:neighbours`), and the write added
`wasc:gr:part`, `wasc:lv:part`, `wasc:sh:part`, the three further-questions
sections `wasc:gr:sub:further`, `wasc:lv:sec:further`, `wasc:sh:sub:further`,
the two title-only sections `wasc:sh:sec:calibration` and
`wasc:sh:sec:corrector`, and the two remarks `wasc:lv:rem:zerosharp` and
`wasc:sh:rem:dzero`. 334 labels in all, all distinct.

Sections are numbered continuously, and statements and equations are
numbered within sections (`\numberwithin{equation}{section}`, as delivered),
so a manuscript's numbers shift with its sections only:

| Part | Manuscript | Section here | Statement / equation `k.j` |
|---|---|---|---|
| I | Report 105 | `k` (unchanged, 1–12) | `k.j` (unchanged) |
| II | Report 107 | `k + 12` (13–22); Section 23 added | `(k+12).j` |
| III | Report 108 | `k + 23` (24–37); 26 and 27 title only | `(k+23).j` |

For example Report 107's Theorem 1.1 is Theorem 13.1, Report 108's Theorem
1.1 is Theorem 24.1 and its Corollary 11.1 is Corollary 34.1. Report 108's
Table 1 is Table 1 here. The two remarks added in the write are Remark 20.1
(the last statement of Section 20) and Remark 33.1 (the last of Section 33),
so no delivered number moved. A check of the build's `.aux` against
separate builds of the three delivered `.tex` files confirmed every label's
number under these offsets. The delivered READMEs, audits and code use the
manuscripts' own numbers.

## Notation

No symbol was renamed. Each Part keeps its manuscript's letters; the front
matter's "Notation across the three Parts" lists every letter whose meaning
changes, with the tempting false readings, and each Part opens with a short
reading-conventions table. The most dangerous are **`H_n`** — in Part I
`H_n(v) = Σ v^{wasc(x)}` (the mark counts *weak ascents*), in Parts II and III
`H_n(w) = Σ w^{E(x)}` (the weight counts *levels*); both equal `a_n` only at
argument 1 — and **`B_n`**: in Part I the ratio diagnostic `n(r_n/μ − 1)`, in
Part III a count (`H_n(w)` or `a_n^{(d)}`). Others: `P` (pressure, Doob kernel,
primitive series, primitive counts `P_n`), `W` (Lambert function and, in Part
I, the circular increment that Parts II and III call `V`), `α` (Part I's
`3q/(2S)` against Parts II–III's `S'`), `L` (last letter or `log X`), `A`
(Part III's cutoff constant in `k = ⌈AT⌉`), `c` (corrector mean, or Part
III's coefficient `c ∈ {w, d}`), `D`, `R`, `F`, `h`, `U`, `k`. Integer `w = d`
does not turn levels into `d`-ascents: `H_3(2) = 12`, `a_3^{(2)} = 6`.

## What the report claims

**Part I (Report 105).**
- Theorem 1.1: for every fixed `d ≥ 0` and `v > 0`, the tilted upper bound
  `limsup n⁻¹ log(H_n^{(d)}(v)/n!) ≤ −log χ(v)`,
  `χ(v) = ∫_v^∞ log t/(t(t−1)) dt`, `χ(1) = π²/6`; the root and scaled ratio
  limits `μ`; exponential concentration of `K_n/n` at `μ`. External input: the
  Fishburn asymptotic (Hwang–Jin (1.1)) as the lower bound, via
  `F_n ≤ a_n^{(d)} ≤ n!`, and the `K + 2` children identity.
- Theorem 1.2 (`d = 1`): `log(a_n/(n!μⁿ)) = ½(log n)² + O((log n)²/log log n)`
  (a quadratic corrector with an exact Poisson identity for the upper bound,
  an exact path change of measure for the lower), and the inverse
  `N(X) = x − (log x)²/(2 log μx) + O(log x/log log x)`, `x = L/W(μL/e)`.
- Section 2: the exact state recurrence, the catalytic equation of
  Auli–Elizalde translated to the ascent refinement, the derivative recurrence
  and `a_n = g'_{n−1}(1)`, the formal Borel identity; Section 10: the inverse
  `o(L/(log L)²)` for every fixed `d`; Section 12: the level-marked kernel and
  the zero-level binomial transform (Jelínek's Fact 5.1, credited in the write).

**Part II (Report 107).**
- Theorem 13.1: the weighted asymptotic, compact-uniform in `w ∈ [w_−, w_+]`;
  at `w = 1` a second, self-contained proof of Theorem 1.2's counting part.
- Theorem 13.2: log-MGF limit `(w/2)(eᵗ − 1)` at speed `(log n)²`,
  concentration, `L^p` convergence of `E_n/(log n)²` to `w/2`, the mean with
  error `O(b_n/√log log n)`, and a full large-deviation principle with rate
  `x log(2x/w) − x + w/2` (proved by elementary tilting).
- Theorem 13.3: `H_n(0) = P_n` (primitive ascent sequences) and
  `log P(E_n = 0) = −(w/2)(log n)² + O((log n)²/log log n)`; the ratio
  `P_n/F_n → e^{−π²/6}` and its transform proof are prior work (Jelínek's Fact
  5.2, credited to Drmota), as Report 107 says.
- Theorem 13.4: the weighted inverse; exact monotonicity
  `H_{i+1} = E(K + 1 + w) H_i ≥ (1 + w) H_i`.

**Part III (Report 108).**
- Theorem 24.1: `log H_n(w) = log n! + n log μ + (w/2)(log n)² + O_𝒲(log n)`
  and `log a_n^{(d)} = log n! + n log μ + (d/2)(log n)² + O_d(log n)` for every
  fixed integer `d ≥ 1`. New ingredients: a capped slope `min(q/M, p)` for small
  states, a run-decomposition prefix count `N_{k,r} ≤ (e(r+2))^k` allowing the
  cutoff `k = ⌈A log n⌉`, the exact normalization `D_n = O(T)`, the shifted row
  `P_d(l, ·) = P(l', ·)` with `l' = max(l − d + 1, 0)`, and a boundary-deficit
  sum.
- Corollary 24.2: `N(Y) = x − (c/2)(log x)²/log(μx) + O(1) = x − (c/2) log x + O(1)`,
  `c = w` or `d`.
- Corollary 34.1: `E E_n = (w/2)T² + O(T^{3/2})`, absolute central moments
  `O(T^{3p/2})`, `Var E_n = O(T³)` (upper bounds).
- Table 1: exact `a_n^{(d)}`, `d = 0..3`, `n ≤ 10` (agreeing with Dukes–Sagan's
  Table 3; recomputed at placement).

**Added by the write** (all marked `[write]`, dated 5 October 2026): Remark
20.1 — with Part III, `log P(E_n = 0) = −(w/2)(log n)² + O(log n)`; Remark
33.1 — the statements of Theorem 24.1 and Corollary 24.2 also hold at `d = 0`
(coefficient 0), by the Fishburn asymptotic and the `K + 2` children
monotonicity `a_{i+1} ≥ 2a_i` for `i ≥ 1`, not by Part III's proof; the
observation that the fixed-`d`
subexponential factors differ by `((d − d')/2)(log n)² + O(log n)`; the residuals
`R_n = log(a_n/(n!μⁿ)) − ½(log n)²` = 3.356, 4.197, 4.725, 5.112, 5.419 at
`n = 100..500` from the shipped terms (evidence only); dated supersession notes;
the attribution of Part I's binomial transform; the front matter.

**Independent check of the write (5 October 2026).** An adversarial check made
by the intake after the write (`32122c09e`) reread the six deductions the write
supplied — Remark 20.1 (zero-level atom, error `O_𝒲(log n)`); Remark 33.1 (the
endpoint `d = 0`); the note after "Why fixed means fixed" in Section 9
(fixed-`d` factors differ by `((d − d')/2)(log n)² + O_{d,d'}(log n)`); the
exclusion of a next term of exact order `log n log log n` (Section 12 note and
item 2 of Section 12.3); the error `O(1/log n)` in (19.2) (note after Theorem
13.2); and the closing of Part III's item 9 (real `d` acts as `⌈d⌉`) — and
found all six valid, with no counterexample and no gap in any proof chain;
`d = 0` is genuinely the Fishburn family, with coefficient 0. Remark 33.1 had
one defect of wording: its proof stated `a_{i+1}^{(0)} ≥ 2a_i^{(0)}` without a
range, and it fails at `i = 0` (`a_0 = a_1 = 1`); it now says "for `i ≥ 1`",
which is all the first crossing needs, with a dated note keeping the first
wording. Two precisions are adopted: the MGF error of the note after Theorem
13.2 now carries its subscript, `O_{𝒲,J}(1/log n)`; and item 9 of Section 37.1
now says that `⌈d⌉` depends on the strict inequality `x_{i+1} > x_i − d` (under
`x_{i+1} ≥ x_i − d` the effective parameter would be `⌊d⌋ + 1`: `d = 1` would
give 24 instead of 23 at `n = 4`), so that for real `d > 0` the coefficient of
`(log n)²` is `⌈d⌉/2`, not `d/2`. The check used neither the delivered
programs nor the write's: its own exact big-integer state recursion over
`(K, l)` computed `a_n^{(d)}` (`d = 0..3`) and `H_n(w)` (`w = 0, ½, 2`) to
`n = 400`, agreeing with brute-force enumeration for `n ≤ 9` (also at real
`d = ½, 3/2, 2.7`); its `d = 0` column is A022493, its `d = 1` column equals
every shipped term of `data/105-growth-weak_ascent_terms.txt` to `n = 400`
(A336070), its `H_n(0)` column is A138265 (primitive ascent sequences), and it
reproduces Table 1 entry for entry. Residual analyses at `n = 25..400`:
`n(log F_n − log n! − n log μ − ½ log n − log C_F) → −0.565` (confirming `C_F`
and `O(1/n)`), `n(P_n/F_n − e^{−π²/6}) ≈ 0.477`; for Remark 20.1, `[log P(E_n =
0) + (w/2)(log n)²]/log n` = −0.510, −0.461, 0.189 at `n = 400` for `w = ½, 1,
2`; at `d = 0`, `N(Y) − x` in `[−2.26, −0.44]` for `5 ≤ m ≤ 400`; the pairwise
quotients `[log(a^{(d)}/a^{(d')}) − ((d − d')/2)(log n)²]/log n` bounded (0.187,
−0.875, −2.205, −1.330 at `n = 400`); the MGF error times `log n` bounded
(−0.049, −0.650, −0.699). Caveat: the local slope of the `d = 1` residual
against `log n` (1.07, 1.25, 1.36 at `n = 100, 200, 400`) is still rising; it
neither supports nor refutes Part III's question 1, and the residuals stay
evidence only. This was a careful reading with numerical tests, not a formal
verification or an external review; the article records it in full at the end
of "Provenance and merge decisions".

## What the report does not claim

Every limitation is printed in place. In short: **no relative-error
equivalent, amplitude, power of `n` or transseries** in any Part — Part III's
`O(log n)` is a polynomial-factor uncertainty; no coefficient of a possible
`log n` term; the full tilted pressure for the ascent count at `v ≠ 1` is only
bounded above (Part I), and no large-deviation principle, variance or central
limit theorem for the ascent count is proved; for levels, no total-variation
Poisson approximation, mod-Poisson convergence, central or local limit theorem,
variance order, positive-level atom asymptotic or sharp tail prefactor (Part
II), and Part III's variance bound is not an order; no uniformity in
`d = d(n)` or as `w → 0` or `∞`; `d = 0` is outside Part III's proof (Remark
33.1 covers it from the literature); no limiting constant, computable bracket or
exact integer recovery for the bounded inverse; no OEIS identifiers for the
unrestricted `d = 2, 3` columns; the Borel radius `π²/6` is established but not
its singular type or continuation. **All three packages**: finite exact checks
prove no asymptotic statement; the floating diagnostics are uncertified; the
literature checks are bounded, not priority certificates; the ratio `P_n/F_n`
and the binomial transform are prior work.

## Further questions, and the standing rule

Each Part closes with "Further questions and research" (Sections 12.3, 23 and
37.1). Under Vladimir's standing rule of 4 October 2026 the write moved there
every claim stated without proof, with source, sketch and what is missing, and
re-scoped those that a later Part answers:

- Part I: (1) a relative-error equivalent and amplitude; (2) the next scale —
  re-scoped: `log n log log n` is excluded by Part III, `c' log n + O(1)` open;
  (3) the full tilted pressure at `v ≠ 1`; (4) LDP, variance and CLT for the
  ascent count (Part II's LDP is for levels); (5) dependence on `d` — answered
  for fixed `d ≥ 1` by Part III, crossover in `d(n)` open; (6) the singular type
  of the Borel transform and continuation of its formal identity; (7) the
  perturbative route from the zero-level anchor to `ℓ = 1`; (8) `B_n ~ log n`;
  (9) effective inverse constants.
- Part II (Section 23, added in the write): Poisson approximation; CLT,
  local limit and variance order (Part III's bound `O(T³)` re-scopes it);
  positive-level atoms and tail prefactors; an amplitude for `H_n(w)`;
  uniformity as `w → 0, ∞`; an equivalent for the zero atom; certified inverse
  constants.
- Part III: its own questions 1–5 stay as printed; added (6) Dukes–Sagan
  Problem 8.7 (the unrestricted generating function for general `d`), (7) OEIS
  identification of the `d = 2, 3` columns, (8) an explanation of the common
  coefficient form `w/2`, `d/2`; (9) its remark that real `d` acts as `⌈d⌉` was
  checked and closes (it depends on the strict inequality `x_{i+1} > x_i − d`;
  the non-strict one would give `⌊d⌋ + 1`), so for real `d > 0` the
  coefficient of `(log n)²` is `⌈d⌉/2`.

Superseded statements stay as printed with dated notes pointing forward: Part
I's and Part II's remainders `O((log n)²/log log n)` (Theorem 24.1); their
inverses `O(log x/log log x)` and the non-claims "not a bounded-error inverse"
(Corollary 24.2); Part I's fixed-`d` inverse `o(L/(log L)²)`; Part I's
"subexponential factors for different fixed `d` need not agree" (they differ,
for `d ≥ 1`); Part II's mean error and `Var = o((log n)⁴)` (Corollary 34.1);
Part II's zero-atom error (Remark 20.1). **Nothing in any of the three
manuscripts was found to be wrong.** One attribution defect is corrected in a
dated note: Report 105 prints the binomial transform between Fishburn and
primitive counts, `A_F(z) = P(z/(1−z))`, without credit; it is Jelínek's Fact
5.1, and primitive ascent sequences go back to Dukes–Kitaev–Remmel–Steingrímsson
(J. Combin. 2 (2011), added to the bibliography). The citation of **Mansour,
*Mathematics* 14(8) (2026), 1378**, made by all three manuscripts, was **not
verified** at placement or at the write; the article says so in Part I, in Part
III and in the bibliography.

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`:

- `a202058-ascent-000-growth` (ordinary ascent sequences with no value three
  times, A202058): same toolkit (frozen geometric kernel, calibration curve,
  Lambert inverse). Its Conjecture `a58:fn:conj:twothirds`,
  `log(a_n/(n!μⁿ)) ~ (2/3)(log n)²` pointwise, is proved there only in limsup and
  cumulative form. This report proves the analogous pointwise law with
  coefficient ½ (and `d/2`) for the unrestricted weak and difference families,
  with an `O(log n)` remainder, by a path change of measure; it says nothing
  about the coefficient 2/3 of that different family.
- `a294220-ascent-multiplicity-caps` (every value at most `b` times): its growth
  constants `μ_b` increase to `6/π²` as `b → ∞`, and it asks about the
  transition to unrestricted ordinary ascent sequences — the Fishburn case
  `d = 0` of Part I. The unrestricted families here have `μ = 6/π²` for every
  fixed `d`, with a correction `(d/2)(log n)²` for `d ≥ 1` that is absent at
  `d = 0`. Not an answer to its question.
- Both are siblings, not hosts. No other report treats A336070, weak ascents or
  difference ascents (searched 5 October 2026). Pointers from those two reports
  back to this one are a separate reciprocal-notes commit; this write edits no
  other report.
- *See also* (dated 6 October 2026, batch-106 reciprocal note):
  [`a005975-interval-graphs`](../a005975-interval-graphs/) (bundle Report 133,
  unlabeled interval graphs A005975/A005976, labels `ivg:`) uses the same
  external input, Hwang–Jin (1.1) for the Fishburn numbers A022493, together
  with two further Hwang–Jin statements (the diagonal size, Theorem 25(ii) of
  the 54-page author PDF, and the self-dual count, Corollary 29). It proves
  `C_n = F_n/2 − F_{n−1} − F_{n−2} log n + O(F_{n−2})` and
  `I_n = F_n/2 − F_{n−1}/2 − F_{n−2} log n + O(F_{n−2})`. No shared theorem;
  a sibling, not a host.

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean file in the repository mentions Fishburn
numbers, ascent sequences or A336070 (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (all 197 staged delivered files checked
  against fresh extractions at the write: 0 differences); only names changed
  (tables at the end). The delivered code and markdown use delivery paths
  (`code/…`, `data/…`, `checks/…`, `validation/…`, `report10N.tex`,
  `README.md`), which are shipped under other names or not at all. The scripts
  resolve paths relative to their own location or the package root, so **none
  runs in this directory**.
- **In-place writes.** Report 107's `build_fixtures.py` rewrites
  `fixtures.json` beside itself, and its `run_checks.py` rewrites
  `corruption_results.json` and the `logs/` records; Report 108's
  `build_fixtures.py`, `run_checks.py` (also `weak_campaign.stdout`/`.stderr`,
  which are not delivered) and `replay_standalone.py` do the same with its
  files, and `seal.py` rewrites `manifest.json` and writes `FINAL_SHA256.txt`.
  Run all of them only on a copy.
- **CRLF on Windows.** Run there, the campaigns write their records with CRLF
  line ends: at placement 67 of Report 107's regenerated files and 154 of Report
  108's differed from the delivery only by CRLF, and a CRLF `fixtures.json`
  from `build_fixtures.py` makes the next `run_checks.py` fail its fixture hash.
  This is a platform artifact, not a defect.
- **Unshipped files named in delivered text.** `108-sharp-checks-README.md`
  describes the `weak_*` files, `weak_corruption_results.json`, `logs/` and
  `weak_logs/` (the `logs/` records are shipped as `data/108-sharp-logs-*`, the
  others are not shipped; Report 107's suite stands for them);
  `code/108-sharp-replay.py` defaults to `report108_source_checks.zip`, and Report
  108's README and `seal.py` name `FINAL_SHA256.txt` and `manifest.json`, none
  of which is shipped (the archive under its arrival name is retrievable, see
  below); `data/108-sharp-validation-input_provenance.json` pins nine internal
  notes (`fixed_d_*.md`, `weighted_*.md`) that were never delivered.
  `107-levels-checks-README.md` names `report107.tex` and `report107.pdf`
  (printed as Part II; the PDF is not shipped).
- **Empty run records.** The 154 empty records are not shipped (see "Not
  shipped"); the shipped `logs` records are therefore a subset of what a
  campaign writes.
- Report 108's README shows an output path under `/tmp/`; use a scratch
  directory outside the repository.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. The simplest
route recreates the delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/A336070_Weak_Ascent_Logarithmic_Correction_Source.zip > s105.zip
git show 60f54ea06:docs/incoming/A336070_Weighted_Levels_and_Large_Deviations_Source.zip > s107.zip
git show 60f54ea06:docs/incoming/Ascent_Sequences_Sharp_Remainders_and_Bounded_Inverses_Source.zip > s108.zip
mkdir r105 r107 r108 && unzip -q s105.zip -d r105 && unzip -q s107.zip -d r107 && unzip -q s108.zip -d r108
cd r105/report105_source
py code/verify_exact.py
py code/run_checks.py --output ../exact-replay.json        # normal, -O and corruption tests
uv run --no-project --with mpmath==1.3.0 python code/sanity_moving_bounds.py --output ../floating-replay.json
cd ../../r107/report107
py checks/verify_exact.py                                  # also with py -O
py checks/run_checks.py                                    # rewrites its own records (copy only)
cd ../../r108/report108
py verify_package.py
py checks/verify_exact.py                                  # also with py -O
py checks/run_checks.py                                    # also reruns Report 107's campaign
```

Python 3.10 or later and its standard library suffice for the exact suites;
the optional floating script needs mpmath.

Results: at placement (5 October 2026, on copies, recorded in the batch-102
dossier) every suite passed — Report 105 `run_checks.py` (normal and `-O`, 14
corruptions rejected; output equal to `data/105-growth-exact_check_results.json`
except two elapsed-time fields), `sanity_moving_bounds.py` (output identical to
`data/105-growth-floating_sanity_results.json`); Report 107 `verify_exact.py`
(normal and `-O`) and `run_checks.py` (31 mutations, 62 rejected runs, 4
baselines; 86 files identical, 67 differing only by CRLF); Report 108
`verify_package.py` (340 payload files), `run_checks.py` and its weak campaign
(41 new and 31 preserved mutations, 144 rejected runs; 187 files identical, 154
CRLF-only). At the write (5 October 2026, Python 3.14.4, Windows, fresh
extractions of the three archives) the exact verifiers were rerun: Report 105
`code/verify_exact.py` passed in about a minute, Report 107
`checks/verify_exact.py` in about 9 s, Report 108 `checks/verify_exact.py` and
`verify_package.py` (340 payload files) in about 40 s together. The campaigns,
which take 2–11 minutes and rewrite their records, were not repeated.

## Rights

Repository contents are MIT-0. The sequence terms printed in the article and
contained in the data and code (`a_n` of A336070, the Fishburn numbers
A022493, the difference-ascent counts) are recomputed by the shipped programs;
Report 105 compares its first 25 terms with the displayed OEIS terms of A336070,
and its 501-term file is self-generated, not an OEIS b-file. OEIS data are
available under CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). The
OEIS entries are credited for the sequences; Bényi–Claesson–Dukes for weak
ascent sequences, Dukes–Sagan for difference ascents, Auli–Elizalde for the
catalytic equation, Hwang–Jin for the Fishburn asymptotic, Jelínek (and Drmota)
for the primitive Fishburn transform and ratio. Nothing was submitted to the
OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The build
after the independent check (5 October 2026): 73 pages (the write's: 72), no
errors, no undefined or multiply defined references or citations, no overfull
or underfull boxes; every one of the 334 labels keeps the number it had in the
write's build (`.aux` compared). The log carries one "Infinite glue shrinkage
found in box being split" message, from the notation longtable breaking across
a page, as in other reports with longtables, and one pdfTeX warning
"destination with the same identifier (name{table.1}) has been already used,
duplicate ignored", from the uncaptioned notation longtable and Table 1; both
were already in the write's build, whose record here overlooked the second. A build of the staged base (`report105.tex` as placed) is
warning-free with 24 pages; its 121 labels keep their numbers here.

## Delivered path → shipped path

Report 105 (`105-growth-`; `README.md` replaced by this guide):

| Delivered | Shipped |
|---|---|
| `report105.tex` | `article.tex` (Part I) |
| `build.sh` | `code/105-growth-build.sh` |
| `code/<name>.py` (build_certificate, exact_models, run_checks, sanity_moving_bounds, verify_exact) | `code/105-growth-<name>.py` |
| `code/exact_check_results.json`, `code/floating_sanity_results.json` | `data/105-growth-<name>.json` |
| `data/exact_certificate.json`, `data/weak_ascent_terms.txt` | `data/105-growth-<name>` |
| `PROVENANCE.json`, `VALIDATION.json` | `data/105-growth-<name>.json` |
| `report105.pdf`, `MANIFEST.sha256` | not shipped |

Report 107 (`107-levels-`):

| Delivered | Shipped |
|---|---|
| `report107.tex` | not shipped; printed as Part II of `article.tex` |
| `checks/README.md` | `107-levels-checks-README.md` |
| `build.sh`, `replay.sh` | `code/107-levels-<name>` |
| `checks/<name>.py` (build_fixtures, run_checks, verify_exact) | `code/107-levels-<name>.py` |
| `checks/<name>.json` (corruption_results, expected_summary, fixtures, standalone_replay) | `data/107-levels-<name>.json` |
| `checks/logs/<name>` (68 non-empty of 136) | `data/107-levels-logs-<name>` |
| `PROVENANCE.json`, `VALIDATION.json`, `REPLAY_RESULT.json` | `data/107-levels-<name>.json` |
| `README.md`, `report107.pdf`, `MANIFEST.sha256`, 68 empty `checks/logs/*` | not shipped |

Report 108 (`108-sharp-`):

| Delivered | Shipped |
|---|---|
| `report108.tex` | not shipped; printed as Part III of `article.tex` (Sections 3–4 in Part II) |
| `checks/README.md` | `108-sharp-checks-README.md` |
| `build.sh`, `replay.py`, `seal.py`, `verify_package.py` | `code/108-sharp-<name>` |
| `checks/<name>.py` (build_fixtures, replay_standalone, run_checks, verify_exact) | `code/108-sharp-<name>.py` |
| `checks/<name>.json` (corruption_results, expected_summary, fixtures, standalone_replay) | `data/108-sharp-<name>.json` |
| `checks/logs/<name>` (86 non-empty of 172) | `data/108-sharp-logs-<name>` |
| `validation/<name>` (five files) | `data/108-sharp-validation-<name>` |
| `README.md`, `report108.pdf`, `manifest.json`, `assemble.py`, `source/*.tex` (8), `checks/weak_*` (6 files, `weak_logs/` with 132 records), 86 empty `checks/logs/*` | not shipped |

## Provenance

Three manuscripts (bundle Reports 105, 107, 108) → one report; base 105. Arrival
`60f54ea06`, placement `6ab1f1979`, write batch 102 (5 October 2026). No
manuscript pins a ProveIt commit. Merge choices (base and chain order, Report
108's Sections 3–4 printed once, its Section 31 printed in full with a note on
its differences from Section 18, the merged bibliography with one added entry,
the attribution note) are listed in the article's front matter, "Provenance and
merge decisions".
