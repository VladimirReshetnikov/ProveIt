# Exponential Towers (OEIS A096537 and A096542)

**Airy limits and the corrected asymptotic of A096537; fractional
corrections and Gamma laws for the shifted family**

A merged research report in two Parts, a theorem and its sequel, built from
two manuscripts of one external research session (the session bundle of
Reports 1–243, arrival commit `60f54ea06`), placed by `8622ca7e5` (batch 110,
cluster 110-TOWER) and written on 7 October 2026. Neither manuscript names an
author, a tool or an addressee; both PDF author fields read "Research report";
neither pins a repository commit.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Airy Limits and the Corrected Asymptotic of A096537: Critical exponential towers and depth weighted labeled trees* (title block "Report192", 4 October 2026); the base | 192 | `A096537_Corrected_Asymptotic_and_Airy_Limits_Source.zip` (662,864 bytes, 23 files; `Report192.tex`, 1,502 lines, 24 pp.) | none | `8622ca7e5` | Part I, Sections 1–14, plus the write's Remarks 1.4 and 13.1 |
| *Fractional Corrections and Gamma Laws for Exponential Towers: A sequel to the leading Airy asymptotic* (title block "Report193", 4 October 2026) | 193 | `A096537_Fractional_Corrections_and_Gamma_Laws_Source.zip` (1,008,394 bytes, 37 files; `Report193.tex`, 1,965 lines, 29 pp.) | none | `8622ca7e5` | Part II, Sections 15–28, plus the write's Section 29 |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. Part II's sign certificate for `c_1` is
a directed-interval computation under a stated arithmetic trust boundary
(Python's correctly rounded `decimal`), resting on an analytic reduction and
tail bound proved in the text; it is not machine-checked.

## What the report proves

`F_1(x) = exp(x exp(2x exp(3x ⋯))) = Σ a_n x^n/n!` is OEIS A096537 (Paul D.
Hanna); `F_y = exp(x y F_{y+1})` is the shifted family whose coefficients
`P_n(y) = n![x^n]F_y` are the rows of A096542; `ρ = 1 − 1/e`, `α = e − 1`;
`b_n = a_n/(n!)^2`.

**Part I (Report 192).**

- **Theorem 1.1:** `b_n ~ √(2/(πρ)) ρ^(−n) n^(−1/2)`, i.e.
  `a_n ~ 2√(2π/ρ) n^(2n+1/2) e^(−n) (e − 1)^(−n)`.
- Theorem 5.1: the critical finite-height tower
  `H_h(1/(eh)) ~ K h^(1/6) e^(−αh)`, `K = 2^(1/6)√e/(√π Ai(0)²)`, from a
  normalized Riccati entrance (Lemma 3.1) and bulk matching (Lemmas 4.1, 4.3);
  Theorem 6.1: a uniform real Airy window.
- Theorem 1.2: the Airy size law (characteristic function
  `Ai(0)²/Ai(−β i t)²`, `p(0) = Ai(0)²/β`) with a uniform lattice local limit
  (Theorem 8.1 on minor arcs, Section 9), and a Gaussian height law for
  depth-weighted labelled trees (Section 11).
- Theorem 1.3: a refined Lambert inverse and a shrinking integer sandwich.
- Section 2: exact-height coefficients, the depth-weighted tree identity,
  `a_n ≥ n² a_{n−1}` (Lemma 2.1).

**Part II (Report 193).**

- **Theorem 15.1:** `b_n ρ^n √n = C + c_1 n^(−1/3) + o(n^(−1/3))`,
  `C = √(2/(πρ))`, `−0.61 < c_1 < −0.25`, with `c_1` an absolutely convergent
  Airy perturbation integral, reduced to a real integral (Theorem 23.1) and
  signed by a proved tail bound and directed interval quadrature on 562 panels
  (Section 24). So `b_n ρ^n √n < C` eventually (no effective onset).
- **Theorem 15.2:** `b_n(y) ~ C ρ^(1−y) ρ^(−n) n^(y−3/2)/Γ(y)` with the same
  relative correction, uniformly on compact `Y ⊂ (0, ∞)`; a normal limit for
  root-ancestor choices; Theorem 25.1, a local Gamma correction.
- Section 26: the positive real Borel boundary; Section 27: threshold inverses
  at the fractional scale.
- Part II answers two of Part I's open questions: the first coefficient of
  "Rates and further coefficients" and "Fixed positive shifts" (for every fixed
  `y > 0`). At `y = 1` its Theorem 15.2 is Part I's Theorem 1.1 with the
  correction added.

## Refuted OEIS formulas (standing rule)

- **A096537** (revision #8, 17 December 2019; live on 7 October 2026):
  "Conjecture: a(n) ~ 2 * Pi * n^(2*n + 1/2) / (exp(n) * (exp(1) - 1)^n). -
  Vaclav Kotesovec, Dec 16 2019" is **false**. Remark 1.4: by Theorem 1.1 the
  limit of `a_n e^n (e−1)^n / n^(2n+1/2)` is `2√(2π/ρ) = 2π √(2/(πρ))`, and
  `πρ < 2` (from `e < 11/4`, `π < 22/7`), so the amplitude `2π` is too small by
  the factor `√(2/(πρ)) = 1.00355251532641107954…`. Report 192 prints this
  factor as `…07955…`, a rounding; Remark 1.4 gives the truncation.
- **A096542** (revision #11, 19 December 2017; live on 7 October 2026): the
  line "T(n, 1) = n*A096537(n)" is **false** for every `n ≥ 2`; the correct
  identity is `T(n, 1) = n·A096537(n−1)`. Remark 13.1: `[y]F_y = x F_1`; the
  entry's own row 2, `0, 2, 3`, gives `T(2,1) = 2 = 2·a_1`, not `2·a_2 = 10`.
  Both manuscripts noted this index mismatch.

Nothing was submitted to the OEIS. No claim of either manuscript was found to
be false.

## What the report does not claim

- No effective rate, onset or error constant for any asymptotic statement; no
  all-orders expansion; the bracket for `c_1` is a rigorous enclosure under
  the stated trust boundary, and `−0.43652529` is only a diagnostic.
- No uniformity as `y ↓ 0` or `y → ∞`; no local limit for the root-ancestor
  statistic; no complex Borel-sector or Δ-domain expansion; no single-ceiling
  inverse at the jumps.
- Credited, not claimed: the sequence and the shifted family (Hanna); the
  continued-exponential tree framework (Bender–Vinson; Poland), whose full
  texts neither manuscript could compare page by page; Airy facts (DLMF 9.2,
  9.7, 9.9); Chapoton's related hyperplane-arrangement enumeration.
- No priority claim; both source comparisons are bounded.

## Further questions, and the standing rule

Section 29 gathers Part I's five questions and Part II's five directions:
rates and further coefficients (the first coefficient answered by Part II),
fixed positive shifts (answered for fixed `y > 0`; extreme shifts open),
larger tilt domains and rare heights, effective inversion with sharper
certified constants and onsets, a complex Borel continuation, and the full
prior-work comparison.

## The inverses and the transseries volume

Classified in the front matter against
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
Part I's (108) `N(Y) = ⌈z(Y)⌉` and Part II's (218) are instances of item (1)
of `p0:thm:staircase` (each uses an admissible piecewise-linear interpolation
of the log coefficients), and their sandwiches follow from it as item (2)
does; the common Lambert base (Part I (14), Part II (220)) is an instance of
`p0:prop:factorial-core` (`κ = 2`, `d = −(2 + log ρ)`); the refined inverses
(107), (219), (221), (222) are analogues of the first term of the volume's
operator series, with the Parts' own error bounds.

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`cff2b48aa`) reconstructed its
additions from the commit's diff, rebuilt both delivered manuscripts and diffed
them against the Parts, and read A096537 (#8) and A096542 (#11) again.

- **Confirmed, checked hardest:** both refutations. The check computed `a_n`
  and the A096542 rows by its own recurrence
  `P_{n+1}(y) = y Σ_k C(n,k)(k+1) P_k(y+1) P_{n−k}(y)` (from
  `F_y = exp(x y F_{y+1})`), with `T(n,k)` recovered by exact interpolation in
  `y`. The live terms (15) and triangle entries (39) agree;
  `T(n,1) = n·a_{n−1}` for `n ≤ 11`, and `T(n,1) = n·a_n` only at `n = 1`.
  Stirling turns Theorem 1.1 into the limit `2√(2π/ρ)`;
  `√(2/(πρ)) = 1.003552515326411079545…` confirms the truncation and the
  rounding. Fits of the check's own values to `n = 600` in powers of
  `n^(−1/3)` give `c_0 = 1.00356`, `c_1 = −0.437`.
- **Confirmed:** the quoted OEIS lines (verbatim); the Lambert base as a
  `p0:prop:factorial-core` instance (`κ = 2`, `d = −(2 + log ρ)`); the staircase
  instances; the numbering (Part I's 135 labels unchanged, including Sections 1
  and 13 where the remarks sit; Part II's 136 shifted by 14 sections and 109
  equations; 19 added); the bibliography merge (both Parts' details kept;
  Report 193's `dlmf9` wording is subsumed by Report 192's Section 9.9(i)); the
  three unshipped certificate files as byte copies; the 49 staged files; both
  exact checkers and Part II's interval tests (outputs equal to the records).
- **Qualified (dated note in Remark 1.4):** the sentence saying that a
  short-range fit could not have distinguished the two amplitudes holds only
  for fits that omit the scale `n^(−1/3)`. With that scale, `n ≤ 100` already
  gives `c_0 = 1.0036`; fits in powers of `1/n` or `n^(−1/2)` give 0.95–0.99 on
  every range up to `n = 300`. At `n = 2000` the intake's 0.9695 is 3.4 % below
  the limit (the remark said about 3.5 %).

The check's record is the last paragraph of the front-matter section "What was
checked, and what was not". Its code and outputs are outside the repository.

## Relation to the repository

No other placed report treats A096537, A096542, continued exponentials or
depth-weighted labelled trees. No Lean or Rocq development treats them.

## Labels and numbering

All labels carry the prefix `xtw:`: Part I `xtw:airy:` (Report 192's 135
labels and the write's two remarks), Part II `xtw:frac:` (Report 193's 136),
and the write's 17 others (`xtw:sec:` for the front sections and Section 29,
`xtw:q:` for its six questions, `xtw:airy:part`, `xtw:frac:part`); 290 in all.
The delivered labels were prefixed before anything cited them.

| Part | Manuscript | Sections | Statements | Equations |
|---|---|---|---|---|
| I | Report 192 | 1–14, unchanged | `k.j`, unchanged; Remarks 1.4 and 13.1 added after the last statement of their sections | (1)–(109), unchanged |
| II | Report 193 | `k + 14` (15–28) | `(k + 14).j` | `(k + 109)` (110–223) |

Both manuscripts number equations continuously; the merge keeps that. Checked
against the `.aux` files of separate builds of the two delivered sources.

## Notation

No symbol was renamed. Shared with the same meaning: `F_y`, `P_n(y)`, `a_n`,
`b_n`, `ρ`, `α`, `c_{n,h}`, `H_h`, `Ai`, `Bi`, `w`, `U`. The front-matter
table lists the letters that change meaning, with the tempting false
readings: Part I's `β = 2^(−1/3)` is Part II's `a`, while Part II's `β` is the
shift offset `y − 1`; the two epsilons are different scales (`1/(eh)` versus
`h^(−1/3)`); Part II's `f` is `K` times Part I's density `p`, not a density;
`K`, `C`, `L_n`, `N`, `T`, `D`, `M`, `J`, `Q`, `x`, `X`, `r`, `z` differ.

## The write's additions

The front matter (Guide, status table, OEIS entries, inverses, notation,
provenance and merge decisions, what was checked, neighbours), the
`\partsource` blocks, Remarks 1.4 and 13.1, Section 29, nine dated `[write]`
notes in the Parts (Sections 12, 13, 14, 15, 16, 27, and three in 28), the label
prefixes, single entries for the seven bibliography keys the two manuscripts
share (with Report 193's additional DLMF 9.7 detail), a pointer from
Report 193's `report192` entry to Part I, and the entry `tsvol`. The preamble
is the union of the two delivered preambles plus `longtable` and `xurl`.
Everything else is delivered text.

## Files

```text
README.md                                         this guide (replaces Report 192's delivered README)
article.tex                                       the merged report (delivered Report192.tex, merged with Report193.tex)
article.pdf                                       compiled report, 60 pages
192-airy-DATA_SOURCES.md                          Part I: sources and attribution (delivered DATA_SOURCES.md)
192-airy-README_REPRODUCIBILITY.md                Part I: reproduction and packaging (delivered README_REPRODUCIBILITY.md)
192-airy-code-README.md                           Part I: the exact code (delivered code/README.md)
192-airy-data-README.md                           Part I: the inputs (delivered data/README.md)
193-frac-DATA_SOURCES.md                          Part II: sources and attribution (delivered DATA_SOURCES.md)
193-frac-README_REPRODUCIBILITY.md                Part II: reproduction (delivered README_REPRODUCIBILITY.md)
193-frac-code-README.md                           Part II: checks and certificate, trust boundary (delivered code/README.md)
193-frac-code-fixtures-README.md                  Part II: the certificate fixtures (delivered code/fixtures/README.md)
code/192-airy-check_exact.py                      Part I: exact checker (delivered code/check_exact.py)
code/192-airy-tower.py, -prufer.py, -profiles.py  Part I: towers, Pruefer enumeration, level profiles (delivered code/)
code/192-airy-diagnose_mpmath.py                  Part I: optional mpmath diagnostics (delivered code/)
code/192-airy-reproduce.py, -test_build.py, -build.py, -verify_manifest.py   Part I: replay, tests, builder, manifest (delivered at the root)
code/193-frac-check_exact.py                      Part II: exact checker (delivered code/check_exact.py)
code/193-frac-test_intervals.py                   Part II: 20,008 interval inclusion checks (delivered code/)
code/193-frac-test_guards.py                      Part II: guard tests (delivered code/)
code/193-frac-certificate.py, -certificate_io.py, -integrate_core.py, -real_kernel.py,
     -airy_interval.py, -interval_decimal.py, -jet_interval.py   Part II: the directed interval certificate (delivered code/)
code/193-frac-reproduce.py                        Part II: replay (delivered code/reproduce.py)
code/193-frac-build.py, -test_build.py, -verify_manifest.py   Part II: builder, tests, manifest (delivered at the root)
data/192-airy-oeis_fixtures.json                  Part I: 15 A096537 terms and nine A096542 rows (third-party, CC BY-SA 4.0)
data/192-airy-generated_coefficients_48.json      Part I: author-generated a_0..a_48 (not OEIS data)
data/192-airy-generated-<name>.json               Part I: exact_checks, verification, BUILD_INFO, build_guards (delivered generated/)
data/193-frac-code-PROVENANCE.json                Part II: source pins read by the programs (delivered code/PROVENANCE.json)
data/193-frac-code-fixtures-<name>_reference.json Part II: coefficient, core and panel references (delivered code/fixtures/)
data/193-frac-generated-<name>.json               Part II: exact_checks, interval_tests, guard_tests, certificate_receipt, RESULT,
                                                  BUILD_INFO, build_guards (delivered generated/)
data/193-frac-generated-certificate-panel_verification.json   Part II: the independent panel re-aggregation (delivered generated/certificate/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
both delivered PDFs; `Report193.tex` and Report 193's `README.md` (Report 192's
`README.md` was staged and is replaced by this guide); the checksum manifests
`SHA256SUMS.json` (22 and 36 entries, verified at intake with full coverage);
and Report 193's `generated/certificate/coefficient.json`, `core.json` and
`panels.json`, which are byte copies of `code/fixtures/coefficient_reference.json`,
`core_reference.json` and `panels_reference.json`.

```sh
git show 60f54ea06:docs/incoming/A096537_Corrected_Asymptotic_and_Airy_Limits_Source.zip > <scratch>/r192.zip
git show 60f54ea06:docs/incoming/A096537_Fractional_Corrections_and_Gamma_Laws_Source.zip > <scratch>/r193.zip
```

**Delivered text that names the delivery layout or a file not shipped.**
Part I's `check_exact.py` imports `verify_manifest` from the package root and
`tower`, `prufer`, `profiles` from `code/`, and reads `data/…`; Part II's
programs read `code/fixtures/…` and `code/PROVENANCE.json` and write
`generated/…`; both packages' replay and build scripts check the closed
delivered inventory, including the manuscript and `SHA256SUMS.json`; the
eight `192-airy-*.md` and `193-frac-*.md` guides and `PROVENANCE.json` use
delivered paths; the articles' reproducibility sections describe the
delivered archives (dated notes there say so).

**Third-party data.** `data/192-airy-oeis_fixtures.json` holds OEIS terms of
A096537 and rows of A096542, published by The OEIS Foundation Inc. under
CC BY-SA 4.0 (https://oeis.org/LICENSE); it is third-party data under that
licence, **not** MIT-0 like the rest of the repository. The 201-term A096537
b-file was not retrieved by Report 192; its regression vector through
`n = 48` is author-generated.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash):

```sh
T=$(mktemp -d)
# Part I: exact checker (standard library only)
mkdir -p "$T/r192/code" "$T/r192/data"
for f in check_exact tower prufer profiles; do cp "code/192-airy-$f.py" "$T/r192/code/$f.py"; done
cp code/192-airy-verify_manifest.py "$T/r192/verify_manifest.py"
cp data/192-airy-oeis_fixtures.json "$T/r192/data/oeis_fixtures.json"
cp data/192-airy-generated_coefficients_48.json "$T/r192/data/generated_coefficients_48.json"
py -I -S -B "$T/r192/code/check_exact.py" > "$T/r192.json"
tr -d '\r' < "$T/r192.json" | cmp - <(tr -d '\r' < data/192-airy-generated-exact_checks.json) && echo same

# Part II: rebuild code/ with its fixtures and provenance, then run the checks
mkdir -p "$T/r193/code/fixtures"
for f in code/193-frac-*.py; do b=$(basename "$f"); case $b in
  193-frac-build.py|193-frac-test_build.py|193-frac-verify_manifest.py) ;;
  *) cp "$f" "$T/r193/code/${b#193-frac-}";; esac; done
for f in coefficient core panels; do
  cp "data/193-frac-code-fixtures-${f}_reference.json" "$T/r193/code/fixtures/${f}_reference.json"; done
cp data/193-frac-code-PROVENANCE.json "$T/r193/code/PROVENANCE.json"
cp 193-frac-code-README.md "$T/r193/code/README.md"
cp 193-frac-code-fixtures-README.md "$T/r193/code/fixtures/README.md"
py -I -S -B "$T/r193/code/check_exact.py" > "$T/ex.json"
py -I -S -B "$T/r193/code/test_intervals.py" > "$T/it.json"
tr -d '\r' < "$T/ex.json" | cmp - <(tr -d '\r' < data/193-frac-generated-exact_checks.json) && echo same
tr -d '\r' < "$T/it.json" | cmp - <(tr -d '\r' < data/193-frac-generated-interval_tests.json) && echo same
```

At the write (7 October 2026, Windows, Python 3.14.4) Part I's checker ran in
about 4 s, Part II's checker in about 1.5 s and its interval tests in about
63 s; all three outputs equalled the recorded files after CR stripping. The
intake dossier also found both checkers byte-identical under `-O`, and reran
Part II's `certificate.py` (about 2 minutes), which reproduced the four
certificate files and the receipt (562 panels, strictly negative coefficient)
byte for byte. Part II's `reproduce.py` failed in the intake's sandboxed
Windows session only because `test_guards.py` imports `unittest.mock`, whose
`asyncio` import raised WinError 10106 there (an environment failure). The
optional mpmath diagnostics and the builders were not run.

## Build

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, longtable,
geometry, microtype, hyperref, xurl, enumitem, lmodern). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was rebuilt this way with MiKTeX after the independent check
(7 October 2026): 60 pages, as before; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
sources, built the same way, give 24 and 29 pages.

## Provenance

- Batch 110 of `docs/incoming`, cluster 110-TOWER: bundle Reports 192 and 193
  (arrival `60f54ea06`), placed by `8622ca7e5` with the prefixes `192-airy-`
  and `193-frac-`; written 7 October 2026.
- Merge decisions: Report 192 is the base (Report 193 is its declared sequel);
  Report 193's re-derivations of leading facts are kept in full because its
  quantitative argument needs them, with dated notes naming the Part I
  counterparts; one table of contents; one bibliography (seven shared keys
  merged, `report192` pointed to Part I, `tsvol` added).
- Sources cited by the Parts: OEIS A096537 and A096542; Bender–Vinson (1996);
  Poland (1998); Chapoton (arXiv math/0301372); DLMF 5.2, 5.7, 5.11, 9.2, 9.7,
  9.9; Python's `decimal` documentation; the transseries volume (added by the
  write).
