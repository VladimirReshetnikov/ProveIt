# Permutations avoiding the vincular pattern 12–34 (A113226)

**Part I: exact enumeration and complete asymptotics. Part II: a record and cycle bijection, uniform asymptotics, and local large deviations**

A research report on OEIS A113226, the permutations avoiding the vincular
pattern 12–34. Bevan, Cheon and Kitaev (BCK) identify these with the
{3, 2+2}-free naturally labelled posets. The report is built from **two**
manuscripts of batch 77 (cluster P5). Both are dated 1 October 2026, both
pin ProveIt `63b9d6840`, and their author line is blank. Source 05 is an
addendum to source 04 ("The original A113226 report is unchanged", its
delivery README). The two form a version pair, not a supersession, and
both are printed in full.

| Source | Manuscript | Archive | Pin | Arrival | Placed | Printed as |
|---|---|---|---|---|---|---|
| 04 (base) | batch 77, manuscript 04: *Exact enumeration and complete asymptotics for permutations avoiding 12 34* (11-page PDF) | `a113226-asymptotics.zip` | `63b9d6840` | `096ee7b87` | `4f11bc9c0` | Part I: Sections 1–9 and Appendix A, with numbering unchanged |
| 05 (member) | batch 77, manuscript 05: *Refined enumeration of A113226: A record and cycle bijection, uniform asymptotics, and local large deviations* (9-page PDF) | `a113226-refined-addendum.zip` | `63b9d6840` | `096ee7b87` | `4f11bc9c0` | Part II: Sections 10–16 (source Section *n* is Section *n* + 9) |

Status: AI-assisted and unrefereed. **Not formalized.** No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status (see "Relation to the
repository" below for the one generic lemma that is formalized). The
delivered review records describe separate proof reviews and independent
coefficient audits. By their own account they are not formal verification
or conventional peer review.

## What the report proves, and what it does not claim

**Part I (source 04).** It derives the closed EGF
H(z) = exp{z/2 + q(3 arcsin q − π/2)/√(1−q²)}, with q = e^{z/2}/2, and the
first-order linear ODE for log H. It gives exact O(N²)-arithmetic
recurrences and identifies the cumulants as A136127 (shifted). It proves
the stretched-exponential form of BCK's Conjectures 13 and 14 with exact
constants:
A_n = D n! ρ^{−n} e^{3c n^{1/3}} n^{−5/6} (Σ a_j n^{−j/3} + O(n^{−(J+1)/3}))
for every fixed J, with ρ = log 4, c = (π²/(4ρ))^{1/3},
D = 2e^{−3}√(c/(3π)) ≈ 0.0357 (BCK's fitted estimate was near 0.032) and
β = −5/6. A finite Gaussian algorithm gives every a_j, and
a_1, …, a_4 are given exactly (Appendix A). The section on inversion gives
a controlled Lambert-W inverse and a ceiling envelope for the integer
threshold.

**Part II (source 05).** It marks the number of distinct nonempty strict
downsets (= the number of block pairs of BCK's word model) by u, and the
isolated elements by s. It proves:
- a record-to-cycle bijection that explains the exponential transform;
- exact component counts with the factor m!(m−1)!;
- a convergent local singular expansion, jointly analytic in u;
- a complex-uniform all-orders first-saddle expansion (Theorem 12.1);
- a global marking phase gap (Lemma 13.1);
- all-orders local large deviations for densities in compact subsets of
  (0, 1/2) (Theorem 14.1), with the stretched-exponential correction;
- mean and variance expansions, a central and a lattice local limit
  theorem, and asymptotic independence from a Poisson(log 4) number of
  isolated elements;
- a conditional Poisson(ρ(u)) law at atypical density, with an explicit
  n^{−2/3} correction and total-variation error O(n^{−2/3});
- Cov(K_n, J_n) = −1/2 + O(n^{−2/3}).

**Not claimed** (every source disclaimer is kept in the article):
- convergence of any correction series;
- an exponentially complete transseries, or the exponentially small
  contributions of the other singularities ρ + 2πik;
- a canonical analytic interpolation of A_n;
- certified finite-n error constants or threshold envelopes (the numerical
  comparisons are checks, not certificates);
- unconditional rounding of a truncated inverse;
- endpoint densities (k = o(n) or n/2 − k = o(n));
- an identification of Part II's statistics with a usual permutation
  statistic;
- a direct bijection to a previously named A136127 model;
- exhaustive priority.

The binary-word model, its bijections, A136127 and its leading
asymptotic, and the standard saddle methods are credited to their authors.
Part I's research questions 1 and 2 are answered by Part II as far as a
dated write note in Section 9 states. Questions 3 and 4 remain open.

## Files

```
article.tex                                     the merged report, standalone LaTeX, internal bibliography
article.pdf                                     the compiled report, 25 pages (title and contents pages 1–2,
                                                "About this report" pages 2–5, Part I pages 5–15,
                                                Part II pages 15–24, Appendix A page 24, references 24–25)
README.md                                       this guide
04-asymptotics-proof.md                         source 04's proof revision (SHA-256 5398b71c…, pinned by its review), as delivered
04-asymptotics-root-mathematical-review.md      source 04's proof review and independent a_1, a_2 check, as delivered
04-asymptotics-root-prior-art-check.md          source 04's source and known-transform verification, as delivered
05-refined-refined-proof.md                     source 05's expanded companion proof, as delivered
05-refined-mathematical-review.md               source 05's fresh independent mathematical audit, as delivered
05-refined-root-refinement-review.md            source 05's earlier pinned mathematical reviews, as delivered
05-refined-reproduction-review.md               source 05's replay environment, tests and limits, as delivered
05-refined-typesetting-review.md                source 05's report-to-proof and visual checks of its 9-page PDF, as delivered
05-refined-literature-screen.md                 source 05's attribution and overlap screen, as delivered
code/04-asymptotics-exact_recurrence.py         source 04: cumulant/EGF recurrence, insertion rules (n <= 65), brute force (n <= 8);
                                                writes exact_values.json beside itself
code/04-asymptotics-asymptotic_coefficients.py  source 04: the finite Gaussian generator of a_j (default order 4)
code/04-asymptotics-validate_asymptotics.py     source 04: scaled residuals and inverse errors; reads exact_values.json
code/04-asymptotics-root_coefficient_audit.py   source 04: separate hand expansion of a_1, a_2 (prints JSON)
code/04-asymptotics-replay.sh                   source 04: the short replay (delivery names; reads exact_values.json)
code/04-asymptotics-build.sh                    source 04: its PDF build (builds the unshipped a113226-asymptotics.tex)
code/05-refined-refined_coefficients.py         source 05: first- and second-saddle coefficient algorithms (order 3)
code/05-refined-validate_refinement.py          source 05: exact refined rows, literal word counts, saddle samples;
                                                imports refined_coefficients; writes exact_rows.json and validation.json
code/05-refined-verify_record_bijection.py      source 05: record/cycle round trips through n = 8
code/05-refined-root_two_saddle_audit.py        source 05: separate hand expansion of b_1, b_2 (prints JSON)
code/05-refined-independent_b3_audit.py         source 05: separate degree-six check of b_3; reads refined_coefficients.json
code/05-refined-fresh-independent-audit.py      source 05: direct-poset audit through n = 8 and independent saddle expansions;
                                                hashes and reads unshipped files (see below)
code/05-refined-verify_package.py               source 05: whole-release verifier (needs the complete delivered package)
code/05-refined-verify.sh                       source 05: runs verify_package.py
data/04-asymptotics-asymptotic_coefficients.json   source 04: constants and a_0..a_4, symbolic and 70-digit decimal
data/04-asymptotics-validation.json                source 04: sampled ratios, scaled residuals and inverse errors (n <= 1000)
data/04-asymptotics-root_coefficient_audit.json    source 04: output of the a_1, a_2 audit
data/04-asymptotics-quality_checks.json            source 04: release checks (pins the delivered tex, PDF and proof hashes)
data/04-asymptotics-repository-check.json          source 04: its ProveIt search at 63b9d6840 (no matches)
data/04-asymptotics-short_replay.log               source 04: recorded output of its short replay
data/04-asymptotics-requirements.txt               mpmath==1.3.0, sympy==1.14.0
data/05-refined-refined_coefficients.json          source 05: first- and second-saddle coefficients through order 3
data/05-refined-validation.json                    source 05: word counts, singular, moment, local-count, complex-u and
                                                   conditional samples (N = 400; also the rows for n <= 8)
data/05-refined-record_bijection_validation.json   source 05: 30,326 round trips through n = 8, one-cycle counts
data/05-refined-root_two_saddle_audit.json         source 05: output of the b_1, b_2 audit
data/05-refined-independent_b3_audit.json          source 05: output of the b_3 audit
data/05-refined-fresh-independent-audit.json       source 05: output of the fresh audit (pins its inputs' SHA-256)
data/05-refined-requirements.txt                   sympy==1.14.0, mpmath==1.3.0 (same pins as source 04's, other order)
```

**Not shipped:**
- the two delivered PDFs (`article.pdf` is a build of the merged text);
- the two delivered READMEs (this README replaces them);
- source 05's manuscript (its text is Part II);
- source 04's `manifest.json` (SHA-256 of 20 files, verified 20/20 at
  placement and retired);
- source 05's `SHA256SUMS` (verified 26/26 and retired);
- source 05's `build.sh` (builds only its unshipped manuscript);
- the two heavy exact tables, which are regenerable (next section).

All of these survive in the arrival commit `096ee7b87`. Source 04's
manuscript was staged as `article.tex` and is replaced by the merged text.

## Reconstructing the excluded data

The two exact tables of the delivery are not shipped, because they are
heavy and regenerable (Vladimir, 2026-10-02). Both survive in the arrival
commit:

```
git show 096ee7b87:docs/incoming/a113226-asymptotics.zip      > a.zip
git show 096ee7b87:docs/incoming/a113226-refined-addendum.zip > b.zip
```

**Part I: A_n and the cumulants ℓ_n through n = 1000** (`exact_values.json`,
2,236,789 bytes, LF). Run on a copy, because the script writes beside
itself:

```
mkdir p1 && cp code/04-asymptotics-exact_recurrence.py p1/exact_recurrence.py
cd p1 && python3 exact_recurrence.py --n 1000 --check-n 65 --brute-n 8
```

This writes `exact_values.json` and took about 2.5 minutes (141 s) on the
intake machine under load. Under Windows Python the file is written with
CRLF line endings (2,238,803 bytes). After CRLF→LF it is byte-identical to
the delivered file; this was checked at intake and re-checked at the write.

**Part II: the refined triangle A(n, k) for n ≤ 400** (`exact_rows.json`,
18,071,638 bytes, one line). Copy the script and the module it imports:

```
mkdir p2 && cp code/05-refined-validate_refinement.py p2/validate_refinement.py
cp code/05-refined-refined_coefficients.py p2/refined_coefficients.py
cd p2 && python3 validate_refinement.py --n 400 --brute 8
```

This writes `exact_rows.json` and `validation.json` and takes several
minutes. The delivery reports about 4 minutes for the whole n = 400
validation, and its recorded `elapsed_seconds` is 214.6. The full n = 400
regeneration was not rerun here: its cost grows roughly like N⁵. The rows
were regenerated for n ≤ 200 at intake (112 s) and for n ≤ 120 at the write
(4 s, the `exact_rows` function alone). Both are value-identical to the
corresponding prefix of the delivered file. Under Windows Python the
single-line file gains one CR byte.

Both scripts write beside themselves, so always run them on copies. In
the shipped layout they would write unprefixed files into `code/`.

## Rerunning the checks

Python 3 with the pins in `data/04-asymptotics-requirements.txt` is
needed (equivalently `uv run --no-project --with sympy==1.14.0 --with
mpmath==1.3.0 python …`; `py` on this Windows machine). Every script finds
its inputs and writes its outputs **beside itself, under the delivered
names**, so none of them runs from `code/` as shipped. Run them on a copy
with the delivered layout, which is either a fresh extraction of the
archives above or the shipped files with their prefix stripped:

- **Part I short replay** (`code/04-asymptotics-replay.sh`). It reruns the
  generator, the audit and `validate_asymptotics.py`, then checks the
  exact prefix n ≤ 100, the insertion rules (n ≤ 40) and brute force
  (n ≤ 8). It **reads `exact_values.json`**, as does
  `validate_asymptotics.py`. In a fresh extraction of `a.zip` the file is
  present; in a copy of the shipped files, regenerate it first (previous
  section). The replay overwrites `asymptotic_coefficients.json`,
  `root_coefficient_audit.json` and `validation.json` in its directory,
  so never run it in place.
- **Part II verifier** (`code/05-refined-verify_package.py`, run by
  `code/05-refined-verify.sh`). It checks the delivered package as a
  whole. It aborts without `SHA256SUMS` and requires the manuscript, the
  PDF, the README, `build.sh` and `exact_rows.json`, none of which is
  shipped. **Run it in a fresh extraction of `a113226-refined-addendum.zip`
  from `096ee7b87`** (`b.zip` above): `bash verify.sh`, or
  `bash verify.sh --full --build` for the n = 400 rows and the PDF rebuild.
  Byte-identity of the rebuilt PDF is promised only on the delivery's TeX
  toolchain.
- **Part II fresh audit** (`code/05-refined-fresh-independent-audit.py`).
  It hashes `refined-proof.md`, `a113226-refined-addendum.tex`,
  `refined_coefficients.json` and `exact_rows.json`, and reads the last
  two. Run it in the fresh extraction too.
- **Single Part II programs.** `refined_coefficients.py --order 3`,
  `root_two_saddle_audit.py`, `independent_b3_audit.py` (reads
  `refined_coefficients.json`) and `verify_record_bijection.py` run in a
  copy that holds only the unprefixed code and that JSON file.
- **CRLF on Windows.** Every program writes its JSON with Python's
  text-mode `write_text`. Under Windows Python the outputs therefore have
  CRLF line endings. Source 04's README promises byte-identical JSON
  outputs; compare after converting to LF (`diff --strip-trailing-cr`), or
  run under a POSIX Python. The delivered verifiers compare parsed JSON,
  not bytes, and are unaffected.

The checks at intake (copies under the intake scratch area) were:
- source 04's full exact regeneration: PASS, byte-identical after CRLF→LF;
- source 05's row regeneration: value-identical through n = 200.

The other suites of both sources were not rerun at intake. Two things
were checked independently at intake. First, the EGF's Taylor
coefficients reproduce 1, 1, 2, 6, 23, 107, 585, 3669, 25932. Second, the
residual (r − 1 − a_1 n^{−1/3}) n^{2/3} at n = 250, 500, 1000 (0.886,
0.907, 0.923) approaches a_2 = 0.9816, with the drift expected from
a_3 = −0.530. At the write, every u = 1 specialization stated in the
article's notation table was rechecked to 40 digits: Part II's ρ, c, D, K,
q, s_1, s_2, r_1, a_1, a_2, α(1) and V(1) against Part I.

## Labels and numbering

Every label carries the prefix `vav:`; Part II's carry `vav:rf:`. The
staged `article.tex` (source 04 as delivered) had 39 unprefixed labels. All
39 are kept with the prefix `vav:`. Source 05's 34 labels are kept with the
prefix `vav:rf:`. The write added the following:
- 8 `vav:sec:*` labels on Part I's unlabelled sections;
- 8 `vav:rf:sec:*` labels on Part II's sections and on its one subsection;
- `vav:part:one`, `vav:part:two` and `vav:tab:notation`.

That makes **92** labels (pattern `\\label(\[[^]]*\])?\{`). No label is
renamed apart from the prefix, and none is removed.

**Part I keeps its delivered numbering exactly.** Its Sections 1–9,
equations (1)–(36), Theorem 1.1 and Appendix A are unchanged. The front
section "About this report" is unnumbered, and Part I's appendix is placed
after Part II. **Part II:** source Section *n* is Section *n* + 9, and
source equation (*k*) is equation (*k* + 36). Its Theorem 1, Lemma 1 and
Theorem 2 are Theorem 12.1, Lemma 13.1 and Theorem 14.1, because theorems
and lemmas share Part I's section-based counter. The `.aux` numbers of all
73 delivered labels were compared with builds of the two delivered
sources: there were 0 mismatches against this rule. The delivered reviews
of source 05 cite its own equation numbers, so for example its "formula
(30)" is equation (66) here.

## Merge decisions and notation

- The Parts are printed one after the other. Part II re-derives Part I's
  analysis at a general marking parameter u, and its u = 1
  specializations are kept where Part II states them; nothing is deduplicated
  away.
- The bibliographies are merged. Part II's keys `BCK`, `OEIS`, `Elizalde`,
  `A136127` and `Testart` point to Part I's entries for the same works.
  Its `ProveIt` entry is added as `proveit`.
- **Renamed symbols** (all three are in Part II, and each is disclosed in
  the article's Table 1):
  - Stirling numbers `S(n,m)` are printed `{n brace m}` (they clashed with
    the analytic factor `S(w,u)`);
  - `T = coth((ρ−w)/4)` is printed `𝒯` (it clashed with `T(x,y,u)`);
  - the compact parameter interval `U` is printed `𝒰` (it clashed with
    Part I's Gaussian variable `U`).

  No normalization changed.
- Part II's phrase "the original report" is replaced in four places by
  "Part I", with a cross-reference.
- Part II's `\,\dd x` is printed with Part I's `\dd` macro, which already
  contains the thin space.
- The preamble merges both sources' packages and macros. It also allows
  URL breaks at `-` and `_` for the file names in the notes.
- Table 1 of the article lists every letter whose meaning changes between
  the Parts or inside Part II, with the false reading beside the true one.
  The letters are a, b, L, ℓ, S, s, T, U, X, q, h, N, α, d, f, C, P, R, M,
  J, K_n and k. It also gives the u = 1 identities ρ(1) = log 4,
  c(1) = c, D(1) = D, K(1) = K, a_j(1) = a_j and L_n(1) = ℓ_n.
- Dated write notes (2 October 2026, batch 77P5) were added in these
  places:
  - after Part I's citation of Elizalde (the sibling report);
  - at the end of Part I's Section 1 (Part II extends Theorem 1.1);
  - after Part I's open bijection question in Section 3 (answered by
    Section 10.1, narrower form open);
  - at the end of Section 7 (transseries volume and staircase theorem);
  - in Section 8 (shipped names, excluded data);
  - in Section 9 (repository context; the status of questions 1–4);
  - at the start of Part II;
  - in Section 16, three times (excluded rows and shipped names, the
    "original release", repository context).

  No statement of either source is changed.

## Relation to the repository and to neighbouring reports

- **Sibling report on A113227.**
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a113227-powered-catalan/`
  is built from batch-77 manuscripts 57 and 56 of cluster P2, and was
  written concurrently with this report. It treats the powered Catalan
  numbers, the avoiders of the sibling vincular pattern 1–23–4.
  - Elizalde (2006) bounded both sequences without a precise equivalent.
    The two reports supply the precise asymptotics for the two patterns,
    by unrelated methods: here an EGF and a stretched-exponential saddle,
    there a positive Bessel spectral representation. They are siblings,
    not duplicates.
  - Neither pair of manuscripts cites the other, because they are
    contemporaneous. Part I does, however, cite Callan's paper on the
    1–23–4 pattern (its Section 9) for the fast recurrence. So "neither
    cites the other" holds for the manuscripts, not for the patterns'
    literature.
  - The two were kept as separate reports, one sequence per report as
    elsewhere in this collection, rather than as Parts III–IV of this one.
- **Transseries volume.** The Lambert-W inverse and the integer-threshold
  envelope of Section 7 re-derive the inversion apparatus of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
  namely `p0:thm:lambert-core`, `p0:thm:perturbed-inversion` and
  `p0:thm:staircase`. No novelty is claimed there.
- **Formal status.** No statement about A113226 is formalized. The only
  related formal statements are generic: the separation clause of the
  staircase theorem, and its failure for arbitrarily small error. These
  are the Lean theorems `Fabius.staircase_separation` and
  `Fabius.staircase_separation_fails` in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.
  They say nothing specific about this sequence.
- **Repository searches in the sources.** Both sources searched ProveIt at
  `63b9d6840` and found nothing. That pin is kept as provenance, and
  dated notes record that the repository now contains this report and the
  sibling report. No other report treats A113226, A136127 or the BCK model
  (`rg` of the repository at the write).

## Delivered files that use delivery names or name unshipped files

- `code/04-asymptotics-replay.sh`, `code/04-asymptotics-build.sh`,
  `code/05-refined-verify.sh`, `code/05-refined-verify_package.py` and
  `code/05-refined-fresh-independent-audit.py` all run on the delivered
  unprefixed names.
  - `build.sh` compiles `a113226-asymptotics.tex`, which is not shipped
    (it is `article.tex` before the merge). It also contains a branch for
    the delivery's own environment (`/tmp/hamiltonian-rank-build`).
  - `verify_package.py` requires the unshipped `SHA256SUMS`, PDF,
    manuscript, README, `build.sh` and `exact_rows.json`.
- `04-asymptotics-proof.md` and source 04's review use delivery names.
  `data/04-asymptotics-quality_checks.json` pins the SHA-256 of the
  delivered manuscript and of its 11-page PDF, neither of which is shipped
  (`article.tex` is the merged text). Its proof hash `5398b71c…` matches
  the shipped `04-asymptotics-proof.md`.
- `data/04-asymptotics-short_replay.log` is the delivery's own run.
- `data/05-refined-fresh-independent-audit.json` records the SHA-256 of
  the excluded `exact_rows.json` (`2a155664…`), of the unshipped
  manuscript (`b4fe1a9e…`), of `refined-proof.md` (`c35244db…`, equal to
  the shipped `05-refined-refined-proof.md`) and of
  `refined_coefficients.json` (`49ea4010…`, equal to the shipped
  `data/05-refined-refined_coefficients.json`). The pins on the excluded
  and unshipped files refer to the copies in the arrival commit.
  `05-refined-mathematical-review.md` pins the same manuscript, and
  `05-refined-typesetting-review.md` pins it and the delivered PDF
  (`b15521c0…`). The manuscript and PDF hashes in
  `data/04-asymptotics-quality_checks.json` (`f1c8aa69…`, `9c78222a…`) are
  those of source 04's delivered files.
- Source 05's reviews cite the delivered nine-page PDF's equation and
  section numbers (see "Labels and numbering"). Its reproduction review
  describes the complete package with `SHA256SUMS` and the exact rows.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build uses pdfLaTeX (MiKTeX here) and needs the `lmodern`, `microtype`,
`float`, `array` and `booktabs` packages. It gives 25 pages with 0 errors,
0 warnings (no undefined references or citations, no multiply defined
labels, no duplicate destinations) and no overfull or underfull boxes.
Build in a scratch directory and keep only `article.pdf`.
