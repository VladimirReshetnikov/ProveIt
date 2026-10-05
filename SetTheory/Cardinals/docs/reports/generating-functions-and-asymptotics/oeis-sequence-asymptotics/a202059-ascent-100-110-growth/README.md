# Ascent Sequences Avoiding 100 or 110

**The sharp linear logarithmic constant for A202059, brackets for A202060, and factorial logarithmic growth**

This is a research report built on 5 October 2026 (write batch 102) from
two manuscripts of one external research session, Reports 243 and 241 of
the session bundle of Reports 1–243, both dated 5 October 2026. Both count
ordinary ascent sequences (`x₁ = 0`, `xᵢ ≤ 1 + asc(x₁…xᵢ₋₁)`) that avoid
classical length-3 patterns: `aₙ` avoids 100 ([A202059](https://oeis.org/A202059)),
`dₙ` avoids 110 ([A202060](https://oeis.org/A202060)), `cₙ` avoids 000, 100
and 110 (Callan–Mansour's Class 36), and, in Part I only, `eₙ` avoids 000
and 100 (no OEIS number).

- **Part I** (Report 243, the base): the linear logarithmic constant,
  `log aₙ = n(log n − 2 log log n + log 2 − 1) + O(n (log log n)²/log n)`,
  the same for `eₙ`, so `(log n)² (aₙ/n!)^{1/n} → 2`; the bracket
  `[−log 2 − 1, log 2 − 1]` for `dₙ` and `cₙ`; two-term first-crossing
  inverses.
- **Part II** (Report 241, the **earlier** report): the two logarithmic
  orders `log uₙ = n log n − 2n log log n + O(n)` for `c, a, d`, an exactly
  counted fresh-label family, the **refutation of the fractional-factorial
  scale `Γ(3n/4+1) μⁿ n^g` conjectured by Conway, Conway, Elvey Price and
  Guttmann** (EJC 29(4) (2022) P4.25, Sections 6–7), and
  non-P-recursiveness.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *The Sharp Linear Logarithmic Constant for 100 Avoiding Ascent Sequences: Triangular comparisons and controlled inverse bounds* (base); author line "Report 243" | 243 | `Report243.zip` (576,065 bytes, 39 files; `article.tex` + 13 `sections/*.tex`, 652 lines; 16 pp.) | none (cites Report 241 by title) | `6ab1f1979` | Part I, Sections 4–15 |
| *Factorial Logarithmic Growth of Pattern Avoiding Ascent Sequences: Ordinary ascent sequences avoiding 100 or 110*; author line "Report 241" | 241 | `Report241.zip` (554,046 bytes, 29 files; `article.tex` + 10 `sections/*.tex`, 546 lines; 13 pp.) | none (cites the A202058 and A294220 report articles on `main`, "inspected 5 October 2026"; both exist) | `6ab1f1979` | Part II, Sections 16–24 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `6ab1f1979` (batch 102, cluster 102-ASC100) removed them from
`docs/incoming/`. The write is batch 102's "Write batch 102
(a202059-ascent-100-110-growth): new report, ascent sequences avoiding 100
or 110".

**Priority.** Report 241 came first, and Report 243 says that it
"refines" it. Report 241 has priority for the two logarithmic orders, the
marked-occurrence upper encoding that Report 243 sharpens, and the
refutation, which Report 243 cites and explicitly does not claim as a
second new refutation. Report 243 is the base only because its setting
contains Report 241's (four classes instead of three) and every main
estimate of Report 241 follows from it (Table 1 of the article).

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, says it is
AI-assisted, or carries "prepared for private review" wording (the
triage's flag was a false positive: the only hits are negations). Every
result, proof, example, remark, question and limitation of both
manuscripts is printed.

## Files

The directory holds 38 files: 7 at the root, 15 in `code/`, 16 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 243, prefix `243-sharp-`**: 22 files besides the article (2 at
the root, 8 in `code/`, 12 in `data/`); its `article.tex` and
`sections/*.tex` are the base of `article.tex` (the write inlined the
thirteen section files, which the placement had staged, so `sections/` is
gone). Root: the source and scope note, the computation note. `code/`: the
builder, the shared helpers, the exact counts, the refined upper-bound
encoding, the positive-row lower construction, guard tests, the archive
replay and the suite runner `verify_all.py`. `data/`: the four
mathematical and guard receipts, the reproduction receipt, five CSV views,
the source-prefix fixture (also Report 241's, byte-identical) and the
requirements note (likewise).

```
243-sharp-COMPUTATION.md
243-sharp-SOURCES.md
code/243-sharp-build.py
code/243-sharp-common.py
code/243-sharp-exact_counts.py
code/243-sharp-guard_tests.py
code/243-sharp-positive_rows.py
code/243-sharp-reproduce_zip.py
code/243-sharp-upper_bound.py
code/243-sharp-verify_all.py
data/243-sharp-all_lengths.csv
data/243-sharp-count_receipt.json
data/243-sharp-counts.csv
data/243-sharp-guard_receipt.json
data/243-sharp-markov.csv
data/243-sharp-positive_rows.csv
data/243-sharp-positive_rows_receipt.json
data/243-sharp-reproduction_receipt.json
data/243-sharp-requirements.txt
data/243-sharp-source_prefixes.json
data/243-sharp-upper_bound_receipt.json
data/243-sharp-upper_bounds.csv
```

**Report 241, prefix `241-growth-`**: 13 files (2 at the root, 7 in
`code/`, 4 in `data/`). Root: the source and scope note (with the page
references into the CCEG journal version), the computation note. `code/`:
the builder, the shared helpers, the exact counts, the family
construction, the occurrence-encoding verifier, guard tests and the
archive replay. `data/`: the four receipts.

```
241-growth-COMPUTATION.md
241-growth-SOURCES.md
code/241-growth-build.py
code/241-growth-common.py
code/241-growth-construction.py
code/241-growth-exact_counts.py
code/241-growth-guard_tests.py
code/241-growth-reproduce_zip.py
code/241-growth-upper_bound.py
data/241-growth-construction_receipt.json
data/241-growth-count_receipt.json
data/241-growth-guard_receipt.json
data/241-growth-upper_bound_receipt.json
```

**Not shipped** (all retrievable from `60f54ea06`): both PDFs
(`Report243.pdf`, `Report241.pdf`); both `MANIFEST.sha256` (verified 38/38
and 28/28 by `build.py --verify-only` at the placement and again at the
write; repository policy drops checksum manifests); both delivery READMEs
(243's was staged and is replaced by this guide; its content is summarized
under "Delivery names"); Report 241's `article.tex` and `sections/*.tex`
(printed as Part II); Report 241's `code/source_prefixes.json` and
`requirements.txt` (byte-identical to Report 243's, shipped once).

## Labels and numbering

Label prefix **`a59:`**: Part I uses `a59:` (Report 243's 61 labels), Part
II `a59:g:` (Report 241's 49 labels; the seven label names the two
manuscripts share are thereby distinct). The write added 17: `a59:part`,
`a59:g:part`, two Part II subsection labels (`a59:g:sub:fixed`,
`a59:g:sub:quant`), six labels of its remarks and corollary
(`a59:rem:Rlead`, `a59:rem:report242`, `a59:g:rem:implied`,
`a59:g:rem:upperimplied`, `a59:g:cor:enonp`, `a59:g:rem:inverseimplied`)
and seven front-matter and appendix labels (`a59:sec:guide`,
`a59:tab:map`, `a59:sec:notation`, `a59:tab:notation`, `a59:sec:limits`,
`a59:app:provenance`, `a59:tab:crosswalk`). 127 labels in all.

Sections are numbered continuously, so the manuscripts' numbers shift:
Part I's Section `k` is Report 243's Section `k − 3`, Part II's Section `k`
is Report 241's Section `k − 15`; equations and theorems are numbered within
sections and shift with them, and are otherwise unchanged (checked against
builds of the delivered sources: all 110 labels carry the expected
numbers). The write's own results are numbered W1–W6 on a separate counter.
For example Report 243's Theorem 1.1 is Theorem 4.1 here, Report 241's
Corollary 5.1 (the refutation) is Corollary 20.1. Appendix A's Table 3
maps every numbered result. The delivered notes and code use the
manuscripts' own numbers.

## Notation

No symbol was renamed. `aₙ, dₙ, cₙ`, the ascent condition and the first
crossing (`νᵤ(X)` in Part I, `Nᵤ(X)` in Part II, both `min{n : uₙ ≥ X}`)
mean the same in both Parts; Part II writes `𝒜ₙ(P)` for Part I's
`Avₙ(P)`. Section 2 (Table 2) lists every letter with different meanings,
with the tempting false reading. The most dangerous is **`b`**: in Part I
`bₙ = Σᵣ T(n,r) = A098569(n−1)`, the triangular comparison count; in
Part II `b` is the block size, and in the proof of its non-P-recursiveness
corollary `bₙ = uₙ/n!`. Others: `T` (a binomial term against a number of
stages), `S`, `H`, `L` (log n, log N or log X in Part I; `L_b(k)` or log X
in Part II), `M`, `r` (repeats or a triangle dimension), `q`, `E`, `N`,
`F`, `D`, `κ`, `μ`. Outside this report, `a202058-ascent-000-growth` uses
`aₙ` for A202058 and `cₙ` for a normalized count.

## What the report claims

**Part I (Report 243).**
- Theorem 4.1: for `u = a, e`,
  `log uₙ = n(log n − 2 log log n + log 2 − 1) + O(n (log log n)²/log n)`,
  so `(log n)²(uₙ/n!)^{1/n} → 2`; for `u = d, c`, the linear constant lies in
  `[−log 2 − 1, log 2 − 1]`, and the normalized root has liminf ≥ 1/2 and
  limsup ≤ 2.
- Lemma 5.1: `log bₙ = n(log n − 2 log log n + log 2 − 1) + O(n log log n/log n)`
  for the triangular sum `bₙ = Σᵣ C(r(r+1)/2 + n − r − 1, n − r)`
  (= A098569(n−1); the exact enumeration is prior and credited).
- Proposition 6.3: `uₙ ≤ Σᵣ S(n,r) T(n+1,r+1)` for `a, d` (the run-indexed
  refinement of Report 241's encoding); Section 7: subexponential skeleton
  cost and the large-repeat tail.
- Sections 8–11: positive-row words with an explicit stars-and-bars rank
  bijection (Lemmas 8.1–8.2), repair of empty rows with three bounded
  fibers (Proposition 9.1), the all-length lower constant for `e` (hence
  `a`), and the doubled seed for the common class (Lemma 11.1, constant
  `−log 2 − 1`).
- Theorem 12.1: `νᵤ(X) = L/λ + (3μ + 1 − log 2) L/λ² + O(Lμ²/λ³)` for
  `a, e` (`L = log X`, `λ = log L`, `μ = log λ`), a bracket with `±log 2`
  for `d, c`.
- Section 13: explicit witnesses that the standard modification map does
  not transfer (0101 ↦ 0201 is not an ascent sequence; self-modified 0110
  contains 110, 0100 contains 100).

**Part II (Report 241).**
- Theorem 16.1: `log uₙ = n log n − 2n log log n + O(n)` and
  `(uₙ/n!)^{1/n} = Θ((log n)^{−2})` for `c, a, d`. Implied by Theorem 4.1
  (Remark W3); proved here first, by a different route.
- Proposition 17.1: an exactly counted family of `F_b(m) = ∏ H_b(k_j)`
  words in `𝒜(000,100,110)` (doubled seed credited to CCEG, Section 7),
  with fresh-record padding; worked example of 18 letters. Only here.
- Lemma 18.1 and Section 18.1: uniform bounds and, for fixed block size
  `b`, `liminf log cₙ/(n log n) ≥ b/(b+2)` (`b = 8` gives 4/5), with the
  `n`-limit taken before `b → ∞`. Only here.
- Section 19: the marked-occurrence encoding,
  `uₙ ≤ 16ⁿ Σᵣ C(n + (r+1)², n − r)` (Proposition 19.2, implied by
  Proposition 6.3, Remark W4) and its optimization (Lemma 19.3).
- **Corollary 20.1**: for `u = a, d` there are no constants with
  `uₙ ~ C Γ(3n/4+1) μⁿ n^g`, and no fixed `α ∈ (0,1)` works even with a
  factor `exp(o(n log n))`; this refutes the scale conjectured in CCEG,
  Sections 6–7 (journal pages 3, 19–24). Only here.
- Lemma 21.1 (classical: entire D-finite functions have finite order;
  reproved) and **Corollary 21.2**: `c, a, d` are not P-recursive, their
  EGFs are entire of infinite order, their OGFs are not D-finite. Only here.
- Proposition 22.1: `Nᵤ(X) = L/w + 2L log w/w² + O(L/w²)`, `w = W₀(L)`.
  Implied by Theorem 12.1 (Remark W6).
- Section 23: the count table through `n = 11` and the source recurrences.

**Added by the write** (all marked `[write]`; proofs printed in place):
Remark W1 (the leading order `L²/4` that Part I's remark after Lemma 5.1
states without proof); Remark W2 (Report 242's relative asymptotic for
`bₙ` implies Lemma 5.1); Remarks W3, W4, W6 (Part I implies Report 241's
Theorem 1.1, Proposition 4.2 and Proposition 7.1); Corollary W5 (`eₙ` is
not P-recursive, by Report 241's argument on Part I's bounds); the bounds
`4^{−n(1+o(1))} ≤ dₙ/aₙ ≤ e^{o(n)}` and `4^{−n(1+o(1))} ≤ cₙ/aₙ ≤ 1`
(note after Corollary 20.1); a comparison of `dₙ` with `bₙ` for `n ≤ 15`;
dated notes; the front matter.

## What the report does not claim

Every limitation is printed in place and collected in Section 3. In short:
**Part I**: no relative equivalent `aₙ ~ bₙ`, `eₙ ~ bₙ` or `dₙ ~ bₙ`
(only `exp(o(n))` ratios); no existence or value of the constant for `d`
or `c`, no optimality of `−log 2 − 1` for `c`; no `uₙ ≤ bₙ` and no
injection into self-modified words; the inverse error tends to infinity, no
rounding rule, non-explicit constants; no poset transfer; the doubled seed,
the encoding (Report 241's), the triangular enumeration and the
self-modified/matrix bridges are not new; not a second refutation. **Part
II**: no relative equivalent, no limit of `(log n)²(uₙ/n!)^{1/n}`, no
linear constant, prefactor or ratio asymptotic; growing inverse error, no
exact ceiling, no effective onset; CCEG's finite counts and algorithms are
not disputed; the OGF's non-D-finiteness is a formal conclusion, not an
inference from radius zero; class and permutation blocks not new; the
bounded search "did not locate" a published correction of the conjecture
(the intake's own quick search found none either), which is not a
priority certificate. **Both**: no peer review, no formal verification,
finite checks are regression tests, a manifest is not a signature, byte
reproducibility is not proof; CCEG's abstract reverses its
algorithm-efficiency labels (both follow the actual Sections 2.3–2.4).

## Further questions, and the standing rule

Each Part closes with "Further questions and research" (Sections 15 and
24). Under Vladimir's standing rule of 4 October 2026:

- **Moved or answered.** Neither manuscript states a claim without proof
  that had to be moved, and **nothing in either was found to be wrong**.
  Part I's one unproved aside (the error `𝓡` has leading order `L²/4`) is
  proved in Remark W1.
- **Part II's three questions**, with dated notes: (1) the linear-order
  constant is **answered by Part I for `a` (and `e`)**: `κ = log 2 − 1`;
  for `d` and `c` it stays open, bracketed in `[−log 2 − 1, log 2 − 1]`;
  (2) relative asymptotics: open; (3) ratios: open, advanced to the
  exponential-scale bounds above; consecutive ratios open.
- **Part I's five questions** stay as printed (the `110` and common-class
  constants; the first sublinear correction and `eₙ/aₙ`; sharper skeleton
  and fiber counts; typical word structure; sharper inversion).
- **Added by the write**: is `dₙ ≤ bₙ` for every `n`? It holds for
  `n ≤ 15`, with equality for `n ≤ 8` and `d₉ = b₉ − 1` (the intake
  dossier's observation), while `aₙ > bₙ` from `n = 5`; `dₙ ≥ bₙ e^{−o(n)}`
  would settle the `110` constant. Data only.

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`:

- The same Conway–Conway–Elvey Price–Guttmann family:
  `a202058-ascent-000-growth` (000), `a202061-ascent-120-deficit` (120),
  `a202062-ascent-201-enumeration` (201) and
  `a294220-ascent-multiplicity-caps` (multiplicity caps). Their READMEs
  list the family without 100 and 110, which this report now covers. No
  theorem is shared. Report 241 read the A202058 and A294220 articles and
  uses neither as an input (their lower bounds do not transfer to the
  common class). Part I's `Av(000,100)` lies inside the A202058 class, whose
  factorial-normalized root tends to `8/(3π²)`; here the root of `eₙ/n!`
  is `Θ((log n)^{−2})`, consistent. Pointers in those READMEs are a
  separate reciprocal-notes commit.
- `a098569-self-modified-ascents` (new in batch 102, Report 242, labels
  `pdt:`, written in `3daaab24e`): Part I's comparison count is its `b_N`
  (`bₙ = A098569(n−1)`). Its Theorem 6.1 (`pdt:thm:elementary`) gives the
  relative asymptotic of `b_N`, which implies Part I's Lemma 5.1, and its
  Lemma 3.1 (`pdt:lem:global`) uses the same comparison phase `H_N` and the
  same two gaps, `4 log 2 − 2` and `2 − 2 log 2` (Remark W2). Lemma 5.1 is
  an elementary second route to a weaker statement; the two manuscripts do
  not cite each other. That report's Section 1 already points here.
- `a336070-weak-ascents` (new in batch 102): a different object (weak
  ascent sequences, factorial root `6/π²`); no shared theorem.
- No other report treats A202059 or A202060 (searched 5 October 2026).

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of
this report is formalized; nothing about ascent sequences is formalized in
the repository.

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (checked against fresh extractions of
  both archives at the write: 50 of 50 placed files identical before the
  write replaced `article.tex`, `README.md` and `sections/`); only names
  changed (table at the end). Receipts and CSVs moved from `code/` to
  `data/`; `build.py` moved from the package root to `code/`.
- The delivered code and notes use delivery names (`build.py`,
  `code/verify_all.py`, `code/<receipt>.json`, `COMPUTATION.md`,
  `README.md`, `MANIFEST.sha256`, `Report243.pdf`, …). `build.py` and
  `reproduce_zip.py` need the delivered layout, the manifest and the PDF,
  so **none runs in this directory**.
- **Windows.** The builders and `verify_all.py` reject backslash path
  components ("backslash output components are forbidden"; forward-slash
  absolute paths are accepted) and compare receipts with raw child
  standard output, which Windows writes with CRLF ("fresh receipt
  differs"); both `guard_tests.py` stop at the backslash-path guard. These
  are platform limits, not mathematics: the individual programs run with
  `--output` and a forward-slash path write LF receipts identical to the
  shipped ones (checked at the write). Run the builders on a POSIX host.
- Report 243's five CSVs and `reproduction_receipt.json` are produced only
  by `verify_all.py`; they were not regenerated here (Windows guard).
- 243's delivered README (replaced) says: Python 3.11+, standard library
  only, commands with `-B -X int_max_str_digits=640`, a `build.py
  --verify-only` integrity check, a full `build.py --output-dir` build that
  must reproduce the frozen PDF byte for byte on its recorded toolchain
  (pdfTeX 1.40.26, TeX Live), and `code/reproduce_zip.py` for an archive
  replay. Rebuilt PDFs from MiKTeX differ in bytes (expected; both packages
  say other TeX installations may differ).
- The guard receipts count different suites: 241's `COMPUTATION.md` says
  409 cases, 243's 335 passing checks.
- `241-growth-COMPUTATION.md` and `243-sharp-COMPUTATION.md` suggest
  `/tmp/…` output paths; use a scratch directory outside the repository.

## Rerunning the checks

Run on a copy, never in this directory. The simplest route recreates the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Report243.zip > r243.zip
git show 60f54ea06:docs/incoming/Report241.zip > r241.zip
mkdir x243 x241 && unzip -q r243.zip -d x243 && unzip -q r241.zip -d x241
cd x243/Report243
py -B -X int_max_str_digits=640 build.py --verify-only
py -B -X int_max_str_digits=640 code/exact_counts.py --output C:/scratch/c243.json
py -B -X int_max_str_digits=640 code/upper_bound.py --output C:/scratch/u243.json
py -B -X int_max_str_digits=640 code/positive_rows.py --output C:/scratch/p243.json
cd ../../x241/Report241
py -B -X int_max_str_digits=640 build.py --verify-only
py -B -X int_max_str_digits=640 code/exact_counts.py --output C:/scratch/c241.json
py -B -X int_max_str_digits=640 code/construction.py --output C:/scratch/k241.json
py -B -X int_max_str_digits=640 code/upper_bound.py --output C:/scratch/u241.json
```

Compare each output with the receipt in the package's `code/` (equal to
`data/<prefix>-<name>`); add `-O` for the optimized run. Output paths must
be new, absolute, outside the package, with forward slashes on Windows. On
a POSIX host the full builders also run:
`python3 -B -X int_max_str_digits=640 build.py --output-dir /abs/new-dir`
(and 243's `code/verify_all.py --output-dir /abs/new-dir`).

Results. At the placement (dossier, Python 3.14.4, Windows, on such
copies): all six mathematical receipts reproduced byte for byte after
CRLF→LF, under normal and `-O` Python (241: counts 15 s, construction
89 s, upper bound 47 s; 243: counts 10 s, upper bound 60 s, positive rows
35 s; one `-O` run of 241's construction died of a MemoryError under
machine memory pressure and passed on rerun); both `guard_tests.py` stop
at the backslash guard; `build.py --verify-only` verified 38 and 28 files.
At the write (5 October 2026): both `--verify-only` checks verified again,
and both `exact_counts.py` runs (about 8 s each) wrote receipts
byte-identical to the shipped ones with `--output`. The longer suites were
not repeated.

## Rights

Repository contents are MIT-0. The sequence terms printed in the article
and in `data/243-sharp-source_prefixes.json`, `data/243-sharp-counts.csv`
and the receipts (`aₙ` of A202059, `dₙ` of A202060) agree with the OEIS
entries, whose data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)); the programs recompute them
from the CCEG recurrences and by literal enumeration. The common-class
prefix is Callan and Mansour's Table 2, Class 36 (EJC 32(1) (2025) P1.40),
factual data, attributed. No third-party paper is shipped. Nothing was
submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The
write's build: 44 pages, no errors, no warnings, no undefined or multiply
defined references, no duplicate destinations, no overfull or underfull
boxes. The log carries three "Infinite glue shrinkage found in box being
split" messages, one from each longtable that breaks across pages (Tables
1, 2 and 3), as in other reports with longtables. The delivered sources built
alone give 16 and 13 pages with no warnings.

## Delivered path → shipped path

Report 243 (`243-sharp-`; manuscript files unprefixed at placement):

| Delivered | Shipped |
|---|---|
| `article.tex`, `sections/*.tex` (13) | `article.tex` (Part I; sections inlined at the write) |
| `README.md` | replaced by this guide |
| `SOURCES.md`, `COMPUTATION.md` | `243-sharp-SOURCES.md`, `243-sharp-COMPUTATION.md` |
| `build.py` | `code/243-sharp-build.py` |
| `code/<name>.py` (common, exact_counts, guard_tests, positive_rows, reproduce_zip, upper_bound, verify_all) | `code/243-sharp-<name>.py` |
| `code/<name>.json`, `code/<name>.csv` (receipts, fixture, CSV views) | `data/243-sharp-<name>` |
| `requirements.txt` | `data/243-sharp-requirements.txt` |
| `Report243.pdf`, `MANIFEST.sha256` | not shipped |

Report 241 (`241-growth-`):

| Delivered | Shipped |
|---|---|
| `article.tex`, `sections/*.tex` (10) | not shipped; printed as Part II of `article.tex` |
| `SOURCES.md`, `COMPUTATION.md` | `241-growth-SOURCES.md`, `241-growth-COMPUTATION.md` |
| `build.py` | `code/241-growth-build.py` |
| `code/<name>.py` (common, construction, exact_counts, guard_tests, reproduce_zip, upper_bound) | `code/241-growth-<name>.py` |
| `code/<name>_receipt.json` (four) | `data/241-growth-<name>_receipt.json` |
| `code/source_prefixes.json`, `requirements.txt` | not shipped (byte-identical to Report 243's) |
| `README.md`, `Report241.pdf`, `MANIFEST.sha256` | not shipped |

## Provenance

Two manuscripts (bundle Reports 243 and 241) → one report; base 243,
priority 241. Arrival `60f54ea06`, placement `6ab1f1979`, write batch 102
(5 October 2026). Neither manuscript pins a ProveIt commit. Merge choices
(base, Part order, inlining of `sections/`, merged bibliography entries,
the W numbering) and every editorial change are listed in the article's
Appendix A.
