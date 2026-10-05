# The Second Logarithmic Term for Regular Tesler Matrices (OEIS A008608)

**A uniform entropy construction and integer throughput decomposition:
`log a_n = C n^{3/2} − (3/4) n log n + O(n log log n)`, `C = π√(8/27)`**

A research article dated 2 October 2026 ("Research report 106" of a
session bundle), built from one manuscript. Its title page reads
"Research report 106 / Prepared for Vladimir", and its PDF metadata give the
author as "Research report prepared for Vladimir"; both are kept as
delivered. The package carries no "prepared for private review" line, no
e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 106 (batch 103) | `A008608_Tesler_Second_Logarithmic_Term_Source.zip` (wrapper directory `report106/`, 22 files, 402,353 bytes, SHA-256 `41db84a6…9e54`), arrival commit `60f54ea06`; main file `report106.tex` | none: the package names no ProveIt commit, path or report | `9c995cefe` (batch 103) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs. The exact checks verify finite
identities and small counts; the floating-point checks are not interval
arithmetic; neither certifies any asymptotic statement.

## Trust boundaries

- **The leading term is inherited.** `log a_n ~ C n^{3/2}` is Corollary 37
  of I. Balashov, C. Bulavenko and Y. Molybog, *Tesler matrices and Lusztig
  data*, Electron. J. Combin. **33**(2) (2026), #P2.25 (published 8 May
  2026, doi:10.37236/13427; p. 17, in their notation
  `L(1^n) = ln T(1^n)`). The manuscript credits it, together with the
  leading inverse `N(y) ~ x` that follows from it. The intake fetched the
  journal PDF (its SHA-256 equals the fingerprint in `data/sources.json`)
  and checked the constant.
- **The counting inequality is an external input.** The lower bound uses
  Theorem 2.1 of Brändén, Leake and Pak (Israel J. Math. 253 (2023)),
  restated as Theorem 8.1. The intake compared the restatement with
  arXiv:2008.05907v3 (SHA-256 again equal to the `sources.json`
  fingerprint) and found it faithful: the row product starts at `i = 2` (the
  source says this is intended), the truncated margins are
  `min{α_i, λ_i − α_i}`, cell bounds may be any element of
  `ℕ ∪ {+∞}`, and §5.1 there gives the power-series capacity convention used.
  ProveIt has not checked BLP's proof. The Dedekind eta transformation
  (DLMF 23.18.5) is the only other non-elementary input.
- **Novelty of the coefficient −3/4 is uncertified.** The source's search
  was bounded and it disclaims novelty certification. The "Future
  questions" of Balashov–Bulavenko–Molybog (§5) do not ask for the second
  term, so no named question is answered. The intake did not find the term
  in BBM, BLP, O'Neill's arXiv version or the OEIS entry, but did not
  compare Leake–Morales (Adv. Appl. Math. 175 (2026) 103002) Theorem 1.2 in
  detail and made no exhaustive search.
- **Constants are non-effective.** No `O`-constant or threshold is
  explicit, including the bracket constant `D` of Theorem 10.1.

## What it proves

`a_n` counts `n × n` upper-triangular nonnegative integer matrices with all
hook sums 1 (regular Tesler matrices), equivalently integral flows on the
complete DAG on `{0, …, n}` with netflow `(1, …, 1, −n)`. **Indexing:** OEIS
A008608 has offset 1 (`a_1 … a_8 = 1, 2, 7, 40, 357, 4820, 96030,
2766572`); the manuscript adds the convention `a_0 = 1`, not an OEIS term.
Constants: `c = π/√6`, `C = 4c/3 = π√(8/27)`,
`B_U = 3/4 + (3/2) log c − (1/2) log 2π = 0.2043366936…`. Theorem numbers
follow the section counter.

- **Theorem 1.1 (`tes:thm:main`):**
  `C n^{3/2} − (3/4) n log n − 2n log log n − O(n) ≤ log a_n ≤
  C n^{3/2} − (3/4) n log n + B_U n + O(√n)`; hence
  `log a_n = C n^{3/2} − (3/4) n log n + O(n log log n)` and
  `(C n^{3/2} − log a_n)/(n log n) → 3/4`. **New:** the coefficient −3/4
  and both explicit bounds.
- **Section 2:** the interval-array and cut-load model, the constant-term
  formula (2.3), singleton elimination (**Lemma 2.1**, `tes:lem:singletons`)
  and the first-row hook recursion (2.4).
- **Lemmas 3.1–3.2 (`tes:lem:partition`, `tes:lem:Etail`):** partition and
  entropy estimates from the exact eta identity (3.7).
- **Section 4:** the elementary upper bound `log a_n ≤ U_n` (4.2), where
  removing the singleton factor produces the −3/4.
- **Proposition 5.1, Lemma 5.2; Lemmas 6.1–6.2, Proposition 6.3:** a feasible
  geometric profile (cutoff `M = 1024`) of entropy
  `C n^{3/2} − (1/4) log n! − O(n)`, with bulk throughputs
  `O(√j log j)` and a terminal layer of width
  `B_n = ⌈(4/c)√n log(n+1)⌉`.
- **Lemmas 7.1–7.2:** independent triangle moves give
  `exp((1/2) log n! − O(n))` integer throughput vectors at entropy cost
  `≤ (n − M) log 2`.
- **Theorem 8.1** (BLP, restated), **Lemma 8.2** (capacity ≥ entropy of any
  feasible table), **Lemma 9.1** (margin penalty
  `≤ log n! + 2n log log(n+1) + O(n)`), and the assembly
  `−1/4 − 1 + 1/2 = −3/4`.
- **Theorem 10.1 (`tes:thm:inverse`):** for `N(y) = min{n : a_n ≥ y}`,
  `L = log y`, `x = (L/C)^{2/3}`:
  `N(y) = x + (2C)^{−1} √x log x + O(√x log log x)`, with the integer bracket
  `⌊z − Ds⌋ < N(y) ≤ ⌈z + Ds⌉` (10.7) and monotonicity `a_{n+1} ≥ a_n` by
  an injection. **New:** the second term and the bracket (the leading
  `N ~ x` is BBM's).

Added by the write (5 October 2026), marked `[write]`:

- **Remark 4.1 (`tes:rem:linear`): `B_U ≈ 0.204` is only an upper-bound
  constant.** With the exact `log a_n` of the first 26 OEIS b-file terms,
  `log a_n ≤ U_n` holds for every `n ≤ 26` (gap 1.39, 14.96, 31.14, 41.06 at
  `n = 1, 10, 20, 26`), and
  `(log a_n − C n^{3/2} + (3/4) n log n)/n ∈ [−1.443, −1.421]` for
  `9 ≤ n ≤ 26` (−1.4213 at `n = 10`, then slowly decreasing to −1.4426 at
  `n = 26`). The actual linear behaviour at these sizes is about `−1.4 n`,
  some `1.6 n` below the upper estimate; too few terms to decide anything
  (40-digit floating point, uncertified).
- **Remark 9.2 (`tes:rem:penaltysharp`), with proof: the margin penalty is
  sharp for this family.** For every `ρ ∈ 𝓡_n`,
  `Σ h(α_i) + Σ h(β_j) ≥ log n! + 2n log log n − O(n)`, because the bulk
  outgoing totals are at least `(√a/c)((1/2) log a − log c − 1/2)`. So the
  `2n log log n` loss cannot be removed by estimating Lemma 9.1 better; it
  needs a larger capacity term, more margin vectors or another counting
  inequality.
- Notes: status (title page); Section 1.1 (provenance, credits, earlier
  bounds, novelty status, repository, indexing, notation table, collected
  non-claims); the intake comparison after Theorem 8.1; a note on
  Theorem 10.1 (what is inherited, the two forms agree, the bracket is
  non-effective and its width `2Ds + 2` is beaten by the correction term
  only by the factor `log x / log log x`); the shipped layout and intake
  reruns (end of Section 11); Section 12.1. Four references the manuscript
  omits: O'Neill 2018, Mészáros–Morales–Rhoades 2017, Armstrong–Garsia–
  Haglund–Rhoades–Sagan 2012, Haglund 2011.

**Earlier bounds (added by the write; the manuscript does not cite them).**
J. O'Neill, *On the poset and asymptotics of Tesler matrices*, Electron. J.
Combin. **25**(2) (2018), #P2.4 (doi:10.37236/6877): Theorem 5.6 of
arXiv:1702.00866v2 improves the lower bound `n! ≤ a_n` of
Mészáros–Morales–Rhoades to `a_n ≥ (2n−3)!!` and tightens their
`a_n ≤ 2^{n(n−1)/2}`, still `e^{O(n²)}`. O'Neill records Pak's Question 1.4,
whether `a_n = e^{Θ(n²)}`; BBM's Corollary 37 answers it negatively, and so
does this report's elementary upper bound (4.2) alone. These bounds do not
reach the second term; the omission affects no proof, only the priority
caveat.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- The leading equivalent and its leading inverse are not new.
- No `O(n)` remainder, multiplicative equivalent, amplitude, full expansion
  or exhaustive novelty certification. "Exponentiating an `O(n log log n)`
  error does not produce a relative-error asymptotic"; `B_U` "is a constant
  in an upper bound, not a proved coefficient of `n` in `log a_n`".
- "A bounded source check through 2 October 2026 did not locate the −3/4
  refinement … This does not certify exhaustive novelty, and no priority
  claim is needed for the proof."
- The inverse error is "asymptotic with an unspecified constant, not a
  finite certified numerical error bar or an `O(1)` inverse".
- The proof uses no fixed-dimensional saddle theorem in a growing dimension
  and no unproved local central limit approximation.
- The exact checks "do not certify a uniform asymptotic estimate or replace
  any lemma"; the fixtures are deliberately manufactured, not the profile;
  the floating sanity check is "not interval arithmetic and does not prove
  any analytic inequality"; the snapshot hashes are regression snapshots,
  not authentication; the corruption tests are no protection against
  simultaneous malicious edits.
- External scholarly PDFs are fingerprinted, not redistributed.

The write adds: novelty is uncertified also after the intake's comparison;
Theorem 8.1 is an external input whose proof ProveIt has not checked; the
write's numerical remark is uncertified.

## Further questions

Section 12.1 of the article ("Further questions and research",
`tes:sec:further`) states every unproved claim as an open question, with
source, sketch and what is missing (Vladimir's standing rule of 4 October
2026). The intake found **no false claim** in the source.

1. **An `O(n)` remainder** (`tes:q:remainder`; source item 1), sharpened by
   Remark 9.2: the loss is exact for the family used.
2. **A linear term** (`tes:q:linear`; item 2): does
   `(log a_n − C n^{3/2} + (3/4) n log n)/n` converge? Not to `B_U`; about
   −1.42 to −1.44 for `n ≤ 26` (Remark 4.1), inconclusive.
3. **A relative-error equivalent**, amplitude, full expansion
   (`tes:q:equivalent`; item 3).
4. **A sharper inverse** (`tes:q:inverse`; item 4): an `O(n)` forward error
   would give an `O(√x)` inverse error; a bounded-error inverse needs an
   `O(√n)` forward error.
5. **Other cut profiles** (`tes:q:profiles`; item 5).
6. **Priority of −3/4** (`tes:q:priority`): compare Leake–Morales
   Theorem 1.2, the journal version of O'Neill, and the Tesler and Kostant
   partition function literature.

The dossier's tags map as U1 → Question 1, …, U5 → 5, U6 → 6.

## Checks made at intake

On copies (Windows, Python 3.14.4):

- At placement, on the extracted archive: `verify_package.py` PASS (21 of 21
  files match `manifest.json`); `checks/run_corruptions.py` PASS, "2 positive
  controls and 62 fail-closed corruption rejections" (2 min 59 s); its
  regenerated `verification_normal.json`, `verification_optimized.json` and
  `corruption_run.log` equal the delivered files after the carriage returns
  are stripped; `corruption_results.json` differs only in the Python version,
  timestamps, set-iteration order inside three schema diagnostics and the
  temporary paths of two input diagnostics. `sanity/profile_sanity.py`
  (NumPy 2.3.5) PASS in 9.8 s.
- At the write, on a copy of the **shipped** files (route B below):
  `verify_exact.py` in normal and `-O` modes (4.5 s and 4.8 s), outputs equal
  to `data/verification_normal.json` and `data/verification_optimized.json`
  after stripping CR; `profile_sanity.py` PASS, integer fields and residuals
  identical, entropies differing by about `1e−10` in absolute value (the last
  three or four digits printed), as the package says floating results may.
- Not run: `build.sh` (TeX Live/Debian format and map set-up; it builds
  `report106.tex`, which is not shipped under that name).
- Independent intake checks (40-digit mpmath): the eta identity (3.7)
  against the direct series at `t = 0.3, 1, c` (agreement to `1e−40`);
  `log a_n ≤ U_n` for `n ≤ 26` against the OEIS b-file; the hook recursion
  (2.4) reproduces `a_1 … a_8`; `B_U` recomputed. The upper bound, the
  `R(t)` identity, `∫E = π²/3`, `∫xE = 3ζ(3)`, the feasibility and deficit
  bounds, the triangle moves, the margins, the dual-cell inequality, the
  penalty, the assembly `−1/4 − 1 + 1/2 = −3/4` and both forms of the
  inverse were rederived by hand. No defect was found.
- The delivered text builds with MiKTeX pdfLaTeX in 13 pages without
  warnings or bad boxes.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats Tesler matrices, flows or the
Kostant partition function, and the report's place in the collection confers
no formal status.

**Neighbouring reports.** None shares a theorem. Before batch 103 no
tracked file mentioned Tesler matrices, A008608, Lusztig data, the Kostant
partition function or flow polytopes. "Contingency" occurs only in
`generating-functions-and-asymptotics/oeis-sequence-asymptotics/a260700-parabolic-double-cosets`
(tables counted by A120733). The matrix-counting reports
`oeis-sequence-asymptotics/a007716-bipartite-multigraphs` and
`oeis-sequence-asymptotics/a261781-matrix-compositions`, and the
Lorentzian-polynomial material of
`enumerative-combinatorics/preorder-root-polytopes`, treat other objects by
other methods.

**Stale claims.** The manuscript makes no claim about the repository.
Nothing to correct; no reciprocal note was needed.

## Notation

The manuscript reuses several letters. A table in Section 1.1 fixes each
meaning, with tempting false readings; no symbol was renamed. The clashes:
`λ` (`λ_i = c/√i` in Sections 4 and 6, any `λ > 0` in (3.9), the row sums
`λ_i = Σ_j k_ij` in Theorem 8.1), `K` (absolute constants in Section 6, the
cell-bound matrix `K = (k_ij)` in Section 8), `h` (the entropy function, the
hook-sum vector in (2.4)), `T` (the count `T(h)`, the cut loads `T_i`,
`T_i^∞`), `L` (`L(t)` and `L = log y`), `G` (a feasible table in Lemma 8.2,
`G(t) = C t^{3/2} − (3/4) t log t` in Section 10), `m`/`M` (interval arrays
`m_[a,b]`, the BLP row count `m`, the bracket points `m_±`, the cutoff
`M = 1024`), `B_U`/`B_n`, `u`/`v` (argument of `h`, BLP's truncated margins),
`r`/`ρ`/`R`/`𝓡_n`, `x`/`y`/`z`, `t`/`t_j`/`s`, `D_n`/`D`, and edge versus
interval subscripts in (7.2). The preamble's `\renewcommand{\Cap}` replaces
the `amssymb` symbol of that name, which the text never uses.

## Labels

Every label carries the prefix `tes:` ("Tesler"; unused elsewhere in the
collection). The manuscript's 78 labels (`sec:`, `eq:`, `thm:`, `lem:`,
`prop:`) were prefixed before anything cited them, and every reference was
updated (39 `\eqref`, 14 `\ref`). The write added 10:
`tes:sec:provenance`, `tes:sec:further`, `tes:rem:linear`,
`tes:rem:penaltysharp`, and the six questions `tes:q:remainder`,
`tes:q:linear`, `tes:q:equivalent`, `tes:q:inverse`, `tes:q:profiles`,
`tes:q:priority`. The report has 88 labels; a build of the delivered text
and of this one give every delivered label the same number (aux files
compared). No statement, proof or number of the manuscript was changed.

## Files

```text
README.md                       this guide (replaces the delivery README)
article.tex                     the report (delivered report106.tex; labels prefixed, [write] additions)
article.pdf                     compiled report, 19 pages
checks-README.md                scope and design of the exact suite (delivered checks/README.md)
sanity-README.md                scope of the floating sanity check (delivered sanity/README.md)
code/build.sh                   deterministic three-pass TeX Live build of report106.tex (delivered at the package root)
code/verify_exact.py            fail-closed exact verifier, stdlib only (delivered checks/)
code/run_corruptions.py         positive controls and 31 corruptions in two interpreter modes (delivered checks/)
code/build_fixtures.py          authoring aid for the two input snapshots, not called by any check (delivered checks/)
code/profile_sanity.py          float64 evaluation of the profile at n = 2048, 4096 (delivered sanity/)
data/rational_fixtures.json     four rational fixtures and triangle rules (delivered checks/)
data/expected_checks.json       independent snapshots, margin digests, a_0..a_7 (delivered checks/); OEIS terms, CC BY-SA 4.0
data/verification_normal.json   verifier output, normal mode (delivered checks/)
data/verification_optimized.json  verifier output, python -O (delivered checks/)
data/corruption_results.json    per-corruption record (delivered checks/)
data/corruption_run.log         human-readable run log (delivered checks/; force-added, *.log is ignored)
data/profile_results.json       sanity results (delivered sanity/)
data/environment.txt            recorded toolchain (delivered at the package root)
data/verification_summary.json  summary record (delivered at the package root)
data/sources.json               primary sources, inspected locations, SHA-256 of the external PDFs (delivered at the package root)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, all recoverable from the arrival commit's archive (next
section): `report106.pdf`, the delivered 13-page PDF (360,521 bytes);
`manifest.json` (3,343 bytes), a SHA-256 manifest of the other 21 delivered
files (repository policy ships no checksum manifests; verified 21/21), and
its verifier `verify_package.py` (1,393 bytes); and the delivery
`README.md` (3,459 bytes), staged at placement and replaced by this guide
(its content is kept under "From the delivery README" below).

**Delivered text that names the delivery layout or files not shipped.** The
article's Section 11 describes "the accompanying source package" with
checksums. `checks-README.md` names `report106.tex`, says "From this
directory" (the delivered `checks/`), and lists the checks files without
`code/`/`data/`; `sanity-README.md` names `report106`, `checks/` and the
command `python3 sanity/profile_sanity.py --output sanity/profile_results.json`
(run from the package root, it would overwrite the recorded result).
`code/build.sh` changes to its own directory and builds `report106.tex`.
In the code, `run_corruptions.py` and `verify_exact.py` take their own
directory as `ROOT`: `verify_exact.py` reads `rational_fixtures.json` and
`expected_checks.json` beside itself unless `--fixtures`/`--expected` are
given; `run_corruptions.py` calls `verify_exact.py` beside itself, reads
the two inputs there, **writes its four records beside itself** and creates
temporary `corruption_inputs_*` directories there. **In the shipped layout
nothing runs in place**; use the routes below.

**Recorded environment.** The delivered records come from a Linux sandbox:
`data/corruption_results.json` records Python "3.12.14 … [Clang 22.1.3]",
the timestamp 2026-10-02T06:29:58Z and, in four input diagnostics, the
temporary paths
`/workspace/shared/tesler_report/checks/corruption_inputs_jwd12979/` and
`…_mz9gxfdq/`; `code/build.sh` refers to `/usr/share/texlive`. These are
paths of the producing machine, not of ProveIt.

**Third-party data.** The small counts in `data/expected_checks.json` (and
repeated in `data/verification_*.json`, `code/build_fixtures.py`,
`checks-README.md` and the article) are terms of OEIS A008608
(https://oeis.org/A008608), published by The OEIS Foundation Inc. under the
Creative Commons Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); they are
third-party data under that licence, not MIT-0 like the rest of the
repository. The intake's check of Remark 4.1 used the first 26 terms of
the OEIS b-file (by Alejandro H. Morales; terms 1–23 from Jay Pantone,
24–26 from Joel B. Lewis, as the entry credits them); no b-file is shipped.

## Retrieving the delivered PDF and manifest

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A008608_Tesler_Second_Logarithmic_Term_Source.zip > "$T/report106.zip"
sha256sum "$T/report106.zip"     # 41db84a6f47438ef1df5e11613598c466bf24fb17678c76d6dcf6d7448489e54
cd "$T" && unzip -q report106.zip && cd report106
python3 verify_package.py        # 21 files match manifest.json
ls -l report106.pdf              # 360,521 bytes, 13 pages
```

## Rerun the checks (on a scratch copy)

Requirements: Python 3.9 or later (standard library only) for the exact
suite; NumPy (2.3.5 recorded) for the sanity check, for example
`uv run --no-project --with numpy==2.3.5 python`. The programs make no
network request. Never run anything in the repository.

**Route A, delivered layout** (restore `report106/` as in the previous
section), as the delivery README gives it:

```sh
cd "$T/report106"
python3 verify_package.py
python3 checks/run_corruptions.py          # about 3 minutes; rewrites checks/*.json and checks/*.log
python3 sanity/profile_sanity.py --output "$T/profile_results.json"
```

`run_corruptions.py` refreshes the records inside the extracted copy, so
compare them with the shipped `data/` files afterwards
(`timestamp_utc`, `python`, the temporary paths and some set orders in
`corruption_results.json` always differ).

**Route B, from the shipped files** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a008608-tesler-matrices
T=$(mktemp -d); mkdir -p "$T/checks" "$T/sanity" "$T/out"
cp "$R"/code/verify_exact.py "$R"/code/run_corruptions.py "$R"/code/build_fixtures.py \
   "$R"/data/rational_fixtures.json "$R"/data/expected_checks.json "$T/checks/"
cp "$R"/code/profile_sanity.py "$T/sanity/"
cd "$T/checks"
python3 verify_exact.py    > "$T/out/normal.json"
python3 -O verify_exact.py > "$T/out/optimized.json"
cmp "$T/out/normal.json"    "$R/data/verification_normal.json"
cmp "$T/out/optimized.json" "$R/data/verification_optimized.json"
python3 run_corruptions.py                 # optional, about 3 minutes; writes into $T/checks
cd "$T" && python3 sanity/profile_sanity.py --output "$T/out/profile_results.json"
```

At the write both `cmp`s matched (after the CR stripping described below)
and the sanity run passed. `verify_exact.py` also runs read-only with
explicit inputs, `--fixtures "$R/data/rational_fixtures.json" --expected
"$R/data/expected_checks.json"`, and writes only to standard output.

**Windows notes.**

- Python writes CRLF in text mode on Windows: the redirected verifier
  output, the four records of `run_corruptions.py` (`Path.write_text`) and
  the `--output` file of `profile_sanity.py` all come out with CRLF, so
  compare after removing CR (`tr -d '\r' < file | cmp - shipped`). The
  delivery README's "compared byte for byte" holds on POSIX.
- `build.sh` needs bash and a TeX Live layout (it builds its own
  `pdflatex.fmt` and loads explicit font maps); use the MiKTeX route below
  instead.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, microtype, geometry, amsmath,
amssymb, amsthm, mathtools, booktabs, enumitem, fancyhdr, hyperref, and
array and longtable for the write's notation table); the bibliography is
embedded. Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 19 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. (TeX notes
once that it ignored infinite glue shrinkage where the notation table breaks
across pages 4 and 5; the output is unaffected.) The delivered source built
the same way gives 13 pages, equally clean. The article keeps the delivered
preamble lines that suppress PDF dates and trailer identifiers.

## From the delivery README

The delivery README (replaced by this guide) titled the package "Report
106 … Prepared for Vladimir, 2 October 2026", stated the main result with
`C = pi sqrt(8/27)`, and said that the leading logarithmic equivalent "was
proved by Balashov, Bulavenko and Molybog (2026) and is explicitly
credited". Its other content, translated to the shipped names:

- *Contents:* `report106.tex` (here `article.tex`), `report106.pdf`, `build.sh`
  (here `code/`), `checks/` and `sanity/` (here `code/`, `data/` and the two
  sub-READMEs), `sources.json`, `environment.txt`,
  `verification_summary.json` (here `data/`), `manifest.json` and
  `verify_package.py` (not shipped).
- *Verify and reproduce:* `python3 verify_package.py`, then
  `python3 checks/run_corruptions.py` ("31 deliberate corruptions in both
  normal and optimized Python"); "All guards remain active with
  `python -O`"; log timestamps change on rerun, while "The deterministic
  baseline verification results themselves can be compared byte for byte";
  `bash build.sh` with TeX Live, which fails on an overfull box or
  unresolved reference, byte-identical only "in the recorded TeX
  environment"; the optional sanity run, "not interval arithmetic", whose
  "Last-bit floating results can vary across platforms"; "No external
  author's code is run"; the build creates `build/` and `qa/`; "Check the
  manifest before rerunning tools that refresh shipped logs/results."
- *Evidence boundaries:* the analytic proof is "conditional only on the
  stated, cited existing counting theorem and classical eta
  transformation"; finite exact computation checks algebra, indexing and
  small counts; numerical sanity has "still weaker evidentiary scope".

## Provenance

- Sources cited by the manuscript: OEIS A008608 (checked 2 October 2026);
  Balashov, Bulavenko and Molybog, Electron. J. Combin. 33(2) (2026) #P2.25,
  Corollary 37; Brändén, Leake and Pak, Israel J. Math. 253 (2023) 43–90
  (arXiv:2008.05907v3, Theorem 2.1, §5.1); Leake and Morales, Adv. Appl.
  Math. 175 (2026) 103002 (context); DLMF §23.18. Added by the write:
  O'Neill, Electron. J. Combin. 25(2) (2018) #P2.4; Mészáros, Morales and
  Rhoades, Selecta Math. 23 (2017) 425–454; Armstrong, Garsia, Haglund,
  Rhoades and Sagan, J. Comb. 3 (2012) 451–494; Haglund, Adv. Math. 227
  (2011) 2092–2106.
- Repository input: none; the package names no ProveIt commit or path.
- Batch 103 of `docs/incoming`, bundle Report 106; arrival `60f54ea06`,
  placement `9c995cefe`, written 5 October 2026. Single source, so the write
  made no merge choices.
