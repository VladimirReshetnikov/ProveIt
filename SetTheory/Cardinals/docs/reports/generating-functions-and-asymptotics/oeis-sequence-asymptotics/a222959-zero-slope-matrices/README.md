# Binary Matrices with Zero Row and Column Slopes (OEIS A222959, A222955)

**`C_n = 2^{n²} e^{−7/5} √(2/π) (2/(π S_n))^{n−1} (1 + 171/(350n) +
483051/(245000n²) + O(n^{−3}))`, an expansion to every fixed order with
rational parity-free coefficients, a self-contained global Fourier
localization, a parity law `C_{2m}/C_{2m−1} ~ 6e^{−3}/(π m³)` with odd first
thresholds, and parity-aware inverses; the count `C_10 = 615667968`, a proof
of the conjecture recorded in A222955 (already a theorem of Richomme), and
narrow arrays settled**

A research article ("Report194" of a session bundle), built from one
manuscript dated 4 October 2026. Its author line is the subtitle "A self
contained study of the square diagonal of OEIS A222959" and its PDF author
field reads "Research report": it names no person, tool or addressee. The
package carries no "prepared for private review" line, no e-mail address and
no personal data; its READMEs use generic `/tmp` example paths.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 194 (batch 108, manuscript 04 of cluster 108-MATR) | `A222959_Zero_Slope_Matrices_All_Orders_and_Inverses_Source.zip` (22 files at the archive root, no wrapper directory, 798,678 bytes, SHA-256 `87c6a152…a446a10`), arrival commit `60f54ea06`; main file `Report194.tex` (1613 lines, 27 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes these matrices. No proof uses a computation.

## Trust boundaries

- **What is proved by hand, self-contained.** Everything in the main
  theorems: the margin and rectangular phase lattices, Haar normalization,
  the dense arithmetic-progression inverse lemmas, the robust core and the
  defect estimate (Theorem 1.2), the dimension-free Gaussian moment bound,
  the finite Taylor/Wick reduction to every fixed order (Theorem 1.1), the
  connected power count, the parity ratio and odd thresholds (Corollary 1.3)
  and the odd-integer envelopes. The literature of Section 13 is credited as
  method precedent and is not used as input.
- **What a computation produced.** `c_1 = 171/350` is computed by hand. `c_2`
  uses only the leading terms of the contractions `K` and `T`, which the
  source also obtains by summing the per-graph entries of its table in
  Section 10; the complete polynomials (56)–(57) come from the package's
  symbolic contraction computation (rechecked by an independent raw-moment
  recursion for `n = 2, …, 5`, and by replay at intake). The write
  recomputed every entry of the coefficient table of Section 10 from the
  displayed exact formulas (SymPy).
- **The finite counts** `C_1, …, C_10` are exact computations used by no
  proof. The localization constants (`δ = 10^{−10}`, …) give only an
  existential threshold.

## What it proves

`C_n` counts `n × n` binary matrices `M` with `Mw = Mᵀw = 0`, where
`w_j = j − (n+1)/2` (odd `n`) or `2j − n − 1` (even `n`), equivalently zero
least-squares slope in every row and column; `C_1 = 2` by the OEIS
convention; `S_n = n(n²−1)/12` (odd) or `n(n²−1)/3` (even); `G_n =
√(2/π)(2/(π S_n))^{n−1}`. Statement numbers are the delivered ones.

- **Theorem 1.1 (`zsm:thm:main`)**: `C_n = 2^{n²} G_n e^{−7/5}(Σ_{j≤J} c_j
  n^{−j} + O_J(n^{−J−1}))` for every fixed `J`, with rational `c_j`
  independent of parity, given by the finite prescription (`zsm:eq:cj`);
  `c_0 = 1`, `c_1 = 171/350`, `c_2 = 483051/245000`; no convergence claimed.
- **Theorem 1.2 (`zsm:thm:globalintro`)**: relative global localization:
  the Fourier integrand outside the central tube contributes `O(G_n e^{−cn})`.
- **Corollary 1.3 (`zsm:cor:thresholdintro`)**: `C_{2m}/C_{2m−1} ~
  6e^{−3}/(π m³)`; each parity subsequence is eventually strictly
  increasing, the whole sequence is not; for large `Y` the first index with
  `C_n ≥ Y` is odd; odd-integer envelopes (`zsm:eq:oddenvelope`).
- **Lemmas 2.1, 4.1–4.2, 5.1–5.2, 7.1, 10.1**: rectangular phase lattice,
  scalar and dense-circuit inverses, robust core, Gaussian cost per defect,
  fixed-degree Gaussian moments, connected power count.
- Section 10 also gives `log(e^{7/5} C_n/(2^{n²} G_n)) = 171/(350n) +
  6483/(3500n²) + O(n^{−3})`; Section 11 the logarithmic phase with `r_1 =
  521/350`, `r_2 = 2983/3500`, and the smooth inverse through its `X^{−1}`
  term; Section 12 the exact meet-in-the-middle formula (`zsm:eq:MITM`) and
  the palindromic bound `C_n ≥ 2^{⌈n/2⌉²}`.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 11.1 (`zsm:rem:transseries`)**: Section 11 against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  (a) The smooth inverse is a **formal instance** of `p0:thm:core-reversion`
  after the change of variable `x = X(1+E_vol)`, `t_vol = 1/X`, over
  `R = ℝ[ℓ_X]` (`ℓ_X = log X` an indeterminate), with `Λ_vol = 2 log 2`,
  `h_vol(u) = log 2 · u²` and an explicit `f_vol`; its first two
  coefficients are the source's `u` and `v`. The core `A_0X²` is admissible
  (`p0:def:core`) but is neither Lambert core, so the formula is **not** an
  instance of `p0:thm:lambert-core`, `p0:prop:factorial-core`,
  `p0:thm:lambert-centered` or `p0:thm:flattening`. After
  `G = √(M/A_0)` it is also a formal instance of `plt:thm:lw-template`
  (data `(1, −3/(2A_0), D_d/(2A_0), B)`, the route of
  `a089479-fixed-permanent-matrices`); the write first said it was an
  instance "of no Lambert theorem of the volume", corrected after the
  independent check below. The analytic error
  bound is the source's, not the volume's. (b) Corollary 1.3 and the odd
  envelopes are **analogues, not instances**, of `p0:thm:staircase`:
  `p0:def:three-inverses` presupposes a sequence increasing from some index
  on, which `(C_n)` is not; part (4) holds for `C_n` by its own proof, which
  uses only classwise monotonicity, but is stated under the violated
  hypothesis; the envelopes are the analogue of part (2). (c) For large `Y`,
  `N(Y)` jumps by 2 between consecutive odd indices, so every continuous `g`
  has `sup |N − g| ≥ 1`: the precise form of the source's "no uniform single
  rounded smooth formula".
- **Remark 12.1 (`zsm:rem:oeisdata`)**: the OEIS records quoted and
  checked, and `C_10 = 615667968` (next section).
- **Remark 13.1 (`zsm:rem:wiseman`)**: the conjecture recorded in A222955 is
  a theorem of Richomme, with a two-line second proof (section after next).
- **Proposition 14.1 (`zsm:prop:narrow`)**: with `T(n,k)` the A222959 array
  (`n` rows of length `k`), `T(n,k) ≥ b_n^{⌈k/2⌉}` for all `n, k ≥ 1`
  (row-palindromic arrays), with equality for every `n` exactly when
  `k ≤ 6`; hence `C_n ≥ b_n^{⌈n/2⌉} ≥ 2^{⌈n/2⌉²}`, a sharper form of the
  palindromic bound (at `n = 8` and `n = 10` the row-palindromic sector holds
  72% and 41% of `C_n`), still negligible as `n → ∞`. This explains the equal
  column pairs of the displayed OEIS array.
- Section 1.1 (`zsm:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), notes at Sections 12, 13 and 14,
  Questions 8–9 in Section 14 (`zsm:q:smoothinverse`, `zsm:q:narrow`), and
  one bibliography entry (the OEIS b-files).

## The OEIS records, and `C_10`

A222959 (revision #8, 3 October 2025, read 6 October 2026) is named,
verbatim,

    T(n,k)=Number of nXk 0..1 arrays with every row and column least squares fitting to a zero slope straight line, with a single point array taken as having zero slope.

Its 68 data terms list the array by antidiagonals and reach the diagonal
only through `T(6,6) = 512` (the `8000` there, twice, is
`T(5,7) = T(7,5)`, not a diagonal term; the write first named only
`T(5,7)`); the comment "Table starts" displays the diagonal through
`T(9,9) = 1808243216`, the source's values. The entry links R. H. Hardin's
b-file of 199 terms, which the source could not retrieve (HTTP 403); the
write could, and its index 181 gives

    C_10 = T(10,10) = 615667968,

which a meet-in-the-middle program written for the write (not shipped)
reproduces (`b_10 = 48`, `48^5 = 254,803,968` positive-row tuples), along
with every `C_n`, `2 ≤ n ≤ 9`. At `n = 10` the ratio to the main term is
6670.0 (6241.9 after dividing by `1 + c_1/n + c_2/n²`); the source's 21.15,
3558.9, 23.66 at `n = 7, 8, 9` were recomputed. A222955 is the first column
(`b_n`); its data and b-file agree with the source's alphabet sizes for
`n ≤ 14`. Recorded only: **nothing was submitted to the OEIS.**

## The A222955 conjecture is a theorem

A222955 (revision #24, 17 March 2026) still carries, verbatim,

    Conjecture: A binary word is counted iff it has the same sum of positions of 1's as its reverse, or, equivalently, the same sum of partial sums as its reverse. - _Gus Wiseman_, Jan 07 2023

Richomme (arXiv:2510.07159v1, Theorems 5.13 and 5.14, read by the write)
proved its first form, the second being equivalent by the partial-sum
identity below (the write first said "proved it"): zero-slope words are his fair words, and fairness is the
position-sum condition; his introduction says so. The write's direct proof
(Remark 13.1): with `P(v) = Σ j v_j`, the reverse has `P(v^R) = (n+1)|v| −
P(v)`, the slope numerator is `P(v) − (n+1)|v|/2`, and the sum of the
partial sums of `v` is `P(v^R)`; `n = 1` holds by convention. Recorded only:
**nothing was submitted to the OEIS.**

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.1):

- Every fixed order only: no convergence, Borel summability, optimal
  truncation or uniformity in a growing order; `c_j`, `j ≥ 3`, not computed;
  the package is not an all-orders Wick engine.
- No practical onset or numerical error bound; the small constants give only
  an eventual threshold ("not a usable numerical error estimate"); the small
  counts are strongly preasymptotic and validate nothing.
- The integer envelopes leave rounding ambiguities near threshold
  coincidences; no uniform rounded smooth formula; no interpolation inherits
  the smooth `X^{−1}` coefficient.
- No absolute priority: a focused literature search, "not a certificate of
  originality"; the Barvinok–Hartigan obstruction concerns the natural
  coordinates only; Arratia–DeSalvo are "conceptual predecessors".
- Finite checks corroborate algebra and implementation only; no formal
  verification; PDF byte identity only for a fixed TeX toolchain; the
  integrity manifests are not signatures.

The write adds: Remark 13.1 rests on its own two-line proof and on
Richomme's text as read; `C_10` is a computation reproducing the b-file and
is used by no proof; Remark 11.1's instance is formal only.

## Further questions

Section 14 of the article (`zsm:sec:limits`) is the report's further-questions
section (Vladimir's standing rule of 4 October 2026). **Nothing in the
source was found to be wrong.** The source's seven items stay as delivered
(practical onset; higher coefficients; optimal truncation; other weights and
rectangular limits; the small-dimension structure; integer inverse
boundaries; literature and formalization), with a dated note: item 5 is
advanced by Proposition 14.1 and item 1 by `C_10`. Added:

8. **Higher terms of the smooth inverse** (`zsm:q:smoothinverse`): the
   source's one-sentence claim that every fixed truncation is justified by
   the finite-order remainders; the formal coefficients are now those of the
   `p0:thm:core-reversion` instance; the written estimate is missing.
9. **Fixed width** (`zsm:q:narrow`, added by the write): asymptotics of
   `T(n,k)` for fixed `k ≥ 7`; only the strict lower bound
   `b_n^{⌈k/2⌉}` is known here.

The package's statement that a C++ program checked all nine counts is not
checkable (the program is not shipped) and is superseded by the
reproductions below.

## Checks made at intake

- At placement (batch-108 dossier 108-MATR, 6 October 2026; Windows, Python
  3.14.4): the staged files are byte-identical to the archive;
  `SHA256SUMS.json` 21/21; `code/PROVENANCE.json` 5/5. The dossier read the
  manuscript in full, found no error, and rechecked by hand `r_1`, `r_2`, the
  parity and two-step ratios, the smooth inverse, the palindromic bound at
  `n = 7, 8, 9` and the energy/defect arithmetic; its own program gave
  `C_1, …, C_8`. On a copy: `reproduce.py` PASS (normal and `-O`
  byte-identical, equal to the delivered receipt), `test_build.py` PASS,
  `check_exact.py --max-n9` PASS.
- At the write (6 October 2026; same machine): the OEIS entries and both
  b-files fetched (above); Richomme's v1 HTML read; the coefficient table of
  Section 10 recomputed from the exact formulas; `C_2, …, C_10` counted
  independently; and the package rerun from a fresh extraction of the
  archive (route A below): `verify_manifest.py` PASS (21 files),
  `reproduce.py` PASS in 12 s with both receipts byte-identical to the
  delivered `generated/exact_checks.json`, `test_build.py` PASS with 321
  tests (84 acceptance, 237 rejection; the delivered record has 326, and the
  five missing are named-pipe and double-slash-path rejections that run only
  where `os.mkfifo` exists or `os.name == 'posix'`), and `--max-n9`
  reproducing `C_9 = 1808243216` in 10 s. Route B was also run.
- **Independent check of the write (6 October 2026).** An adversarial check
  made by the intake after the write (`3e9c7ae10`), with its own code, after
  fetching both entries, both b-files and Richomme's v1 again. Proposition
  14.1: proof re-read; a general `n × k` counter of its own gave 119 cells
  (all `n, k ≤ 10`, `n = 11` with `k ≤ 10`, `n ≤ 9` with `k = 11`), each
  satisfying (1)–(2), the array symmetric where computed both ways, and the
  118 cells within the b-file in agreement; the shares 72% and 41%
  recomputed. `C_10 = 615667968` reproduced by that program (a partition
  different from the write's), `C_1, …, C_9` likewise; the ratios at
  `n = 7, …, 10` at 30 digits; `r_1 = 521/350`, `r_2 = 2983/3500`.
  `C_{2m}/C_{2m−1} = 1, 1, 1, 0.4479, 0.3405` (`m = 1, …, 5`) and both
  parity classes strictly increasing: the sign pattern of Remark 11.1(b),
  far from the asymptotic ratio. Remark 13.1 checked against Richomme's
  text. One statement too strong: Remark 11.1(a)'s "and of no Lambert
  theorem of the volume" (after `G = √(M/A_0)` the smooth inverse is a
  formal instance of `plt:thm:lw-template`, its solution reproducing `u`,
  `v` by SymPy); corrected with a dated note keeping the first wording.
  Made precise, also with dated notes: Remark 12.1 names both cells of the
  value 8000 (indices 60 and 62), and Remark 13.1 says that Richomme proved
  the first form. The check is recorded at the end of Section 12.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns these matrices or fair words.
Placement in the collection confers no formal status.

**The transseries volume.** Remark 11.1: the smooth inverse is a formal
instance of `p0:thm:core-reversion` (after a change of variable) and,
after `G = √(M/A_0)`, of `plt:thm:lw-template`; the threshold statements
analogues of `p0:thm:staircase`. No novelty is claimed
for the inversions.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a380592-tied-football-seasons` (A380592) is the nearest in method: a
growing-dimensional Fourier count with its own global localization, every
fixed order and residue-class inverse thresholds. Its all-orders step imports
Isaev's complex cumulant theorem; this report's uses the one-sided bound
`Z_K ≥ −m(n)` and a finite Taylor expansion instead, and imports no cumulant
theorem. Neither uses the other; a reciprocal note for a380592 is proposed
separately. `a005163-diagonally-symmetric-asms` is unrelated despite the
matrix setting.

**Stale claims.** Before batch 108 no file of the repository named A222959 or
A222955; the source made no claim about the repository.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `C_n` and `T_959(n,k)` against the
retained column set `C`, the constants `C_G, C_{d,p}, C_K` and the colour C;
`b_n, V_n` against `V = E D²` and the projection `V`; `E, 𝔼, ℰ, E_d`; `d_0,
d, D, D_d`; `c, c_0, c_1, c_j` (`c_1` is both the coefficient `171/350` and
a Gaussian tail constant in (30)); the leverages `h_{ij}` and the several
`H`; the section-local `K, F, T, L`; `κ` (a constant and joint cumulants);
`N(Y), X, x_±` against the volume's `N_*`; `u, v, ℓ_i` and the write's
`ℓ_X = log X`. Symbols of the transseries volume that collide (`h, E, t, f,
Λ, κ, d`) carry the subscript "vol" in Remark 11.1. No symbol was renamed.

## Labels

Every label carries the prefix `zsm:` (none existed in the repository). The
manuscript's 94 labels (`eq:` 69, `sec:` 15, `lem:` 7, `thm:` 2, `cor:` 1)
were prefixed before anything cited them, and the 83 references to them
updated. The write added 7: `zsm:sec:provenance`, `zsm:rem:transseries`,
`zsm:rem:oeisdata`, `zsm:rem:wiseman`, `zsm:prop:narrow`, and the questions
`zsm:q:smoothinverse`, `zsm:q:narrow`. The report has 101 labels; builds of
the delivered text and of this one give all 94 delivered labels the same
numbers (aux files compared). The added statements are the last numbered
ones of their sections, the added subsection follows the last delivered text
of Section 1, the added questions continue the delivered list as items 8–9,
and the added displays are unnumbered.

## Files

```text
README.md                            this guide (replaces the delivery README)
article.tex                          the report (delivered Report194.tex; labels prefixed, [write] additions)
article.pdf                          compiled report, 35 pages
DATA_SOURCES.md                      primary sources, data provenance and scope (delivered at the root)
README_REPRODUCIBILITY.md            commands, dependencies, inventory, trust boundary (delivered at the root)
code-README.md                       the code README (delivered code/README.md)
data-README.md                       the data README (delivered data/README.md)
code/matrix_exact.py                 exact projector, lattice, alphabet and enumeration routines (delivered code/)
code/check_exact.py                  exact replay driver; --max-n9 option (delivered code/)
code/derive_second_correction.py     connected-Wick contraction polynomials for c2 (delivered code/)
code/verify_second_correction.py     independent raw-moment check of them, n = 2..5 (delivered code/)
code/reproduce.py                    normal and -O isolated replay with byte comparison (delivered at the root)
code/build.py                        deterministic PDF/ZIP release builder (delivered at the root)
code/verify_manifest.py              closed-inventory manifest checker (delivered at the root)
code/test_build.py                   guard and builder tests (delivered at the root)
data/PROVENANCE.json                 sizes and SHA-256 of the mathematical modules and data (delivered code/PROVENANCE.json)
data/reference.json                  C_n for n <= 9 and alphabet sizes/ranks for n <= 14 (delivered data/)
data/generated-exact_checks.json     the exact replay receipt (delivered generated/exact_checks.json)
data/generated-verification.json     replay summary with the receipt's SHA-256 (delivered generated/verification.json)
data/generated-build_guards.json     guard-test summary, 326 tests (delivered generated/build_guards.json)
data/generated-BUILD_INFO.json       build metadata (delivered generated/BUILD_INFO.json)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report194.pdf` (the delivered 27-page PDF, 570,054 bytes); `SHA256SUMS.json`
(3,044 bytes, 21 entries, verified at placement; repository policy ships no
checksum manifests); the delivery `README.md` (3,257 bytes), staged at
placement and replaced by this guide (summarized below); and the C++
meet-in-the-middle program that `DATA_SOURCES.md`, `data-README.md` and
`data/reference.json` say produced the recorded `n = 9` count, which was not
in the delivered package either.

**Delivered text that names the delivery layout or files not shipped.**
`DATA_SOURCES.md`, `data-README.md` and `data/reference.json` cite the C++
count (not delivered); `data-README.md` says its bytes are pinned by
`code/check_exact.py` (still true) and points to `DATA_SOURCES.md`;
`README_REPRODUCIBILITY.md` and the delivered README give commands at the
delivered names (`reproduce.py`, `build.py`, `verify_manifest.py`,
`test_build.py` at the package root, `generated/`, `Report194.tex`,
`SHA256SUMS.json`); `code/build.py` pins `code/PROVENANCE.json` (shipped as
`data/PROVENANCE.json`) and compiles `Report194.tex`; `code/verify_manifest.py`
checks the closed delivered inventory; Section 12 of the article speaks of
"the accompanying source archive" and its manifest. The release tools also
expect POSIX semantics for some guards (named pipes, path aliases).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A222959_Zero_Slope_Matrices_All_Orders_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 87c6a152db72c05a395b78e173a3ad207c30e07206c0de9b98bf6ae41a446a10, 798,678 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # the 22 files are at the archive root
```

## Rerun the checks (on a scratch copy)

Python 3.11 or later, standard library only. Never run anything in the
repository; every output path must be new and outside the package.

**Route A, delivered layout** (as the delivery READMEs give it; run at the
write on Windows, except the `-O` guard suite and the PDF build):

```sh
cd "$T/pkg"
python3 -B verify_manifest.py                                   # PASS, 21 files
python3 -B reproduce.py --output-dir "$T/replay"                # PASS; both receipts equal generated/exact_checks.json
python3 -B test_build.py                                        # PASS (321 tests on Windows, 326 on POSIX)
python3 -O -B test_build.py
python3 -I -S -B code/check_exact.py --max-n9 --output "$T/n9.json"   # C_9 = 1808243216, about 10 s
```

The release build (`python3 -B build.py --output "$T/release"`) needs pdfTeX
and was not run by the intake.

**Route B, from the shipped files, any OS** (tested at the write; 8 s):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a222959-zero-slope-matrices
B=$(mktemp -d); mkdir "$B/code" "$B/data"; cd "$B"
cp "$R"/code/*.py code/; cp "$R/data/reference.json" data/
python3 -I -S -B code/check_exact.py --output "$T/check.json"
cmp "$T/check.json" "$R/data/generated-exact_checks.json"      # identical
```

Use `py` where `python3` is not on the path; on Windows give absolute output
paths with forward slashes.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, microtype, hyperref, enumitem); the bibliography
is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, after
the independent check (34 pages at the write): 35 pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 27 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered reproducibility
claims apply to `Report194.tex` under the delivering toolchain, not to this
build.

## From the delivery README

The delivery README (replaced by this guide) summarized the theorem and the
proof's ingredients as above; said "The supplied code evaluates c0=1,
c1=171/350 and c2=483051/245000" and "No all-order Wick engine, practical
onset, convergence of the formal series, or absolute priority claim is
supplied"; listed the package contents; gave the replay, test and build
commands with Linux example paths under `/tmp` (with notes for macOS and
Windows paths, and that existing outputs, symlinked components and `.`/`..`
are rejected); said the mandatory replay recomputes counts through `n = 8`,
projector identities through `n = 12` and alphabets through `n = 14`, with
the `n = 9` count "recorded independent enumeration evidence … not a default
rerun"; and described the PDF/ZIP release builder.

## Rights

Repository contents are MIT-0. The article, `data/reference.json` and this
README quote OEIS terms and comments of A222959 and A222955; OEIS content is
published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE), and those terms remain under that licence. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A222959 and A222955; Prodinger,
  Discrete Math. 28 (1979) 269–276; Richomme, arXiv:2510.07159v1; Bera et
  al., J. Math. (2020) 3236405; Arratia–DeSalvo, arXiv:1105.2834v2;
  Barvinok–Hartigan, arXiv:0903.5223v2 and arXiv:0910.2497v2;
  Kuperberg–Lovett–Peled, arXiv:1302.4295v3; Harrison–Miller,
  arXiv:1301.3928v1; Aw, arXiv:2604.08857v1. Read by the write: the OEIS
  entries and b-files, Richomme's v1 HTML (Theorems 5.12–5.14). Not read by
  the write: the others (what the source inspected is in `DATA_SOURCES.md`).
- Batch 108 of `docs/incoming`, bundle Report 194; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report194.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
