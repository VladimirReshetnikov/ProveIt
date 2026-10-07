# Diagonal Multiple Alignments: All Fixed Orders, Column Counts and Inverse Thresholds (OEIS A262810, A262809, A316677, A316674)

**For the number `a_n` of binary matrices with `n` labelled rows, every row
sum `n`, ordered nonzero columns (A262810): `log(a_n/K_n) = Σ_{j≤J} C_j n^{-2j}
+ O(n^{-2J-2})` for every `J`, with Kotěšovec's equivalent `K_n` and explicit
`C_1, C_2, C_3`; a uniform `C^r` expansion in the column mark with only powers
of `n^{-2}`; the column count has mean `n²/(2 log 2) + n/4 + …` and a Gaussian
limit on scale `n`; substituting `k = n` in the classical fixed-`k`
equivalent misses a factor `e^{-1/12}`; a Lambert-`W` inverse and a two-ceiling
threshold enclosure; the nonnegative analogue A316677 by a binomial
coupling.**

A research article dated 3 October 2026 ("Report 177" of a session bundle),
built from one manuscript. Its author line reads "Report 177 OEIS A262810"
and its PDF title and author fields are empty: it names no person, tool or
addressee. The package carries no "prepared for private review" line, no
e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 177 (batch 109) | `Diagonal_Sequence_Alignments_Asymptotics_and_Inverses_Source.zip` (21 files, no wrapper directory, 1,120,000 bytes, SHA-256 `ce7560445477…ecbecaf8cef9b4e`), arrival commit `60f54ea06`; main file `report.tex` (572 lines, 14 pp.) | none: the package names no ProveIt commit and no repository path | `f7e9e5c2f` (batch 109) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Theorem 1.1 (uniform marked expansion),
  Corollary 1.2, Theorem 1.3 (column count), Proposition 7.1 (the
  fixed-dimension substitution), Theorems 8.1–8.2 (inverse expansion and
  enclosure) and the coupling of Section 9: the positive binomial-power
  representation, Euler–Maclaurin with a vanishing boundary (Lemma 4.1),
  gamma moment expansions after centring the roots, Stirling's series, the
  real mgf limit theorem, implicit differentiation and Lagrange inversion.
- **What rests on computation.** The explicit `L_1, L_2, L_3` and
  `C_1, C_2, C_3` are outputs of the finite rational algorithm of Section 5,
  checked by the shipped verifier (exact `Fraction` arithmetic; through order
  5 in the extension run) and rederived numerically by the write.
- **What is diagnostic.** Nothing in the article is a floating-point table;
  the write's numerical checks are observations.
- **What is prior.** Kotěšovec's leading equivalent (OEIS, 2016); the exact
  family, positive sum and fixed-dimensional asymptotic (Griggs–Hanlon–
  Odlyzko–Waterman 1990, Pemantle–Wilson 2008, Eger 2015); the unmarked
  relation `Ã_n(1) = 2^{n−1} a_n` (OEIS A316674, A316677; Eger Section 5.6,
  citing Duchi–Sulanke 2004).

## What it proves

`λ(u) = log(1 + 1/u)`, `λ = log 2` at `u = 1`, `N = n²`; `𝓑_n(u)` is the gamma
carrier (1). Equation and statement numbers are the delivered ones (the
article numbers equations consecutively).

- **Theorem 1.1 (`dma:thm:main`)**: `‖log(A_n(u)/𝓑_n(u)) − Σ_{j≤J}
  L_j(λ(u))/N^j‖_{C^r(U)} = O(N^{−J−1})` (2), `L_1 = z⁴/2880`,
  `L_2 = z⁴(693 − z²)/181440`, `L_3 = z⁴(3z⁴ + 3200z² + 493920)/29030400`
  (3)–(5).
- **Corollary 1.2 (`dma:cor:C`)**: `log(a_n/K_n) = Σ C_j n^{−2j}`, with
  `K_n` Kotěšovec's equivalent (6) and `C_1 = (λ⁴ + 248)/2880`,
  `C_2 = −(λ⁶ − 693λ⁴ + 144)/181440`,
  `C_3 = (3λ⁸ + 3200λ⁶ + 493920λ⁴ − 63360)/29030400` (7)–(9).
- **Theorem 1.3 (`dma:thm:law`)**: mean and variance of the column count to
  `O(n^{−4})` (10)–(11) and `(𝖫_n − n²/(2λ) − n/4)/n ⇒ 𝒩(0, σ²)`,
  `σ² = (1 − λ)/(4λ²)` (12).
- Section 2: the generating function (13), the positive representation (14),
  inclusion–exclusion (15), the binomial basis (16), the grid recursion (17),
  rational tail enclosures (18). Section 3: centred roots and `B_r(N)`
  (19)–(20). Section 4: Lemma 4.1 and the gamma expectation. Section 5: the
  algorithm and the Stirling relation. Section 6: the cumulant generating
  function and the auxiliary-`𝖬` identities.
- **Proposition 7.1 (`dma:prop:fixed`)**: `log(a_n/G(n,n)) = −1/12 +
  (31/360 + λ²/24)/n² + O(n^{−4})` for the fixed-`k` equivalent `G(n,k)`
  (38).
- **Theorems 8.1–8.2 (`dma:thm:inverse`, `dma:thm:ceiling`)**: the Lambert
  start `x_0 = √(2T/W(2T/λ²))`, the expansion of the root `x_J` of the
  surrogate `F_J(x) = T` to any order, and
  `⌈x − δ_J(x)⌉ ≤ ν(T) ≤ ⌈x + δ_J(x)⌉`, `δ_J = C_J x^{−2J−3}/log x` (43), for
  `ν(T) = min{n : a_n ≥ e^T}`; `a_n` strictly increasing by an explicit
  injection.
- Section 9: `Ã_n(u) = ((1+u)/u)^{n−1} A_n(u)` and the coupling
  `L̃_n = L_n − (n − 1) + Bin(n − 1, 1/2)`.

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.4 (`dma:rem:oeis`)**: the OEIS entries quoted and the b-files
  compared (next section).
- **Remark 8.3 (`dma:rem:transseries`)**: the inversions against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: `ν(T)` is the staircase `N_*`
  of `p0:def:three-inverses` (`A_n = log a_n`, `n_1 = 1`), so
  `p0:thm:staircase`(1) applies. (b) Theorem 8.2 is, **as stated and proved,
  an analogue** of `p0:thm:staircase`(2) (a direct bracket about the root of
  a surrogate); the write adds a **second route** through
  `p0:thm:staircase`(1) with the interpolation `F_J + r̃`, and, by part (3),
  `n = ⌊x_J(log a_n) + 1/2⌋` for large `n`. (c) **Instance after `X = x²`**:
  the Lambert start is `p0:prop:factorial-core` with `κ = 1/2`,
  `d = −log λ`; its large-`T` expansion is a **formal**
  `plt:thm:lw-template` instance with data `(2, 1, 0, log(1 − t log λ))` in
  the chart `Z_vol = log x`, `ξ_vol = log T`. (d) **Formal instance after
  `x = x_0(1+E)`**: the inverse expansion of Theorem 8.1 is
  `p0:thm:core-reversion` with `Λ_vol = 2 + 1/ℓ`, `ℓ = log(x_0/λ)`,
  `t_vol = 1/x_0`. (e) The full surrogate equation `F_J(x) = T` is **not
  shown to be an instance** of `plt:thm:lw-template` ((H3) fails in the chart
  of (c)); not claimed to be outside every chart.
- Section 1.1 (`dma:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions); notes after the abstract, at the ends of
  Sections 8 (inverse diagnostics) and 9 (priority of the unmarked
  relation), in Section 10 (the comparisons now made, the shipped layout) and
  at its end.

## The OEIS entries (Remark 1.4)

Read on 7 October 2026 in the internal format; quoted verbatim.

- **A262810** (revision #19, 12 July 2018), offset 0, by Alois P. Heinz:
  "Number of lattice paths from {n}^n to {0}^n using steps that decrement one
  or more components by one." (a path is a sequence of nonzero binary
  columns, so the definition is the source's); data `1, 1, 13, 16081,
  5552351121, …` (9 terms); "a(n) ~ n^(n^2 - n/2 + 1) / (exp(1/12) * 2^(n +
  log(2)/24) * Pi^((n-1)/2) * log(2)^(n^2+1)). - _Vaclav Kotesovec_, Mar 23
  2016", which is (6) exactly; b-file `n = 0..25` (Heinz).
- **A262809** (revision #59, 30 May 2026): the array; "Also, A(n,k) is the
  number of alignments for k sequences of length n each (Slowinski 1998).";
  "d(k) = (2^(1/k) - 1)^(-k). - _David Bevan_, Apr 07 2022" (the growth rate
  of (38)); "A(n,k) = Sum_{i >= 0} binomial(i,n)^k/2^(i+1). - _Peter Bala_,
  Jan 30 2018" ((14) at `u = 1`).
- **A316674** (revision #27): "A(n,k) = A262809(n,k) * A011782(n) for k>0,
  A(n,0) = 1."
- **A316677** (revision #8, 10 July 2018), which the source could not fetch:
  "a(n) = A262810(n) * ceiling(2^(n-1)) = A262810(n) * A011782(n)." — the
  diagonal relation of Section 9 is recorded there directly.

The write computed `a_n`, `n ≤ 25`, exactly by Howroyd's formula (a route
different from the source's difference table): all 26 terms of the A262810
b-file agree, `a` is strictly increasing from `n = 1`, and all 26 terms of
the A316677 b-file equal `2^{n−1} a_n`. Nothing was submitted to the OEIS.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- No global novelty: Kotěšovec's equivalent and the classical family,
  positive sum and fixed-dimensional asymptotic are credited; the unmarked
  relation is used "not as an independent discovery"; the source assessment
  is bounded, "not a theorem of global priority or an exhaustive literature
  search".
- No complex-parameter uniformity, local CLT or Berry–Esseen rate; no
  effective remainder constants or onsets; no exact universal single
  ceiling; no convergent infinite series; no exponentially improved counting.
- Proposition 7.1 is a nonuniformity example, "not an error in the fixed-`k`
  theorem"; Pemantle–Wilson's handbook corrections are unrelated.
- Exact rational finite checks establish finite identities and bounds, not
  the analytic theorem.

The write adds: its own checks are floating or finite; Remark 8.3 claims no
novelty for any inversion.

## Further questions

Section 10.3 of the article keeps the source's five questions (growth
regimes `k(n)` of the fixed-`k` formula and the crossover; a local CLT and a
rate; effective constants and onsets; large-order behaviour of `L_j`,
optimal truncation and exponentially small sectors; unequal growing row
sums). A dated note (Vladimir's standing rule of 4 October 2026) records
that no unproved claim of the source lies outside them and none is wrong.
**Nothing in the source was found to be wrong**; nothing was refuted or
moved. Dated notes record that the b-file and A316677 comparisons the source
could not make are now made, and that the unmarked relation of Section 9 is
in Eger, Section 5.6, credited there to Duchi–Sulanke (2004; not read; whether
their argument also tracks the number of steps, giving the marked identity,
was not checked).

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 20/20. The
  dossier read the manuscript and found no error, checked `C_1` by hand and
  the injection, and, with its own inclusion–exclusion at `n = 8, 16, 24`,
  found `(log(a_n/K_n) − C_1/n² − C_2/n⁴ − C_3/n⁶) n⁸ = 0.01450, 0.01385,
  0.01374`, bounded mean and variance errors times `n⁴`, and
  `(log(a_n/G(n,n)) + 1/12) n²` approaching `0.10612999`. It reran the
  verifier on copies: orders 3 and 5 identical to `checks.json`,
  `checks.order5.json` after removing Windows CR bytes;
  `verify_manifest.py` passing; `check_reproducibility.py` failing on Windows
  (CRLF output compared with the frozen file).
- At the write (7 October 2026; same machine; Python 3.14.4, mpmath 1.3.0):
  every proof line by line (the list is in Section 1.1), with no mathematical
  error found; exact `a_n` to `n = 25` and the b-files (above);
  `(log(a_n/K_n) − C_1/n² − C_2/n⁴ − C_3/n⁶) n⁸ = 0.014181, 0.013880,
  0.013777, 0.013730` at `n = 10, 15, 20, 25`; the Stirling relation (33) for
  `C_1, C_2, C_3` to 64 digits; `(log(a_n/G(n,n)) + 1/12) n² = 0.1061302552,
  0.1061300175, 0.1061300038` at `n = 10, 20, 25` against
  `31/360 + λ²/24 = 0.1061299867…`; mean and variance errors times `n⁴`
  (`−0.00262, −0.00259, −0.00257` and `0.00698, 0.00689, 0.00684` at
  `n = 12, 16, 20`); `A(n,k)/G(n,k) = 0.99707, 0.99853` (`k = 2`; `n = 40, 80`)
  and `0.99461, 0.99730` (`k = 3`); at `T = log a_n`, `x_J(T) − n` for
  `J = 0..3` below `n^{−2J−3}/log n` at `n = 10, 20, 25`, and the first
  inverse correction about `0.33` (limit `1/4`, logarithmic rate). The
  verifier rerun from the shipped files (Route B below): both orders give the
  frozen results after removing CR bytes; `check_reproducibility.py` fails on
  Windows as at intake.
- Sources read by the write: the four OEIS entries and two b-files; Eger
  arXiv:1511.00622v2, Sections 5.5–5.6; the transseries volume. Not read:
  Griggs–Hanlon–Odlyzko–Waterman, Pemantle–Wilson, Duchi–Sulanke, Slowinski.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
8.3(a)–(b) applies is formalized generically as `Fabius.staircase_ceil` (and
part (3) as `Fabius.staircase_round`) in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about these sequences is.

**The transseries volume.** Remark 8.3: the threshold a staircase instance;
Theorem 8.2 an analogue of `p0:thm:staircase`(2) as proved and a consequence
of (1) with the write's interpolation; the Lambert start a
`p0:prop:factorial-core` instance after `X = x²`, its expansion a formal
`plt:thm:lw-template` instance; the inverse expansion a formal
`p0:thm:core-reversion` instance; the full surrogate equation not shown to
be a template instance.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a138178-symmetric-packed-matrices`, whose source's `SOURCES.md` read "177
(A262810 diagonal alignments)" and found a different model, already points
here (its Section 1.1 and README), so no reciprocal note is needed.
`a261781-matrix-compositions` (Part IV, packed matrices) and
`a138178-symmetric-packed-matrices` count other matrix classes; no result is
shared.

**Stale claims.** Before batch 109 no file of the repository named A262809,
A316674 or A316677, and A262810 was named only in
`a138178-symmetric-packed-matrices`. The source audit's "no A262810/A262809
alignment entry" in the public catalogue was true on 3 October 2026.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `λ`, `λ(u)`, `λ(t)`; `ρ`; `h`, `H_q`,
`H_J`, `H_0`; `q`; `B_r(N)`, Bernoulli `B_s(x)`, `B_{2s}`; `K_n`, `K`, `C_j`,
`C_J`; `L_j`, `𝖫_n`; `N`, `𝒩`; `a`, `a_n`, `a_j`; `r_m`, `r`, `R_j`, `R`;
`t`, `t_m`, `T`; `𝖬`, `M`; `F(v)`, `F_0`, `F_J`, `G_N`, `G(n,k)`; `p`,
`p_n(m)`; `μ_r`, `κ_r`; `ν(T)`, `D`, `W`. No symbol was renamed; the volume's
colliding letters carry the subscript "vol" in Remark 8.3.

## Labels

Every label carries the prefix `dma:` (none existed in the repository). The
manuscript's 61 labels (`eq:` 45, `sec:` 9, `thm:` 4, `cor:` 1, `lem:` 1,
`prop:` 1) were prefixed before anything cited them, and the 45 references
to them (36 `\eqref`, 9 `\ref`) updated. The write added 3: `dma:rem:oeis`,
`dma:sec:provenance`, `dma:rem:transseries`. The report has 64 labels;
builds of the delivered text and of this one give all 61 delivered labels
the same numbers (aux files compared). The added statements are the last of
their sections, the added subsection follows the last delivered text of
Section 1, and nothing was inserted before a delivered display or statement.

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report (delivered report.tex; labels prefixed, [write] additions)
article.pdf                        compiled report, 19 pages
README_CODE.md                     the verifier's documentation (delivered at the root)
source_audit.md                    the source's attribution audit (delivered at the root)
code/verify_report177.py           exact rational verifier (delivered at the root)
code/check_reproducibility.py      standalone replay against the frozen results (same)
code/verify_manifest.py            release-inventory check (same)
code/build.py                      isolated PDF and ZIP builder, TeX (same)
code/test_build.py                 build and manifest rejection tests (same)
data/checks.json                   frozen verifier output, order 3 (same)
data/checks.order5.json            frozen verifier output, order 5 (same)
data/guards.json                   frozen negative-input tests (same)
data/reproducibility.json          frozen replay receipt (same)
data/BIBLIOGRAPHY.json             primary-source URLs and hashes of the inspected PDFs (same)
data/generated-BUILD_INFO.json     build receipt (delivered generated/)
data/generated-build_guards.json   build-test receipt (delivered generated/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report177.pdf` (the delivered 14-page PDF, 426,570 bytes);
`SHA256SUMS.json` (1,846 bytes, 20 entries, verified at placement; repository
policy ships no checksum manifests); `generated/verification.json`,
`generated/verification_guards.json` and `generated/reproducibility.json`,
byte copies of `data/checks.order5.json`, `data/guards.json` and
`data/reproducibility.json`; and the delivery `README.md` (5,715 bytes),
staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.** The
delivery README calls `report.tex` "byte-identical to the separately
delivered `Report177.tex`", which is not in the archive (the shipped
`article.tex` before the write was that `report.tex`); `README_CODE.md` gives
commands for the delivered root layout (`verify_report177.py`, `checks.json`,
…); `code/build.py`, `code/test_build.py` and `code/verify_manifest.py` expect
`report.tex`, `README.md`, `Report177.pdf`, `generated/` and
`SHA256SUMS.json` at the package root; `code/check_reproducibility.py`
compares with `checks.json` beside it; `source_audit.md` and
`data/BIBLIOGRAPHY.json` describe the primary PDFs, which are not shipped
(they were never in the package); Section 10.2 of the article describes the
delivered package. So no program runs under the shipped names; use one of the
routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Diagonal_Sequence_Alignments_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # ce75604454776132a218c40bbafa3a9344211cb5a1ea023deecbecaf8cef9b4e, 1,120,000 bytes
cd "$T" && unzip -q a.zip
```

## Rerun the checks (on a scratch copy)

Python 3.9 or later, standard library only. Never run anything in the
repository. Each `--output` must be a new file.

**Route A, delivered layout**, from `$T`:

```sh
python3 -E -B verify_report177.py --output NEW-checks.json
python3 -E -B verify_report177.py --order 5 --output NEW-checks5.json
python3 -E -B check_reproducibility.py --output NEW-repro.json   # POSIX (compares LF output)
python3 -E -B verify_manifest.py
python3 -E -B test_build.py                                      # POSIX
python3 -E -B build.py --output /new/dir/normal                  # TeX, POSIX
```

**Route B, from the shipped files** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a262810-diagonal-alignments
B=$(mktemp -d); mkdir -p "$B/generated"; cd "$B"
cp "$R"/code/*.py .; cp "$R"/data/checks.json "$R"/data/checks.order5.json "$R"/data/guards.json "$R"/data/reproducibility.json "$R"/data/BIBLIOGRAPHY.json .
cp "$R/data/generated-BUILD_INFO.json" generated/BUILD_INFO.json; cp "$R/data/generated-build_guards.json" generated/build_guards.json
cp checks.order5.json generated/verification.json; cp guards.json generated/verification_guards.json; cp reproducibility.json generated/reproducibility.json
cp "$R/README_CODE.md" "$R/source_audit.md" .; cp "$R/article.tex" report.tex
```

then the verifier commands of Route A. At the write, in this layout, both
orders reproduced `checks.json` and `checks.order5.json` byte for byte after
removing the CR bytes Windows writes (about 1 s each);
`check_reproducibility.py` failed on Windows for that reason. The manifest,
build tests and build need the delivered `README.md`, `Report177.pdf` and
`SHA256SUMS.json` (Route A). Use `py` where `python3` is not on the path.

## Build the PDF

pdfLaTeX (geometry, fontenc, lmodern, microtype, amsmath, amssymb, amsthm,
mathtools, booktabs, hyperref, enumitem, array); the bibliography is
embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026: 19
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 14 pages). The
write loads `array` for its notation table (a dated comment in the
preamble). The delivered byte-identity claims (fixed source date, suppressed
PDF metadata) apply to `Report177.tex` under the delivering toolchain, not to
this build.

## From the delivery README

The delivery README (replaced by this guide) said that "The report contains
the analytic proofs" and that "finite computation is not a proof of an
asymptotic remainder estimate"; listed the contents (including
`Report177.pdf`, `generated/` and `SHA256SUMS.json` "release archives only");
said that "No private research notes, downloaded primary PDFs, caches,
auxiliary TeX files, or unrelated source files belong to this package"; gave
the requirements and a fresh-replay recipe (manifest check, build tests in
normal and `-O` modes, two isolated builds compared byte for byte); listed
what every build checks (inventory, verifier through order 5 in both modes,
negative-input guards, replay, TeX warnings and boxes, manifest); and
described the isolation and determinism of the build, adding that
`SHA256SUMS.json` "is not a digital signature".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A262810, A262809, A316674 and A316677; OEIS content is published by
The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and
that content remains under that licence. Short quotations of the cited
papers are for attribution. No third-party PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A262810, A262809, A316674, A316677;
  Griggs–Hanlon–Odlyzko–Waterman, Graphs Combin. 6 (1990);
  Pemantle–Wilson, SIAM Rev. 50 (2008), Section 4.9; Eger, J. Autom. Lang.
  Comb. 20 (2015) and arXiv:1511.00622.
- Batch 109 of `docs/incoming`, bundle Report 177; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 7 October 2026. Single source, so no merge
  choices. The delivered `report.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
