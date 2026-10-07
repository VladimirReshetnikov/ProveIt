# Distinct Sums of Square Roots: Quantitative Asymptotics and Inverse Indices (OEIS A397045)

**`a(n)`, the number of distinct values in `[n, n+1)` of finite sums of
square roots of positive integers, equals `N(n+1)`, the number of vectors
`(m_d)` over the squarefree `d ≥ 2` with `Σ m_d √d < n+1`;
`log a(n) = K(n+1)^{2/3} + O(n^{1/3})` with `K = (81ζ(3)/π²)^{1/3}`, which
proves the OEIS conjecture; an exact-product saddle formula with relative
error `O(n^{-1/3})`, valid at atomic endpoints; inverse indices
`J(y) = (log y/K)^{3/2} + O(log y)` and `J(y) + 1 = X(y) + O(1)`; and,
unconditionally, no equivalent `C n^β exp(K n^{2/3})`, because of a surviving
pole at a zeta zero of least height.**

A research article dated 3 October 2026 ("Report 172" of a session bundle),
built from one manuscript. Its author line and PDF author field are empty
and its title block reads "Report 172": it names no person, tool or
addressee. The package carries no "prepared for private review" line, no
e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 172 (batch 109) | `Distinct_Square_Root_Sums_Asymptotics_and_Inverses_Source.zip` (23 files, no wrapper directory, 565,603 bytes, SHA-256 `0b71479e336a…cf0efbec3d08`), arrival commit `60f54ea06`; main file `Report172.tex` (869 lines, 20 pp.) | none: the package names no ProveIt commit and no repository path | `f7e9e5c2f` (batch 109) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Theorems 1.1–1.4 with complete conventional
  proofs: linear independence of square roots of squarefree integers (the
  exact identity), Möbius counting and Rankin–Chebyshev bounds (the
  logarithmic law, Section 4), a smoothing lemma for a signed comparator with
  a first Edgeworth term (the saddle formula, Sections 5–6), the inverse
  brackets (Section 7), and a Mellin argument at a zeta zero of least positive
  height (Section 8), which uses only standard facts about the zeros (their
  existence, none on the real segment of the critical strip) and neither RH
  nor simplicity. Appendix A gives a second, weaker Gaussian route. No proof
  uses a computation.
- **What rests on computation.** The exact values `a(n)`, `n ≤ 35`: a
  bounded enumeration with rational square-root enclosures that aborts on any
  ambiguous comparison (Python to `n = 20`, C++ to `n = 35`).
- **What is diagnostic.** The saddle table of Section 10 and every decimal:
  binary64, no interval arithmetic.
- **What is prior.** The leading law is a specialization of Kohlbecker 1958
  (Main Theorem and Corollary 1), and the qualitative saddle equivalent is
  Ingham's 1941 theorem (in the form of Bringmann–Jennings-Shaffer–Mahlburg,
  Theorem 4.1), as the source says; Dong–Robles–Zaharescu–Zeindler are
  conceptual prior art for zeta zeros in implicit saddles.

## What it proves

`𝒟` is the set of squarefree `d ≥ 2`; `c = 1/ζ(2)`, `A = 2ζ(3)/ζ(2)`,
`K = 3(A/4)^{1/3} = (81ζ(3)/π²)^{1/3} = 2.1447175229…` (1.1);
`F(t) = −Σ_{d∈𝒟} log(1 − e^{−t√d})`; `t(x)` solves `−F'(t) = x`. Statement
and equation numbers are the delivered ones.

- **Theorem 1.1 (`srs:thm:log`)**: `a(n) = N(n+1) = N_≤(n+1)` and
  `log a(n) = K(n+1)^{2/3} + O(n^{1/3})` (1.3); Section 2 (canonical vectors,
  the unit coefficient (2.2)) and Section 4 (Rankin bound (4.1),
  Proposition 4.1, two-sided finite bounds).
- **Theorem 1.2 (`srs:thm:saddle`)**:
  `N(x) = exp(F(t) + tx)/(t √(2π F''(t))) {1 + O(t)}`, `t ~ (2A/x)^{1/3}`,
  for `N` and `N_≤`, at atoms too (1.5); Lemma 3.1 (cumulants), Section 5
  (characteristic function up to a fixed frequency), Lemma 6.1 (smoothing
  with a signed comparator), Lemma 6.2 (first Edgeworth comparison, CDF error
  `O(t²)`).
- **Theorem 1.3 (`srs:thm:inverse`)**: for `J(y) = min{n ≥ 1 : a(n) ≥ y}`,
  `J(y) = (log y/K)^{3/2} + O(log y)` (1.6), and `J(y) + 1 = X(y) + O(1)`
  with `H(X) = log y` (1.7)–(1.8); asymptotic brackets, not rounding rules.
- **Theorem 1.4 (`srs:thm:obstruction`)**: no `C > 0`, `β ∈ ℝ` with
  `a(n) ~ C n^β exp(K n^{2/3})`; Lemma 8.1 (`srs:lem:pole`, a pole of exact
  order `m` of `Γ(s)ζ(s+1)(ζ(s/2)/ζ(s) − 1)` at a least-height zero) and
  Corollary 8.2 (`srs:cor:finiteexpansion`: no finite real power–logarithm
  expansion of `F` with bounded remainder).
- Section 9: the bridge to Ingham's theorem (the radial bound (9.3)) and
  Kohlbecker's specialization; Section 10: the exact computation (Table 1),
  the truncation tail bound (10.2) and the diagnostics (Table 2);
  Appendix A: the Gaussian route, relative error `O(t log(1/t))`.

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.5 (`srs:rem:oeis`)**: the OEIS entry quoted (next section);
  the conjecture proved; Kohlbecker's specialization worked out; the b-file.
- **Remark 2.1 (`srs:rem:comment`)**: the entry's cumulative comment
  corrected (section after next), with the exact count (2.4) of the model it
  names and the strict increase of `a`.
- **Remark 7.1 (`srs:rem:transseries`)**: the inversions against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: `J(y)` is the staircase `N_*` of
  `p0:def:three-inverses` (`A_n = a(n)`, `n_1 = 1`), so
  `p0:thm:staircase`(1) gives `J = ⌈ν_𝒜⌉` for every admissible
  interpolation. (b) **Theorem 1.3 is not an instance**: both brackets are
  direct `O(log y)` and `O(1)` estimates, not two-ceiling brackets, and an
  `O(1)` error does not determine `J`; a **second route** to (1.8) through
  `p0:thm:staircase`(1), with the log-linear interpolation of `a`, recovers
  the same `O(1)`. (c) **A trivial formal instance**: the leading inverse
  `(log y/K)^{3/2}` is `plt:thm:lw-template` with data `(2/3, 0, log K, 0)`
  in the chart `Z_vol = log x`, `ξ_vol = log log y`; no Lambert function
  occurs, and neither `p0:thm:lambert-core` nor `p0:prop:factorial-core` is
  involved. (d) **Not shown to be an instance**: the implicit equation
  `H(X) = log y` (Corollary 8.2 is why the source keeps `F` whole); not
  claimed to be outside every chart.
- Section 1.1 (`srs:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions); notes after the abstract, in Section 10
  (the full `n = 35` rerun, the diagnostics rechecked and extended, the
  shipped layout) and at the end of Section 11.

## The OEIS entry (Remark 1.5)

A397045, read on 6 October 2026 in the internal format (revision #27,
17 June 2026); quoted verbatim. Name: "Number of distinct values in the
interval [n,n+1) that can be represented as a sum of square roots of
positive integers.", offset 1, by Ali Sada (14 June 2026); 35 terms,
`3, 7, 17, 35, 76, …, 428363342`; formula line "Conjecture: log a(n) ~
k*n^(2/3). Possibly k = (81*zeta(3)/Pi^2)^(1/3) = 2.1447.... - _Charles R
Greathouse IV_, Jun 15 2026"; b-file "Table of n, a(n) for n = 1..75".

- **The conjecture is proved** by Theorem 1.1, law and constant, with error
  `O(n^{1/3})`. It was already implied by classical theory, as the source
  says: the write read Kohlbecker's Main Theorem and Corollary 1
  (pp. 362–363 of the publisher's PDF), which allow arbitrary positive real
  part sizes; with `n(u) = B(u) ~ c u²` they give
  `log P(u) ~ (3/2)(4cζ(3))^{1/3} u^{2/3} = K u^{2/3}`. The entry still
  states a conjecture; nothing was submitted to the OEIS.
- `K = 2.144717522977472648…`; the source's `2.1447175229…` is a correct
  truncation.
- **The b-file** (75 terms), retrieved by the write: its first 35 terms
  equal the data and the source's fixture, and it is strictly increasing.
  Terms 36–75 were not recomputed (the source had not retrieved the file).

## The entry's comment, corrected (Remark 2.1)

The entry's comment reads "Number of distinct values in the interval [0,n+1)
that can be represented as a sum of square roots of integers (or
equivalently, squarefree integers) k > 1. - _Charles R Greathouse IV_, Jun 15
2026". The equivalence is false; the source says so (Section 2, "The
alternate OEIS wording": 8 values instead of `a(2) = 7`, because `√4 = 2`),
and the write keeps it on record, under Vladimir's standing rule, with a
proof:

- With integer radicands `k > 1` and the empty sum, the count is
  `𝓘_n = a(n) + Σ_{i=0}^{n−2} a(i)` (`a(0) = 1`), because the unit
  coefficient can be any sum of integers `≥ 2` (from `√(b²)`, `b ≥ 2`):
  `𝓘_n = 3, 8, 21, 46, 104` against `a(n) = 3, 7, 17, 35, 76` (`n ≤ 5`; also
  counted by brute force). Without the empty sum it gives `2 ≠ a(1)`. So
  neither convention makes the integer reading equal to `a(n)`; squarefree
  (or nonsquare) radicands with the empty sum do, which is Theorem 1.1's
  identity.
- Also `a(n+1) − a(n)` is the number of nonunit sums in `[n+1, n+2)`, at
  least one for every `n ≥ 0` (the sums `i√2 + j√3` beyond `5√2`, and the
  data below), so `a` is strictly increasing.

The comment belongs to the OEIS entry, not to the source; nothing was
submitted to the OEIS.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- The leading law (Kohlbecker) and the qualitative exact-saddle equivalent
  (Ingham) are classical; no new general partition theorem and no exhaustive
  literature priority ("This is not an exhaustive novelty claim").
- Dong–Robles–Zaharescu–Zeindler are conceptual prior art for zeta zeros in
  implicit saddles, with a different spectrum.
- The inverse brackets are asymptotic: no numerical constant, finite
  threshold or exact rounding rule; a numerical root of `H(X) = log y` is not
  a guaranteed rounding instruction.
- The truncation tail bound controls omitted terms only; floating
  diagnostics are noncertified.
- Section 8 gives no pointwise formula over the zeta zeros, no RH-scale
  remainder and no transseries, and does not deny `F(t) ~ A/t²`.
- No exact data beyond `n = 35`; fresh default coverage only to `n = 20`.
  No OEIS submission, publication, author contact or repository edit.

The write adds: its checks are floating or finite; Remark 2.1 corrects a
comment of the OEIS entry, not the source; Remark 7.1 claims no novelty for
any inversion.

## Further questions

Section 11 of the article (`srs:sec:sources`) keeps the source's four
questions: a sharper relative error than `O(t)`, uniform at atoms; a
pointwise explicit formula for `F` over the zeta zeros; an effective inverse
with certified constants; faster exact counting with the ambiguity-abort
guarantee. A dated note (Vladimir's standing rule of 4 October 2026) adds
that the OEIS b-file reaches `n = 75` by a method the entry does not state
(question 4 stays open; the terms were not verified). **Nothing in the
source was found to be wrong**, and no unproved claim of the source lies
outside the four questions. Refuted with proof: the OEIS comment's
"(or equivalently, squarefree integers)" (Remark 2.1).

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 22/22. The
  dossier read the manuscript and found no error, checked the Mellin factor
  and the pole argument of Lemma 8.1, the comment's failure at `n = 2`, and
  `K`, and reran the companion on copies: `exact` and `cpp --n 20` identical
  to the delivered outputs; the optional `cpp --n 35 --allow-full` (3.6 s,
  `PASS`, 428,363,342 vectors, 788 generators, no ambiguous comparison, all
  35 terms equal to the fixture); `diagnostics` equal up to the last binary64
  digits; `test_companion.py` and `test_build.py` fail on Windows at their
  symlink guards.
- At the write (6 October 2026; same machine; Python 3.14.4, mpmath 1.3.0,
  MinGW-w64 g++ 16.1.0): every proof line by line (the list is in Section
  1.1), with no mathematical error found; the bound `|E(u)| ≤ 4u` also
  numerically at every jump `√d`, `d < 4·10⁵` (`max |E(u)|/u = 0.86`); with
  its own code, `A`, `K`, Table 1 against the b-file, Table 2 to every
  printed digit, and its extension `e^{H(n+1)}/a(n) − 1 ≈ −0.00277, −0.00247,
  −0.00214` at `n = 50, 60, 75` (rounded; ratio to `t` from `−0.040` at
  `n = 5` to `−0.006` at `n = 75`); the integer-radicand counts by brute
  force. The companion rerun from the shipped files (Route B below): `exact`
  and `cpp --n 20` byte-identical to the shipped outputs; `cpp --n 35
  --allow-full` `PASS` in about 3 s with the counts above (so Table 1's rows
  `n = 25, 30, 35`, labelled "historical", are now freshly reproduced);
  `diagnostics` within `4·10⁻¹⁵` of the shipped values (last binary64
  digits); `test_companion.py` fails at its broken-symlink guard on Windows.
- Sources read by the write: the OEIS entry and b-file; Kohlbecker (AMS PDF:
  introduction, Main Theorem, Corollaries 1 and 1*); Bringmann–Jennings-
  Shaffer–Mahlburg arXiv:1910.03036v3, Section 4, Theorems 4.1–4.2 (the
  hypotheses (a)–(d), (i)–(ii) are those Section 9 checks);
  Dong–Robles–Zaharescu–Zeindler arXiv:2412.20101v1, Section 6 ((6.10),
  Lemmas 6.2 and 6.8); the transseries volume. Not read: Ingham's paper,
  Agarwala–Auluck, A000333, DLMF 25.10.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
7.1(a)–(b) applies is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about this sequence is.

**The transseries volume.** Remark 7.1: the index a staircase instance;
Theorem 1.3 not an instance (direct `O(1)`, `O(log y)` estimates), with a
second route through `p0:thm:staircase`(1); the leading inverse a trivial
formal `plt:thm:lw-template` instance; the implicit equation not shown to be
an instance.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a097356-sqrt-restricted-partitions` and `a022629-distinct-partition-norms`
use the same toolkit (exact saddle, Edgeworth term, integer inverses) for
different integer-part products; `a126764-lconvex-polyominoes` and
`a022629-distinct-partition-norms` also cite Ingham's theorem. No result is
shared, so no reciprocal note is proposed.

**Stale claims.** Before batch 109 no file of the repository named A397045,
and no report counted sums of square roots by value.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `K`, `𝒦`, `𝒦_T`; `A`, `𝒜`; `a`, `a(n)`;
`H`, `H_3`; `m(t)`, `m_d`, `m_1`, `m`; `v(t)`, `v`, `u`; `D`, `𝒟`; `E`,
`𝔼`; `R(t)`, `R_t(u)`; `B(u)`, `B_0`, `B_T`; `G`, `G(y)`, `g_t`; `Δ`, `δ`;
`h`, `h_1`, `h_2`, `L`; `q`, `Q`, `Q_r`; `c`, `c_0`, `c_*`, `c_1`; `t`, `T`,
`J`; `ρ`, `ν`. No symbol was renamed; the volume's colliding letters carry
the subscript "vol" in Remark 7.1.

## Labels

Every label carries the prefix `srs:` (`dsr:` is used by other reports; none
used `srs:`). The manuscript's 90 labels (`eq:` 68, `sec:` 12, `thm:` 4,
`lem:` 4, `prop:` 1, `cor:` 1) were prefixed before anything cited them, and
the 84 references to them (59 `\eqref`, 25 `\ref`) updated. The write added
5: `srs:rem:oeis`, `srs:sec:provenance`, `srs:rem:comment`,
`srs:eq:integermodel`, `srs:rem:transseries`. The report has 95 labels;
builds of the delivered text and of this one give all 90 delivered labels
the same numbers (aux files compared). The added statements are the last of
their sections, the added subsection follows the last delivered text of
Section 1, and nothing was inserted before a delivered display, table or
statement.

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered Report172.tex; labels prefixed, [write] additions)
article.pdf                               compiled report, 26 pages
sources-REFERENCES.md                     the source's access record of its references (delivered sources/)
code/companion.py                         exact, cpp and diagnostics commands (delivered code/)
code/enumerate_roots.cpp                  independent C++ enclosure enumerator (delivered code/)
code/test_companion.py                    companion tests; fail on Windows at a symlink guard (delivered code/)
code/test_build.py                        build-guard tests; POSIX (delivered code/)
code/build.py                             clean-tree PDF and ZIP builder, TeX Live (delivered at the root)
data/BUILD-INFO.json                      toolchain and reproducibility scope (delivered at the root)
data/requirements.txt                     no pip dependencies, with comments (delivered at the root)
data/fixtures-SHA256.json                 fixture hash, read by the companion (delivered fixtures/)
data/fixtures-oeis_35_historical.json     the 35 OEIS terms and a(0) = 1, verified run of n <= 35 (same)
data/fixtures-provenance.json             historical versus fresh coverage (same)
data/sources-source_provenance.json       primary sources and access (delivered sources/)
data/generated-exact.json                 recorded exact checks, n <= 20 (delivered generated/)
data/generated-cpp_n20.json               recorded C++ run, n <= 20 (same)
data/generated-saddle_diagnostics.json    recorded binary64 diagnostics (same)
data/generated-tests.json                 test receipt, normal Python (same)
data/generated-tests_optimized.json       test receipt, python -O (same)
data/generated-build_tests.json           build-test receipt, normal Python (same)
data/generated-build_tests_optimized.json build-test receipt, python -O (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report172.pdf` (the delivered 20-page PDF, 412,337 bytes);
`SHA256SUMS.json` (2,100 bytes, 22 entries, verified at placement;
repository policy ships no checksum manifests); and the delivery `README.md`
(7,945 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`code/companion.py` reads `fixtures/` at `../fixtures` from its own directory
(`ROOT = Path(__file__).resolve().parent.parent`) and checks the fixture's
SHA-256; `code/build.py` expects `Report172.tex`, `README.md`,
`requirements.txt`, `build.py`, `code/`, `fixtures/` and `sources/` at the
package root and writes `generated/`; `code/test_companion.py` and
`code/test_build.py` use the delivered names; `data/BUILD-INFO.json`
describes `SHA256SUMS.json`; `data/fixtures-provenance.json` and
`sources-REFERENCES.md` describe the fixture and the n = 35 run as not
rerun; Section 10.3 of the article describes the delivered archive ("this
PDF", "The README"). So no program runs under the shipped names; use one of
the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Distinct_Square_Root_Sums_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 0b71479e336a2bdd6561965cfd0581bbeb90f4dc8bbadd833e1f8c0efbec3d08, 565,603 bytes
cd "$T" && unzip -q a.zip
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only; `g++` with C++17 and
`__uint128_t` for the C++ commands. Never run anything in the repository.
Each `--output` must be a new file.

**Route A, delivered layout**, from `$T`:

```sh
python code/companion.py exact --output NEW-exact.json
python code/companion.py cpp --n 20 --output NEW-cpp20.json
python code/companion.py cpp --n 35 --allow-full --output NEW-cpp35.json   # optional, the full n <= 35 run
python code/companion.py diagnostics --output NEW-saddle.json
python code/test_companion.py --output NEW-tests.json                      # POSIX (symlink guards)
python code/test_build.py --output NEW-build-tests.json                    # POSIX
python build.py --output /existing/dir/Report172-new.zip --pdf-output /existing/dir/Report172-new.pdf   # TeX Live, POSIX
```

**Route B, from the shipped files** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a397045-square-root-sums
B=$(mktemp -d); mkdir -p "$B/code" "$B/fixtures" "$B/generated" "$B/sources"; cd "$B"
cp "$R"/code/companion.py "$R"/code/enumerate_roots.cpp "$R"/code/test_companion.py "$R"/code/test_build.py code/; cp "$R/code/build.py" .
for f in "$R"/data/fixtures-*; do n=$(basename "$f"); cp "$f" "fixtures/${n#fixtures-}"; done
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
cp "$R/data/sources-source_provenance.json" sources/source_provenance.json; cp "$R/sources-REFERENCES.md" sources/REFERENCES.md
cp "$R/data/BUILD-INFO.json" "$R/data/requirements.txt" .; cp "$R/article.tex" Report172.tex
```

then the commands of Route A (`build.py` also needs the delivery
`README.md`, from the archive). At the write, in this layout, `exact` and
`cpp --n 20` gave the shipped outputs byte for byte, `cpp --n 35
--allow-full` passed in about 3 s, `diagnostics` agreed to the last binary64
digits, and `test_companion.py` failed at its broken-symlink guard (Windows);
`test_build.py` and `build.py` were not run. Use `py` where `python` is not
on the path.

## Build the PDF

pdfLaTeX (geometry, fontenc, lmodern, microtype, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, float, hyperref, enumitem,
fancyhdr); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 26
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered text, built the same way, gives 20 pages and
two duplicate destinations (`table.1`, `table.2`), because it loads `float`
after `hyperref`; the write loads `float` before `hyperref` (a dated comment
in the preamble), which removes them. The delivered byte-identity claims
(`SOURCE_DATE_EPOCH`, suppressed PDF dates) apply to `Report172.tex` under
the delivering toolchain (pdfTeX, TeX Live 2025/dev), not to this build.

## From the delivery README

The delivery README (replaced by this guide) listed the contents; said the
default fresh calculation covers `n = 0, …, 20` (458,000 canonical nonunit
vectors, 268 generators, denominator `2^96` enclosures in Python, `2^48` in
C++) and a direct shell enumeration to `n = 12` (14,155 vectors), with
strict and weak endpoints tested at `0, 1, √2, 2√2, √2+√3, √2+√5, 3, 6`;
that "No floating-point number decides membership" and that "Every
unresolved comparison aborts without emitting a successful result"; that the
full `n = 35` run is optional ("no fresh full rerun is claimed"); gave the
build command (new destinations only, temporary trees, deterministic ZIP)
and the diagnostic commands with the tail bound, adding that "The output is
diagnostic, not a finite-n error certificate"; and that the package "does
not redistribute third-party papers".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS entry
A397045 and the fixture transcribes its terms; OEIS content is published by
The OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and
that content remains under that licence. Short quotations of the cited
papers are for attribution. No third-party PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A397045 and A000333; Kohlbecker,
  Trans. AMS 88 (1958); Ingham, Ann. of Math. 42 (1941);
  Bringmann–Jennings-Shaffer–Mahlburg (arXiv:1910.03036v3); Agarwala–Auluck,
  Proc. Cambridge Philos. Soc. 47 (1951); Dong–Robles–Zaharescu–Zeindler
  (arXiv:2412.20101v1); DLMF 25.10.
- Batch 109 of `docs/incoming`, bundle Report 172; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report172.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
