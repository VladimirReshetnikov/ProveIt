# Exact Pole Sectors and Integer Recovery for Ordered Tuple Relations (OEIS A173217, A301466, A301468)

**Sets of distinct ordered d-tuples on an active ordered vertex set: an
exact-amplitude pole decomposition after the signed-Stirling transform with a
global tail bound, absolute integer recovery from O(n^{1−1/d}) exact poles
with a certified rational-interval algorithm, an all-fixed-order compact-complex
collision kernel, and shrinking two-ceiling inverse enclosures; with three
confirmed corrections to the repository's transseries volume.**

A single-source report: bundle Report 220 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The author line and
the PDF author field read "Research report"; the manuscript names no person,
tool or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Exact pole sectors and integer recovery for ordered tuple relations: All-fixed-order collision kernels and shrinking inverse enclosures* ("Report220", 4 October 2026) | `Report220-reproducibility.zip` (688,477 bytes, 26 files, wrapper `Report220/`; `Report220.tex`, 757 lines (the write said 758), 18 pp.) | `a4186a946` | `article.tex` |

**Pin:** the package records ProveIt commit `c744ff67d` (4 October 2026), an
ancestor of the placement; the write verified the three Git blobs, the
SHA-256 and the quoted line ranges. The transseries volume was unchanged at
the write (same blob); `d92db8d06` later added two dated repair boxes recording
the corrections of Appendix A (blob now `f6f91ca8…`).

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

`H_d(n)` (d ≥ 2) counts pairs `([v], E)` with `E ⊆ [v]^d` a set of `n`
distinct ordered tuples using every vertex (`d = 2, 3, 4`: A173217, A301466,
A301468). `λ = log 2`, `z_m = λ + 2πim`, `B_{d,n} = (dn)!/(2 n! λ^{dn+1})`.

- Section 2: `H_d(n) = Σ_k C(k^d, n)/2^{k+1}` (2) and the signed-Stirling
  transform of the Fubini numbers; Lemma 2.1 the positive-degree pole identity
  (proved by Fourier series); **Theorem 2.2:**
  `H_d(n)/B_{d,n} = Σ_m (λ/z_m)^{dn+1} A_{d,n}(z_m)` with explicit polynomial
  amplitudes.
- **Theorem 3.2:** a global tail bound after the transform, valid for cutoffs
  growing with `n`; Corollary 3.3: exponentially separated fixed sectors.
  Theorem 4.1: the normalized growing-cutoff bound, which cannot certify
  rounding (11).
- **Theorem 5.2:** with `M = ⌈(d/6)(2n^{d−1})^{1/d}⌉`,
  `|H_d(n) − T_{d,n,M}| < 13/(18 n^{d−1}) ≤ 13/36`, so `2M − 1 = O(n^{1−1/d})`
  exact poles recover the integer; Corollary 5.3 a harmonic cutoff; a
  certified algorithm with rational intervals (Section 5.1).
- **Theorem 6.1:** all fixed orders of the collision kernel `G_{d,n}(w)`,
  uniformly on compact complex sets; explicit (33)–(37).
- Section 7: the first nonreal sector (38)–(39) and the divergence of the
  fixed-pole surrogate. Section 8: the known leading equivalents, smooth
  models `F_{d,R}`, Lemma 8.1 (monotonicity), **Corollary 8.2** (two-ceiling
  enclosures of the threshold).
- Appendix A: three corrections to the pinned transseries volume.

(Section, statement and equation numbers are those of the committed PDF;
equations are numbered consecutively, (1)–(51).)

## What the report does not claim

The enumeration, the signed-Stirling transform, the Fubini pole identity
(Hickerson, A000670) and the leading equivalents (OEIS) are prior;
Novelli–Thibon–Thiéry give context, Cameron–Prellberg–Stark the collision
methods, the repository reports are method precedents. No worldwide priority
claim; it does not solve the A260700 or matrix-composition sector questions.
Cutoffs and constants are not claimed optimal; the pole count is not a
bit-complexity or stability statement; compact-w uniformity does not reach the
recovery scale; inverse constants and onset are existential, with no
single-ceiling formula; the decimal diagnostics are not interval certificates.

## The write's findings

- **The transseries volume (Appendix A, dated notes):** all three corrections
  confirmed. The proof of `q2:thm:fubini` drops the constant 1/4 of the
  symmetric Mittag-Leffler expansion (`1/(2 − e^z) → 1/2` as `Re z → −∞`;
  the pole part is 3/4 at `z = 0`); the theorem, for `n ≥ 1`, survives.
  `q2:rem:weighted` needs `max`, not `min`, of `ρ_x` (`|T_1(1) − 1| = 0.0390…`
  against `(log 1.1)²/12 = 0.000757…`), and reverses the large-weight
  direction (the first modulus ratio is 0.740 … 0.00158 for `x = 0.001 … 100`).
  The write adds that the volume's own proof of the uniform bound transfers to
  the weighted family only while `ρ_x ≤ 2π`, whereas the report's bound (51)
  needs no restriction. At the write the volume still had all three passages;
  its correction is the separate commit `d92db8d06` (see the independent
  check); the volume is not edited here.
- **The OEIS entries** (Remark B.1): A173217 (#30, Paul D. Hanna 2010;
  equivalent by Václav Kotešovec 2018), A301466 (#10) and A301468 (#4)
  (Kotešovec 2018, with the general `m > 2` equivalent), A000670 (#913,
  Hickerson's pole formula), and A173219, A121251, A104209 as Appendix B
  describes them. The write's counts equal the b-files (A173217 to n = 100,
  A301466 to 60, A301468's 11 terms). No conjecture (corrected at the
  independent check: A000670 displays two, unrelated); no OEIS edit.
- **Recomputed with the write's own code:** counts by two formulas and by
  brute force; the tail bound and majorant on grids; the cutoff table (exact);
  recovery at both cutoffs for 21 inputs (all errors below the bounds, all
  rounding to `H_d(n)`); `C_{d,1}` for `d = 2..5`, `c_1`, `c_2` (own
  implementation of (24)–(26)); (36)–(37) by a direct expansion independent of
  the kernel; the `d = 2` expansion numerically at three points; the
  equivalents and `b_{d,1}`; the Lambert formula; the first nonreal pair at
  `n ≤ 320` with exact amplitudes.
- **Remark 8.3 (transseries volume):** Lemma 2.1 is the first equality of
  `q2:thm:fubini` (same statement, independent proof); Theorems 3.2 and 5.2
  are analogues of `q2:thm:pole-tail` and `q2:prop:budget`; growth outside
  `p0:def:model`; the order-zero inverse (48) an exact instance of
  `p0:thm:lambert-core`; `x_R` for `R ≥ 1` not shown to be an instance of
  `plt:thm:lw-template`; Corollary 8.2 an analogue of `p0:thm:staircase`(2).

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`7ad0ec8ab`) read the seven
OEIS entries again and recomputed every number the write added, with its own
code. It also checked the two repair boxes that `d92db8d06` added to the
transseries volume. It is recorded in a dated note at the end of Appendix B.

- **Confirmed:** `H_d(n)` by inclusion–exclusion (2) against the three b-files
  (A301466 to 175 by the Stirling–Fubini formula), brute force, the table of
  Section 1 and monotonicity; the cutoff table; recovery below
  `13/(18n^{d−1})` (and the harmonic bound) at both cutoffs for nine inputs up
  to `(12,10)`; `max K/R = 0.3183157`; the log-2 bounds; `κ(d,a_*) + β_d = 2 − log 2`;
  (34), (36), (37) and `C_{d,1}` from the definition (3) of the amplitude
  (stable residuals to `n = 2000`); `b_{d,1}`; the first nonreal pair (ratio
  1.0173 at `n = 20`, `1 + 6·10^{−14}` at 40); Appendix A's identity, values
  and ratios; the pin (commit, three blobs, SHA-256, quoted lines); both
  manifests; the byte identity of the 20 staged files and of the omitted byte
  copy; Remark 8.3; the label numbering (74 delivered labels unchanged) and
  the file listing.
- **The volume's repair boxes (`d92db8d06`) are right.** The constant is
  `1/4` exactly. With `|u_k(x)| < 1` for `k ≠ 0` the bound `ρ_x²/12` holds for
  every `x > 0`. The volume's monotonicity argument fails for `ρ > 2π` (for
  example at `ρ = 7` from `n = 2` on). The numbers in both boxes agree. **One point
  the boxes do not mention:** the proof of `q2:thm:weighted` applies the
  Mittag-Leffler argument "verbatim". The symmetric expansion of
  `(1 − x(e^z − 1))^{−1}` has the entire part `1/(2(1 + x))`, not 0. That
  theorem, too, stands for `n ≥ 1`. This is reported to the volume's owner;
  the volume is not edited.
- **Corrected (dated notes):** the delivered text has 757 lines, not 758. The
  statements that the volume is unchanged are dated by the later repair (the
  `TSvol` entry is no longer the pinned blob). "None of the entries has a
  conjecture" is wrong for A000670: it displays Peter Bala's 2022
  periodicity conjecture and Mikhail Kurkov's 2018 formula (marked proved in
  2026), neither related to this report.

No mathematical claim of the write was found wrong. Rebuilt: 24 pages (23),
label numbers unchanged.

## Further questions, and the standing rule

Section 10 (sharper cutoffs, precision and bit complexity, growing complex
arguments, effective inverse thresholds, other edge models), with a dated note
under Vladimir's standing rule of 4 October 2026; added from the non-claims:
explicit constants for Corollary 8.2 and interval certificates for the
diagnostics. No claim of the source was found false; its three corrections to
the volume are confirmed.

## Relation to the repository

No other file of the repository names A173217, A301466 or A301468. The
report cites, at the pinned commit, the transseries volume (whose Fubini
chapter it corrects), `a260700-parabolic-double-cosets` and
`a261781-matrix-compositions`. Its exact nonreal sectors through one
signed-Stirling transform bear on, but do not answer, Question 3 of
`a260700-parabolic-double-cosets` (nonreal Fubini poles through both defect
sums); a reciprocal note there is proposed with this write.
`a386374-first-block-maximum` (batch 113) uses the same Fubini pole for
another statistic. No Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `otr:`: the 74 delivered labels, prefixed before
anything cited them (50 references updated: 31 `\eqref`, 19 `\ref`), the
write's label for Appendix B (`otr:app:scope`) and its three
(`otr:sec:provenance`, `otr:rem:transseries`, `otr:rem:oeis`); 78 in all. The
write's remarks are the last statements of their sections and its additions
contain no numbered display, so every number is delivered (checked against
the `.aux` of a build of the delivered text: 74 labels, 0 differences).
Section 1.1 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.1 with the false readings: `λ`/`ρ` (Appendix A follows the volume's `ρ`),
`H_d`/`h` (`H_d(n)` is not a harmonic number), `A`/`B`, `S`/`s`, `T`/`F`, `C`,
`E`/`e`/`D`, `K`/`M`/`R`, `q`/`L`, `w`/`z`/`Θ`/`θ`, `p`/`β`/`γ`.

## The write's additions

The status note after the abstract, Section 1.1 (provenance and pin, sources
read, checks, relation, collected non-claims, reading conventions), Remarks 8.3
and B.1, the dated notes in Sections 9 and 10 and in Appendix A (the pin and
the three confirmations), the label prefixes and the label of Appendix B, the
bibliography entry `TSvol`, the `\file` macro and `writenote` environment, and
one preamble line (`etoolbox`, a ragged-right bibliography, which removes the
delivered build's two underfull lines). Everything else is delivered text.

## Files

```text
README.md                               this guide (replaces the delivered README.txt)
SOURCES.txt                             the source's attribution and pin notes
article.tex                             the report (delivered Report220.tex, written)
article.pdf                             compiled report, 24 pages
code-README.md                          the source's code guide (delivered code/README.md)
code/check_hypergraph.py                exact counts, pole-tail and asymptotic diagnostics (mpmath)
code/derive_hierarchy.py                exact kernel coefficients through order four (SymPy)
code/negative_controls.py               rejection cases, oracle independence, serialization regressions
code/outer-reproduce.py                 the delivered root driver: finite checks, PDF and ZIP
code/rational_checks.py                 certified recovery, rational constants, exact inequality suites
code/reproduce.py                       finite driver (each program twice normally and twice under -O)
code/validation.py                      shared guards and JSON writers
data/PROVENANCE.json                    hashes of the scripts this package was adapted from (delivered code/)
data/SOURCE_FILES.txt                   the delivered public inventory
data/code-requirements.txt              SymPy and mpmath pins (delivered code/requirements.txt)
data/hierarchy_reference.json           pinned kernel coefficients (delivered code/; equal to the recorded output)
data/oeis_reference.json                OEIS terms for n = 0..8 (delivered code/)
data/requirements.txt                   the delivered root requirements (pins and toolchain notes)
data/results-check_results.json         output of check_hypergraph.py
data/results-negative_controls.json     output of negative_controls.py
data/results-rational_checks.json       output of rational_checks.py suite
data/results-recovery_example.json      output of rational_checks.py recover 2 25
data/results-reproduction_receipt.json  the finite driver's receipt
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
the delivered `Report220.pdf` (18 pages) and `README.txt` (replaced by this
guide); the pure checksum manifests `MANIFEST.json` (25 entries) and
`code/SHA256SUMS.txt` (17 entries), both verified at the write; and
`code/results/hierarchy_coefficients.json`, a byte copy of
`data/hierarchy_reference.json`.

```sh
git show 60f54ea06:docs/incoming/Report220-reproducibility.zip > <scratch>/r220.zip
```

**Delivered text that names the delivery layout.** `SOURCES.txt`,
`code-README.md`, `data/SOURCE_FILES.txt`, `data/PROVENANCE.json` and Section
9 of the report describe the delivered archive (`Report220.tex`, `code/`,
`code/results/`, `MANIFEST.json`); the programs read
`hierarchy_reference.json` and `oeis_reference.json` next to themselves; both
drivers expect that layout (a dated note in Section 9 says what is shipped).

**Third-party data.** `data/oeis_reference.json`,
`data/results-check_results.json` and `data/results-rational_checks.json`
contain OEIS terms of A173217, A301466 and A301468 (CC BY-SA 4.0, https://oeis.org/LICENSE).

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash), restore the
delivered names in a scratch directory:

```sh
T=$(mktemp -d); mkdir -p "$T/code" "$T/o"; cp code/*.py "$T/code/"
cp data/hierarchy_reference.json data/oeis_reference.json "$T/code/"
D=$PWD/data; cd "$T"
py -B code/derive_hierarchy.py --output o/hierarchy_coefficients.json        # SymPy 1.14.0
py -B code/check_hypergraph.py --coefficients o/hierarchy_coefficients.json --output o/check_results.json   # mpmath 1.3.0
py -B code/rational_checks.py suite --output o/rational_checks.json           # standard library
py -B code/rational_checks.py recover 2 25 --output o/recovery_example.json
cmp <(tr -d '\r' < o/hierarchy_coefficients.json) <(tr -d '\r' < "$D/hierarchy_reference.json") && echo same
for f in check_results rational_checks recovery_example; do
  cmp <(tr -d '\r' < o/$f.json) <(tr -d '\r' < "$D/results-$f.json") && echo "same $f"; done
```

At the write (7 October 2026, Windows, Python 3.14.4) all four outputs, also
under `-O`, equalled the shipped files after removing carriage returns (about
one minute in all). `negative_controls.py`, and with it the finite driver
`code/reproduce.py`, stops on Windows at a regression that compares the
console output (CRLF line ends) with the saved file, a Windows-only failure
also recorded at intake. The outer PDF/ZIP driver was not run.

## Build

pdfLaTeX (lmodern, amsmath, amssymb, amsthm, mathtools, microtype, booktabs,
longtable, array, xcolor, geometry, hyperref, etoolbox). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was rebuilt at the independent check from this file with
MiKTeX pdfLaTeX (three passes, 7 October 2026): 24 pages (the write's: 23); no errors or warnings, no undefined references, no
multiply defined labels, no duplicate destinations, no overfull or underfull
boxes. The delivered text gives 18 pages and two underfull lines in the
bibliography.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 220 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: OEIS A173217, A301466, A301468, A000670;
  Novelli–Thibon–Thiéry (2004); Cameron–Prellberg–Stark (2006, two papers);
  Bender–Canfield–McKay (1997); the repository's transseries volume,
  `a260700-parabolic-double-cosets` and `a261781-matrix-compositions` at the
  pinned commit; and the transseries volume at the current commit (added by the
  write).
