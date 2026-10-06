# Unlabeled Interval Graphs (OEIS A005975 and A005976)

**`C_n` and `I_n` are asymptotic to half the Fishburn numbers, with a
negative `F_{n−2} log n` correction, its constant
`b_0 = log(6/π²) + γ + 1`, and an inverse threshold kept inside two
ceilings**

A research article dated 2 October 2026 ("Report 133" of a session bundle),
built from one manuscript. Its author line reads "Report 133" and its PDF
author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 133 (batch 106) | `A005975_A005976_Interval_Graph_Asymptotics_and_Inversion_Source.zip` (wrapper directory `report133/`, 11 files, 492,968 bytes, SHA-256 `534c6615…8405c`), arrival commit `60f54ea06`; main file `report133.tex` (694 lines, 20 pp.) | none: the package names no ProveIt commit, path or report | `47fc7a069` (batch 106) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. Every asymptotic
statement has a conventional proof from stated external inputs; none rests
on a computation.

## Trust boundaries

- **External inputs, not re-proved** (Section 2 of the article; the write
  located each at the cited place): Hwang and Jin, *Asymptotics and
  statistics on Fishburn matrices and their generalizations* (54-page author
  PDF; J. Combin. Theory Ser. A 180 (2021) 105413): equation (1.1)
  (Zagier's expansion `F_n = c μⁿ n^{n+1}(1 + c_1/n + O(n⁻²))`, p. 2),
  Theorem 25(ii) and the probability generating function of the diagonal
  size in its proof (pp. 40–41), Corollary 29 (self-dual counts, p. 46). The
  arXiv version 2 numbers these Theorem 22 and Corollary 26 and prints (1.1)
  only with `O(n⁻¹)`. Gallai's orientation theorems as Theorems 3–6 of
  Klavík, Kratochvíl, Krawczyk and Walczak (arXiv:1204.6391v1, Section 4).
- **What is proved by hand.** The graph-fibre analysis: simplicial vertices
  are the diagonal cells of the Fishburn matrix (Lemma 4.1), the rooted
  counts `T_m, R_m = (2 log m + O(1))F_m` (Lemma 4.2), genericity (Lemmas
  5.1–5.4), the exact two-to-one dominant fibres (Proposition 6.1), the
  four-case loss bound (Section 7), the transfer (Section 8), the constant
  (Section 9) and the inverse (Section 10).
- **The finite checks prove nothing asymptotic.** The shipped checker
  regenerates Fishburn matrices through size 9 and tests the constructions;
  "They do not establish the infinite asymptotic estimates, a finite error
  constant, or a rounding certificate."
- **Priority is not established.** See "What was known" below.

## What it proves

`I_n` and `C_n` count all and connected unlabeled interval graphs on `n`
vertices (A005975, A005976), `F_n` the unlabeled interval orders (Fishburn
numbers, A022493), `q = 6/π²`. Statement numbers follow the section counter
and are the delivered ones; labels carry `ivg:`.

- **Theorem 1.1 (`ivg:thm:main`)**: `C_n = F_n/2 − F_{n−1} − F_{n−2} log n
  + O(F_{n−2})` and `I_n = F_n/2 − F_{n−1}/2 − F_{n−2} log n + O(F_{n−2})`;
  relative forms `2C_n/F_n = 1 − π²/(3n) − π⁴ log n/(18n²) + O(n⁻²)`, and
  `− π²/(6n)` for `I_n`.
- **Corollary 1.2**: `a_n = K n! √n qⁿ (1 + α/n − β log n/n² + O(n⁻²))`
  with `K = 6√3 e^{π²/12}/π^{5/2} ≈ 1.3521662450`, `β = π⁴/18`,
  `α_I = a_F − π²/6`, `α_C = a_F − π²/3`, `a_F = 3/8 − 17π²/144 + π⁴/432`.
- **Theorem 9.1 (`ivg:thm:constant`)**: the same with `−(log n + b_0)F_{n−2}
  + o(F_{n−2})`, `b_0 = log q + γ + 1 ≈ 1.0795154`, from the constant of the
  rooted diagonal mean, a second exact fibre family ("universal vertex + leaf
  + generic core", loss `F_{n−2}/2`) and the next ordinal term; also
  `I_n = C_n + C_{n−1} + 2C_{n−2} + O(F_{n−3})`. Corollary 9.2 gives the
  relative coefficients.
- **Theorem 10.1 (`ivg:thm:inverse`)**: for `N_a(T) = min{n : a_n ≥ T}`,
  `⌈y − B/(y² log y)⌉ ≤ N_a(T) ≤ ⌈y + B/(y² log y)⌉`, `y` the large root of
  an explicit Stirling-type `Φ_α`; two Newton steps from
  `x = L/W(qL/e)` reach `y` within `O(x⁻³(log x)⁻³)`; monotonicity
  `C_{n+1} ≥ I_n ≥ C_n`. Constants and onset are not effective.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 10.3 (`ivg:rem:lambert`)**: strict monotonicity (`I` from `n = 1`,
  `C` from `n = 2`; `C_1 = C_2 = 1`), so `N_a(T)` is the integer staircase of
  the transseries volume's `p0:def:three-inverses` and its
  `p0:thm:staircase`(1) applies to every admissible interpolation. The
  Lambert start `x = L/W_0(qL/e)` is an **instance** of
  `p0:prop:factorial-core` (`κ = 1`, `d = log q − 1`). The equation
  `Φ_α(y) = L`, the Newton steps and the two-ceiling bracket are
  **analogous, not instances**: the bracket compares `a_n` with two smooth
  envelopes at the integers and uses no interpolation.
- **Remark 12.1 (`ivg:rem:bukhjeffs`)**: Bukh and Jeffs's unlabeled estimate
  stated precisely (below), and the sharpening
  `log a_n = n log n − (1 + log(π²/6))n + log n + log(K√(2π)) + O(1/n)` for
  `a_n ∈ {I_n, C_n}`, `log(K√(2π)) = 1.2206464656…`.
- **Remark 12.2 (`ivg:rem:hanlon`)**: Hanlon (1982), read; the literature to
  2023 (next section).
- Section 1.1 (provenance, the sources as read, relation to the repository,
  non-claims, reading conventions), the note at the end of Section 11
  (shipped layout, reruns) and Section 12.1 (further questions).

## What was known: Hanlon to Bukh–Jeffs

The intake had not read Hanlon (1982), so the placement record (`47fc7a069`)
said the leading term "may be classical". The write read the article (Trans.
Amer. Math. Soc. 272 (1982) 383–426, the AMS scan): it enumerates unlabeled,
labeled, identity and unit interval graphs through reduced graphs and
"buried" subgraphs, gives recursive generating functions (Theorem 3) and
tables of `I_n` for every `n ≤ 30` and of `C_n` at selected `n ≤ 30`
(Tables VII, VIII), derives
asymptotics only for unit interval graphs (Section 7), and in its
concluding Section 8 (p. 420) lists the asymptotic number of interval graphs
as an **open problem**, adding that it was not even known whether the
generating function has a positive radius of convergence. Yang and Pippenger
(Proc. AMS Ser. B 4 (2017); abstract read) showed that radius is zero. Acan
(arXiv:1810.02040, read) proved `log I_n ~ n log n` and called finding `I_n`
asymptotically a strong result (Remark 2). Bukh and Jeffs
(arXiv:2203.12063v2, 28 June 2023, read), in the third item of Section 5
"Problems and remarks", p. 11, derive from their Sandwich Theorem the
unlabeled bound `F_{n−2}/(n(n−1)) ≤ I_n ≤ F_n` (factor improvable to `1/2`
through Hanlon) and, with Brightwell–Keller's Theorem 1,
`log I_n = n log n − (1 + log(π²/6))n + O(log n)`. The source quotes this
correctly; Theorem 1.1 sharpens it (Remark 12.1). **None of these four
sources states `I_n ~ F_n/2`, anything for `C_n`, or a correction term.**
That settles the caveat about Hanlon; it does not establish priority, since
the literature after mid-2023 was not searched exhaustively.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- No all-orders expansion; no effective constants or onset; the inverse "is
  therefore not a finite algorithm" for exact thresholds, and
  `N_a(T) = ⌈y⌉ + O(y⁻²/log y)` is not asserted (Remark 10.2).
- No historical-priority claim; the source comparison "is not an exhaustive
  novelty search".
- The `n⁻²` coefficient of the conventional normalization (Corollary 1.2) is
  not evaluated.
- The external inputs are not newly proved; series identities are formal
  (no positive radius asserted); finite checks are not proofs; the archive
  seal is not a digital signature.

The write adds: its numbers are exact counts, ratios of them or
floating-point fits, and certify no limit.

## Further questions

Section 12.1 of the article ("Further questions and research",
`ivg:sec:further`) states every unproved claim as an open question with its
source, sketch and what is missing (Vladimir's standing rule of 4 October
2026). **Nothing in the source was found to be wrong.**

1. **The remainder beyond `b_0`** (`ivg:q:remainder`; source item 1).
   *Observation at the write:* with `δ^C_n = (F_n/2 − F_{n−1} − C_n)/F_{n−2}
   − log n` and its `I` analogue, both of which tend to `b_0 = 1.0795`,
   OEIS terms plus Hanlon's Table VII give `δ^C_n` = 1.2755, 1.1911, 1.1053,
   1.0914, 1.0800, 1.0707, 1.0631, 1.0570, 1.0520 and `δ^I_n` = 1.8802,
   1.6329, 1.4642, 1.4348, 1.4095, 1.3876, 1.3685, 1.3518, 1.3371 at
   `n = 15, 20, 24, …, 30`. `δ^C_n` decreases from its maximum 1.2817
   (`n = 16`) through `n = 30` and **falls below `b_0` between `n = 26` and
   `n = 27`**; `δ^I_n` is still above it at 30. The intake's reading
   ("decreasing towards `b_0`", through `n = 25`) is superseded: the approach
   is not monotone from above. Fits through 3–5 consecutive values ending at
   `n = 26, 28, 30` give limits from −21.4 to 2.8 (−3.8 to 1.7 for the
   windows ending at 30; corrected at the independent check, which found
   that the first wording, "the last 3–5 values", did not match the range),
   drifting with the window, so thirty terms neither confirm nor contradict
   `b_0`. The one input testable much further: exact diagonal totals `T_m`
   through `m = 200` give `T_m/F_m − 2 log m` = 0.338, 0.283, 0.201 at
   `m = 30, 50, 200`, extrapolating to 0.15904 against `2a_0 = 0.159031`
   (0.159031 with an additional `m⁻²` term, independent check).
2. **A full power–logarithm expansion** (`ivg:q:expansion`; item 2).
3. **Effective constants and an explicit onset** (`ivg:q:effective`; item 3
   and Remark 10.2).
4. **Higher exceptional fibres** (`ivg:q:fibers`; item 4).
5. **The `n⁻²` coefficient in the conventional normalization**
   (`ivg:q:conventional`): needs the second Fishburn coefficient, which the
   cited (1.1) does not print.
6. **External inputs and priority** (`ivg:q:external`).

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, standard library only):

- At placement (batch-106 dossier), in the delivered layout:
  `check_math.py` to standard output PASS, normal (2 min 26 s) and `-O`
  (1 min 19 s), byte-identical outputs (13,790 bytes; no delivered math JSON
  exists to compare); `verify.py --inventory-only` PASS (10 hashed files);
  `MANIFEST.sha256` 10/10. `test_adversarial.py`, `build.py` and `pack.py`
  were not run (symlinks, FIFOs, POSIX `O_NOFOLLOW`, Debian pdfTeX).
- At the write: on a fresh extraction of the archive from `60f54ea06`,
  `verify.py --inventory-only` PASS; route B below (`-O`, 20 s) reproduced
  the 13,790-byte output byte for byte. The 7 staged code and data files,
  and the staged `article.tex` and `README.md` before the write, are
  byte-identical to the archive.
- Independent numbers: the dossier checked the Euler transform of A005976
  against A005975 and `C_{n+1} ≥ I_n ≥ C_n` through `n = 24`, and `δ` values
  through 25. The write extended both to `n = 30` with Hanlon's Table VII
  (whose legible rows agree with the OEIS, and whose rows 25–30, inverted,
  reproduce Table VIII at `n = 10, 15, 20, 25, 30`), recomputed `F_n`, and
  computed `T_m` exactly through `m = 200` by inclusion–exclusion over forced
  zero rows and columns (it reproduces the article's `T_1, …, T_9`); the
  bound `F_{n−2}/2 ≤ I_n ≤ F_n` holds for `3 ≤ n ≤ 30`, and
  `n(F_n/(2K n! √n qⁿ) − 1)` = −0.5682 at `n = 30` (limit `a_F = −0.5647`).
- The dossier spot-checked Lemmas 5.1–5.4, Proposition 6.1, the Section 7
  case split and the Newton bound; the write rechecked the arithmetic of the
  constant in Theorem 9.1. No error.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`c6488293e`) fetched the OEIS b-files of
A005975 and A005976 (both `n = 1, …, 30`) and A022493 (`n ≤ 488`), and reread
Hanlon's article, Bukh–Jeffs (arXiv v2, printed p. 11), Acan (arXiv v1) and
the Yang–Pippenger abstract. It confirmed Remark 12.2 and the assignment of
the two sequences; the inverse Euler transform of the A005975 b-file
reproduces the A005976 b-file at every `n ≤ 30` and Hanlon's Table VIII at
every printed row, and Table VII's rows 25–30 equal the A005975 b-file. It
confirmed Remark 12.1 (`log(K√(2π)) = 1.2206464656`; differences −0.450,
−0.178, −0.102), the three parts of Remark 10.3 (monotonicity also checked on
the data through 30), all eighteen `δ` values, the maximum at `n = 16` and
the crossing between 26 and 27. Two sentences of `ivg:q:remainder` were
corrected, with dated notes keeping the first wording: the values beyond the
OEIS data fields are also in the OEIS b-files (which the write had not
used), and the fit range −21.4 to 2.8 comes from windows ending at `n = 26`
(windows ending at 30 give −3.8 to 1.7; the conclusion is unchanged). It
computed `T_m` through `m = 200` by an independent route — the diagonal
generating function of Hwang–Jin, Proposition 4(ii) and (2.12), to first
order at `v = 1`; brute force agrees for `m ≤ 6` and `F_m` equals the A022493
b-file for `m ≤ 200` — confirmed 0.338, 0.283, 0.201 and 0.15904, and with an
additional `m⁻²` term obtained 0.159031, that is `2a_0` to about `2·10⁻⁷`
(sentence added). No mathematical error was found. The record is a dated note
at the end of Section 12.1 (`ivg:sec:further`).

## Relation to the repository

**Formal status.** No Lean or Rocq file treats interval graphs, interval
orders (in the order-theoretic sense) or Fishburn numbers. Placement in the
collection confers no formal status.

**Neighbouring reports** (paths under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- [`a336070-weak-ascents`](../a336070-weak-ascents/) (**neighbour**): uses
  the same Hwang–Jin equation (1.1) as an external input
  (`wasc:gr:eq:fishburn`); its `d = 0` difference-ascent column is A022493.
  No shared theorem.
- **Siblings sharing a pipeline** (same placement commit `47fc7a069`,
  written separately in batch 106):
  [`a156808-circle-graphs`](../a156808-circle-graphs/) (bundle Reports 150
  and 152, unlabeled circle graphs A156808/A156809, labels `cgr:`) and
  [`a123448-permutation-graphs`](../a123448-permutation-graphs/) (bundle
  Report 153, unlabeled permutation graphs A123448, labels `prg:`). All
  three count a representation model (interval orders here; indexed chord
  matchings; permutations), show that almost every graph has a recoverable
  prime core with bounded decorations whose representations form one full
  orbit of the representation symmetry group (duality, of order 2, here,
  whence `F_n/2`; the dihedral group of order `4n`; the Klein four-group),
  make the symmetric cores negligible, and invert. No manuscript cites
  another; the decomposition theories, inputs and normalizations differ, and
  `S_n`, `F`, `T`, `Q`, `K`, `β` mean different things (Notation).
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
  (`p0:prop:factorial-core`, `p0:def:three-inverses`, `p0:thm:staircase`):
  Remark 10.3 says what is an instance; no novelty is claimed for the
  inversion.

**Stale claims.** The manuscript makes no claim about the repository, and
before batch 106 no file mentioned A005975 or A005976. Nothing to correct.

## Notation

A table at the end of Section 1.1 fixes the reused letters, with tempting
false readings: `I_n, C_n` (unlabeled; Bukh–Jeffs's `f_1(n)` is labeled),
`F_n` (Fishburn numbers, not `F(x) = Σ n! xⁿ` of `a123448`), `S_n` (self-dual
interval orders, not the symmetric matchings or simple permutations of the
siblings), `O_n, A_n` (versus big-O and the factor `A_m(v)`), `T_m, R_m`
(versus the level `T` of `N_a(T)`), `𝓔_m, 𝓓_n, 𝓠_m, 𝓙_n`, `B_m^all` versus
the bracket constants `B, B'`, `K, q, a_F, β` (versus the unknown `β` of
`a156808`), `a_0, b_0` versus `b = log(K√(2π))`, `c_1`, `L, L_j`, `u, w`,
`M`, `h`, `V, Λ`. No symbol was renamed.

## Labels

Every label carries the prefix `ivg:` (none existed in the repository). The
manuscript's 80 labels (`eq:` 56, `sec:` 11, `lem:` 7, `thm:` 3, `cor:` 2,
`prop:` 1) were prefixed before anything cited them, and all 94 `\ref`/
`\eqref` were updated. The write added 11: `ivg:sec:provenance`,
`ivg:rem:lambert`, `ivg:rem:bukhjeffs`, `ivg:rem:hanlon`, `ivg:sec:further`,
and the questions `ivg:q:remainder`, `ivg:q:expansion`, `ivg:q:effective`,
`ivg:q:fibers`, `ivg:q:conventional`, `ivg:q:external`. The report has 91
labels; a build of the delivered text and of this one give all 80 delivered
labels the same numbers (aux files compared). The added remarks are the last
numbered statements of their sections and the added displays are unnumbered.

## Files

```text
README.md                    this guide (replaces the delivery README)
article.tex                  the report (delivered report133.tex; labels prefixed, [write] additions)
article.pdf                  compiled report, 27 pages
code/check_math.py           self-contained exact checks (delivered at the package root)
code/output_guard.py         new-only, outside-bundle output guard imported by the others (root)
code/verify.py               closed inventory, manifest check, normal/-O replay (root)
code/build.py                two clean three-pass pdfTeX builds compared with the frozen PDF (root)
code/pack.py                 deterministic ZIP packing (root)
code/test_adversarial.py     inventory, output and mathematical mutation tests (root)
data/build-environment.txt   the delivering toolchain and deterministic settings (root)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (checked again at the write).

**Not shipped**, recoverable from the arrival commit (next section):
`report133.pdf` (the delivered 20-page PDF, 361,063 bytes);
`MANIFEST.sha256` (797 bytes, the SHA-256 seal of the other ten files;
repository policy ships no checksum manifests; verified at placement); and
the delivery `README.md` (10,245 bytes), staged at placement and replaced by
this guide (summarized under "From the delivery README").

**Delivered text that names the delivery layout or files not shipped.**
`code/verify.py` enforces the delivered flat eleven-file inventory
(`report133.tex`, `report133.pdf`, `MANIFEST.sha256`, the six programs,
`build-environment.txt`, `README.md`) in its own directory: **it rejects the
shipped layout and does not run here**; `build.py`, `pack.py` and
`test_adversarial.py` call it or assume the same layout. Section 11 of the
article speaks of "the source archive" and its README. Use the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A005975_A005976_Interval_Graph_Asymptotics_and_Inversion_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 534c6615efe491a12ebb17f5e423646ac36e93c4802859ed4ec5d4245d48405c, 492,968 bytes
cd "$T" && unzip -q a.zip     # creates report133/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only; no network. Never run anything
in the repository; output paths must be new and outside the package (the
programs refuse anything else).

**Route A, delivered layout** (POSIX host; `--inventory-only` tested at the
write on Windows, the full commands at placement):

```sh
cd "$T"
python3 -B report133/verify.py --inventory-only
python3 -B report133/verify.py --output "$T/verification.json"     # runs check_math normal and -O; several minutes
python3 -B report133/check_math.py --output "$T/math.json"
python3 -B -O report133/check_math.py --output "$T/math-O.json"
cmp "$T/math.json" "$T/math-O.json"
python3 -B report133/test_adversarial.py --output "$T/adversarial.json"   # POSIX only (symlinks, FIFOs)
```

`build.py` and `pack.py` (frozen-PDF byte comparison, deterministic ZIP)
need the recorded TeX Live/Debian toolchain and were not run by the intake.

**Route B, from the shipped programs** (tested at the write; it skips the
integrity layer and checks the mathematics only):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a005975-interval-graphs
B=$(mktemp -d); cp "$R/code/check_math.py" "$R/code/output_guard.py" "$B/"; cd "$B"
python3 -B -O check_math.py > out-O.json     # about 20 s to 80 s; prints the JSON to standard output
python3 -B check_math.py > out.json          # about 2.5 min
cmp out.json out-O.json
```

The output is 13,790 bytes and identical in both modes. Use `py` where
`python3` is not on the path.

## Build the PDF

pdfLaTeX (geometry, amsmath, amssymb, amsthm, mathtools, booktabs, array,
microtype, fontenc, lmodern, hyperref, fancyhdr); the bibliography is
embedded.

```sh
D=$(mktemp -d); cp article.tex "$D/"; cd "$D"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026: 27
pages after the independent check (26 at the write); no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source built the same way gives 20 pages
with one `amsmath` warning (`\atop`); the write typesets that summation
range with `\substack` (the same display). The article keeps the delivered
preamble lines that suppress PDF dates and trailer identifiers; the
delivered byte-identity check of the PDF applies to the delivered
`report133.tex` under the delivering TeX installation, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described "a reader bundle"
whose checker "regenerates its data using only Python's standard library"
and whose finite checks "do not constitute a proof of an asymptotic
theorem". It listed the exact flat inventory of eleven files and the
verifier's rules (no extra or missing file, no directory, symlink or special
file; a canonical sorted manifest); the reader commands for `verify.py`,
`check_math.py` and `test_adversarial.py` in normal and `-O` modes, with
outputs that must be new, outside the bundle and free of symlink components;
the deterministic PDF build (fixed source epoch, locale and time zone, three
pdfLaTeX passes in two clean builds compared with the supplied PDF), the
deterministic `ZIP_STORED` packing and fresh-extraction test; the coverage
and limits of the adversarial tests ("selected adversarial tests, not a
claim of exhaustive security testing"); and the author-only sealing command,
stating that the hashes and unkeyed manifest "are not a digital signature".

## Rights

Repository contents are MIT-0. The shipped files hold recomputed values
only, no OEIS data file. The article and this guide quote OEIS terms of
A005975 and A005976 and quantities computed from them; OEIS content is
published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE), and those terms remain under that licence. The
counts for `n = 25, …, 30` used in Section 12.1 are from Hanlon's 1982
tables (computed by A. Nymeyer in R. W. Robinson's project), cited, not
shipped. Nothing was submitted to the OEIS; A005975 and A005976 carry no formula
or asymptotic.

## Provenance

- Sources cited by the manuscript: Hwang and Jin (arXiv:1911.06690 and the
  author PDF); Klavík, Kratochvíl, Krawczyk and Walczak (arXiv:1204.6391);
  Bukh and Jeffs (arXiv:2203.12063v2); Hanlon, Trans. AMS 272 (1982);
  OEIS A005975, A005976, A022493. Added by the write: Acan
  (arXiv:1810.02040); Yang and Pippenger, Proc. AMS Ser. B 4 (2017); the
  transseries volume of this repository.
- Repository input: none; the package names no ProveIt commit or path.
- Batch 106 of `docs/incoming`, bundle Report 133; arrival `60f54ea06`,
  placement `47fc7a069`, written 5 October 2026. Single source, so no merge
  choices. The delivered `report133.tex` is shipped as `article.tex`; the
  delivered programs and build record as listed above.
