# Fixed-Couple Ménage Rows (OEIS A332709)

**Proofs of both conjectures displayed in A332709 (adjacent differences equal
A127548, row unimodality), discrete concavity and log-concavity with all
equality cases, a position-uniform all-orders expansion of every row, an exact
total-variation identity in every row, and fixed-column inverse models with a
two-candidate threshold enclosure.**

A single-source report: bundle Report 221 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The author line and
the PDF author field read "Report 221"; the manuscript names no person, tool
or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Fixed couple ménage rows: Exact differences, concavity, uniform expansions and inverse enclosures* ("Report 221", 4 October 2026) | `Report221.zip` (475,232 bytes, 16 files, no wrapper directory; `Report221.tex`, 591 lines, 16 pp.) | `a4186a946` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded; its source
ledger pins the Git blobs of two repository files, which were the current ones
at the write; the transseries volume has since received two dated repairs in
Appendix V (`d92db8d06`), not touching the statements the report compares.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration in this repository exists for any statement of this report, and
its place in the collection confers no formal status.

## What the report proves

`T(n,k)` (A332709, `3 ≤ k ≤ n`) counts ménage permutations of `[n]` with
`π(1) = k`; `A(n,s) = T(n,s+2)`, `U_n` the ménage numbers (A000179, row sums),
`L_m` A127548, `q = min(s, n−1−s)`.

- Section 2: the Shevelev–Moses factorization (5) through path matching
  polynomials (credited), reflection, `L_m = U_m + 2 Σ_{r<m} U_r` (11).
- **Theorem 3.2:** `T(n,k) − T(n,k−1) = L_{n−2k+4}` for `4 ≤ k ≤ n`,
  `n ≥ 2k−3` (with `0` at the even centre and the reflected negatives), the
  A332709 difference conjecture.
- **Theorem 4.2:** every row is positive, palindromic, unimodal and
  discretely concave, with the exact maxima (a four-entry plateau for even
  `n ≥ 6`), all concavity and log-concavity equality cases; the A332709
  unimodality conjecture.
- Theorem 5.1: an exact mean decomposition; Theorem 5.3: uniform truncation;
  **Theorem 6.1:** a position-uniform all-orders expansion of
  `(n−2)A(n,s)/U_n`, Table 1 through `n^{−10}`, and (2) for the fourth column
  A258667: `1 + 2/n⁴ + 16/n⁵ + … `.
- **Theorem 7.2:** the uniform-law total variation of a row is exactly
  `2(1/(n−2) − A(n,1)/U_n)` for every `n`, `= 2/n⁴ + 12/n⁵ + 48/n⁶ + …`.
- Theorem 8.1 (exact range recovery from smooth models), the Lambert start
  (39)–(40), **Theorem 9.1** (a two-candidate threshold enclosure with
  existential constants).

(Section, statement and equation numbers are those of the committed PDF;
equations are numbered consecutively, (1)–(45).)

## What the report does not claim

Rook inclusion–exclusion, the Shevelev–Moses factorization and their
unimodality observation, Kagey's prefix framework, the Kaplansky–Riordan
expansion, the Wyman–Moser rounding formula and the repository's inverse
distinctions are prior; no global novelty or first-proof claim; the publisher
texts of Kagey and Gu–Zhao were not read. Fixed orders, fixed columns for the
inverses, existential constants and onsets, no certified threshold algorithm,
no single-ceiling formula; floating diagnostics; the Lean proof was read, not
rerun.

## The write's findings

- **The OEIS entries** (Remark 11.1): A332709 is still at revision #33
  (1 February 2021, Peter Kagey) with both conjectures displayed; Theorems 3.2
  and 4.2 prove both posted statements (the difference on its natural domain
  `k ≥ 4`). All 1275 b-file terms (rows 3–52) equal the write's count.
  **A258667** (#79, 19 August 2026, Shevelev–Moses) conjectures
  `a(n) ~ e^{−2} n!/(n−2) (1 + Σ_{k≥1} (−1)^k/(k!(n−1)_k))`; Ralf Stephan's
  comment (30 June 2026) reports an AI agent's Lean proof of the leading
  equivalence. Read as a leading equivalence (as the Lean file formalizes it:
  `target_theorem_0` is an `IsEquivalent` statement) the conjecture holds;
  **read as an asymptotic expansion in powers of 1/n it fails at the fourth
  relative order**: by (23) the displayed expression is `(U_n + ϑ_n)/(n−2)`
  with `|ϑ_n| ≤ 1/2`, so by (2) `a(n)` divided by it is
  `1 + 2/n⁴ + 16/n⁵ + O(n^{−6})` (numerically `n⁴(ratio − 1)` = 3.10, 2.46,
  2.22, 2.10 at `n` = 20, 40, 80, 160). The source called its result
  "compatible" with the leading equivalence; the write records the stronger
  reading's failure. No OEIS edit.
- **Recomputed with the write's own code:** `T(n,k)` for `n ≤ 160` against
  the b-file, the entry's own formula and brute force (`n ≤ 9`); every exact
  statement of Sections 2–7 for `n ≤ 160` (differences, the complete
  shape classification, the mean identities, the TV identity and sign pattern,
  the auxiliary recurrences and bounds); **Table 1 rederived** from the ménage
  recurrence (28) and the line recurrence by exact power-series algebra, with
  bounded exact residuals `n^{11}(R − Σ c_r n^{−r})` at `n = 60, 100, 140`;
  the TV coefficients; the Wyman–Moser rounding for `2 ≤ m ≤ 160`; the log
  expansion (38) and the inverse start (40) at exact range values.
- **Sources:** the Lean file at the current main branch plus one trailing
  newline reproduces the SHA-256 the source pins; the canonical volume's
  subtitle is "… and the inversion of rapidly growing functions" (the source
  shortens it to "… and inversion").
- **Remark 9.2 (transseries volume):** growth outside `p0:def:model`; the
  Lambert start (39) an exact instance of `p0:thm:lambert-core`; the refined
  start, the model inverse and (41) not shown to be instances of
  `plt:thm:lw-template`; Theorem 8.1 an analogue of `p0:thm:staircase`(3) and
  Theorem 9.1 of (2).

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`b353bba89`) read the OEIS
entries and the Lean file again and recomputed every number the write added,
with its own code: `T(n,k)` from the entry's double-sum formula (not the
cofactor formula (5)), `U_n` from Touchard's formula. It is recorded in a dated
note at the end of Section 12.

- **Confirmed:** all 1275 A332709 b-file terms, the A000179 and A127548
  b-files, the posted terms of A258664–A258667 and A258673; Theorems 3.2, 4.2
  (complete classification) and 7.2 (identity and sign pattern) for every
  `n ≤ 120`; Table 1 and the TV coefficients by exact residuals at
  `n = 100, 200, 300` (bounded and settling, also at the central column); the
  Wyman–Moser rounding for `2 ≤ m ≤ 300`; the A258667 ratio
  (`n⁴(ratio − 1)` = 3.1016, 2.4644, 2.2150, 2.1036, 2.0509 at
  `n = 20 … 320`, next coefficient → 16); the Lean file's size, pinned SHA-256
  (with one appended newline) and `IsEquivalent` statement; the provenance
  figures, the 15-entry manifest, the byte identity of the 12 staged files,
  Remark 9.2, the label numbering (60 delivered labels unchanged) and the
  file listing.
- **Corrected (dated note after Remark 11.1):** the write said that
  A258664–A258666 and A258673 "post no asymptotic formula". Each posts the
  A258667 conjecture `a(n) ~ e^{−2} n!/(n−2)(1 + Σ_{k≥1} (−1)^k/(k!(n−1)_k))`
  (revisions #85, #75, #74, #71, Shevelev–Moses), with no proof recorded. The
  report settles all four as it does A258667: by (23), Theorem 6.1 and
  Table 1, `a(n)` divided by the displayed expression is
  `1 − n^{−3} − 4n^{−4} + …` (A258664), `1 + 2n^{−4} + 15n^{−5} + …`
  (A258665) and `1 + 2n^{−4} + 16n^{−5} + …` (A258666, A258673). So each
  conjecture holds as a leading equivalence and fails as an asymptotic
  expansion, at relative order `n^{−3}` (A258664) or `n^{−4}`. Exact counts
  agree (`n³(ratio − 1)` = −1.108 … −1.013, `n⁴(ratio − 1)` = 2.427 … 2.048
  and 2.464 … 2.051 at `n = 40 … 320`).
- **Stale (dated note after the provenance note):** the pinned blob of the
  transseries volume was current at the write; `d92db8d06` changed it later
  the same day (Appendix V only).

Rebuilt: 20 pages (19), label numbers unchanged.

## Further questions, and the standing rule

Section 12 (explicit inverse constants and onset, total-variation identities
for other boards, several fixed couples, higher-difference signs, the
inaccessible publisher texts), with a dated note under Vladimir's standing
rule of 4 October 2026; added: a rerun of the Lean proof. The two A332709
conjectures are proved; the expansion reading of the A258667 conjecture is
refuted at relative order `n^{−4}`, and the same conjecture in A258664–A258666
and A258673 is settled the same way (independent check); no claim of the
source was found false.

## Relation to the repository

No other file of the repository names A332709, A127548, A258667 or A000179.
The source credits the transseries volume and `Combinatorial_Transseries_Inverses`
for its inverse distinctions (compared in Remark 9.2). No result of another
report is shared, so no reciprocal note. No Lean or Rocq development in this
repository treats these sequences (the A258667 Lean file is external).

## Labels and numbering

All labels carry the prefix `fcm:`: the 60 delivered labels, prefixed before
anything cited them (48 references updated: 36 `\eqref`, 12 `\ref`), and the
write's three (`fcm:sec:provenance`, `fcm:rem:transseries`, `fcm:rem:oeis`);
63 in all. The write's remarks are the last statements of their sections and
its additions contain no numbered display or table, so every number is
delivered (checked against the `.aux` of a build of the delivered text: 60
labels, 0 differences). Section 1.2 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.2 with the false readings: `T`/`A` (`A(n,s)` is not an A-number),
`L`/`𝓛` (the centre difference is not `L_0`; `𝓛(S)` is a law), `U`/`𝓤`/`u`,
`R`/`𝓡`, `F`/`𝓕`/`Φ`, `S`/`E`, `h`/`q`/`s`/`k`, `m`/`N`/`M`, `X`/`ℓ`/`W`,
`x`/`c`/`C`, `a_n`/`D`/`J`/`K`.

## The write's additions

The status note after the abstract, Section 1.2 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 9.2 and
11.1, the dated notes after Table 1 and in Sections 10 and 12, the label
prefixes, the bibliography entry `TSvol`, and the `\file` macro and
`writenote` environment. Everything else is delivered text.

## Files

```text
README.md                                     this guide (replaces the delivered README.md)
SOURCES.md                                    the source's bounded source ledger
article.tex                                   the report (delivered Report221.tex, written)
article.pdf                                   compiled report, 20 pages
code/build.py                                 the delivered builder (checks, PDF, manifests, ZIP; delivered root)
code/check_exact.py                           deterministic exact tests and negative controls
code/diagnostics.py                           100-digit diagnostics, explicitly noncertifying
code/menage.py                                exact counts, rational coefficient engine, exact TV, guarded APIs
data/receipts-diagnostics.json                output of diagnostics.py (delivered receipts/)
data/receipts-exact.json                      output of check_exact.py (delivered receipts/)
data/receipts-exact_low_digit_cap.json        the same with PYTHONINTMAXSTRDIGITS=640 (byte-equal)
data/receipts-exact_low_digit_cap_optimized.json  the same under -O with the cap (byte-equal)
data/receipts-exact_optimized.json            the same under -O (byte-equal)
data/requirements.txt                         mpmath pin with comments (delivered root)
data/source_pins.json                         fingerprints of the sources the author read (delivered root)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery (the delivered root builder moved to `code/`,
the receipts and root data files to `data/`). Not shipped (retrievable from
`60f54ea06`): the delivered `Report221.pdf` (16 pages) and `README.md`
(replaced by this guide), and the pure checksum manifest `MANIFEST.sha256`
(15 entries, verified at the write).

```sh
git show 60f54ea06:docs/incoming/Report221.zip > <scratch>/r221.zip
```

**Delivered text that names the delivery layout.** `SOURCES.md`,
`data/source_pins.json` and Section 10 of the report describe the delivered
archive (`Report221.tex`, `receipts/`, `MANIFEST.sha256`, root `build.py`); a
dated note in Section 10 says what is shipped. `code/build.py` expects that
layout and runs only in a re-extracted archive.

**Third-party data.** `code/check_exact.py` and `code/menage.py` contain no
copied OEIS b-file; the receipts contain values the programs compute.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash):

```sh
T=$(mktemp -d); mkdir -p "$T/code"; cp code/menage.py code/check_exact.py code/diagnostics.py "$T/code/"
D=$PWD/data; cd "$T"
py -B code/check_exact.py > exact.json                                   # standard library only
py -B -O code/check_exact.py > exact_optimized.json
PYTHONINTMAXSTRDIGITS=640 py -B code/check_exact.py > exact_low_digit_cap.json
PYTHONINTMAXSTRDIGITS=640 py -B -O code/check_exact.py > exact_low_digit_cap_optimized.json
py -B code/diagnostics.py > diagnostics.json                             # mpmath 1.3.0
for f in exact exact_optimized exact_low_digit_cap exact_low_digit_cap_optimized diagnostics; do
  cmp <(tr -d '\r' < $f.json) <(tr -d '\r' < "$D/receipts-$f.json") && echo "same $f"; done
```

At the write (7 October 2026, Windows, Python 3.14.4) all five outputs
equalled the shipped receipts after removing carriage returns (about 8 s in
all). The builder was not run.

## Build

pdfLaTeX (lmodern, inputenc, amsmath, amssymb, amsthm, mathtools, booktabs,
array, longtable, geometry, microtype, xurl, hyperref, enumitem, fancyhdr). In
a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was rebuilt at the independent check from this file with
MiKTeX pdfLaTeX (three passes, 7 October 2026): 20 pages (the write's: 19); no errors or warnings, no undefined references, no
multiply defined labels, no duplicate destinations, no overfull or underfull
boxes. The delivered text gives 16 pages with the same clean log.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 221 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: OEIS A332709, A127548, A000179, A258667;
  Shevelev–Moses (2016); Kaplansky–Riordan (1946, through Wyman–Moser);
  Wyman–Moser (1958); Kagey (arXiv 2023; DAM 2024 not read); Gu–Zhao (2021,
  abstract only); the AlphaProof Nexus A258667 Lean file; the repository's two
  transseries volumes; and the transseries volume as `TSvol` (added by the
  write).
