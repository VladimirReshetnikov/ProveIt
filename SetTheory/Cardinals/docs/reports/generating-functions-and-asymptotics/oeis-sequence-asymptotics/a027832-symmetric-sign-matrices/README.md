# Symmetric Sign Matrices and Free Degree Constraints (OEIS A027832)

**`A_n ~ 2^{n(n+1)/2} q^n Z_0 e^{−ℓ²/2} · {exp(ℓ√n + J/4), n even; 1, n odd}`
for symmetric `{−1,+1}` matrices with nonnegative row sums, where
`φ(ℓ) = ℓΦ(ℓ)`; removing `f = O(√M)` degree caps near half the order
multiplies the all-capped graph count by `Φ(ℓ)^{−f}` times an explicit
collective correction; and a continuous inverse with eventual two-ceiling
threshold brackets**

A research article ("Report 239" of a session bundle), built from one
manuscript dated 5 October 2026. Its author line and PDF author field read
"Report 239": it names no person, tool or addressee. The phrase "private
review" occurs in the package only in sentences saying that such material is
not included (Section 10 of the article and `SOURCES.md`; the delivery README
likewise excludes "private audit files"). The delivery README's build
commands used generic example paths; they are not reproduced here.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 239 (batch 108) | `Report239.zip` (31 files in a wrapper directory `Report239/`, 567,302 bytes, SHA-256 `01d2635f…4d80c1d9`), arrival commit `60f54ea06`; main file `article.tex` with 12 files `sections/*.tex` (792 lines, 19 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes sign matrices, degree-capped graph counts or the
McKay–Wanless–Wormald asymptotics. No proof uses a floating-point
computation.

## Trust boundaries

- **What is imported, cited and not reproved.** McKay–Wormald's dense
  degree-sequence enumeration (Eur. J. Combin. 11 (1990), Theorem 3(ii), with
  uniformity from their Theorem 2; Theorem 3.1 here). McKay–Wanless–Wormald
  (CPC 11 (2002)): Corollary 2, the all-capped count, which supplies the
  constants `q`, `Z_0`, `J`, the exponential rate and the square-root
  boundary effect of the matrix theorem; and Lemma 2 and equation (29), the
  quantitative finite-saddle estimates (8.2)–(8.3). The diagonal-to-extra-
  vertex correspondence is credited to Greenhill–McKay (LAA 436 (2012)).
- **What the write checked.** It read the McKay–Wanless–Wormald statements
  used (authors' final version, pp. 3, 6, 11–14) and the Greenhill–McKay
  correspondence (arXiv:1103.0080v3, p. 3) and found them as the source
  quotes them, including the identification of their saddle equation with
  the source's (details in Section 1.2 of the article). It did **not** read
  the 1990 McKay–Wormald paper: the hypotheses and uniformity of Theorem 3.1
  as stated are the source's reading (Question 1).
- **What the source proves.** The graph bridge (with proof), the relative
  concentration under mixed caps (an unequal-cap switching argument derived
  in full), the capped-binomial sub-Gaussian bound, the exact tilt and its
  uniform integrability, the parity balancing, and hence the transfer
  theorem from all-capped to mixed capped and free coordinates; the matrix
  equivalent then follows from the imported all-capped count.
- **The package** regenerates all 17 OEIS terms by an exact recursion,
  checks small cases by literal enumeration, encloses `ℓ`, `Φ(ℓ)^{−1}` and the
  other constants in rational intervals, and prints noncertified binary64
  diagnostics. It proves nothing asymptotic.

## What it proves

`A_n` counts symmetric `n × n` matrices with entries `±1`, diagonal included
and variable, whose row sums are all nonnegative (positions labelled;
`A_0 = 1`). `U_f(M,k)` counts graphs on `[M]` whose first `M − f` degrees are
at most `k`, `B = U_0`. Statement numbers are the delivered ones.

- **Proposition 1.1 (`ssm:prop:bridge`)**: `A_n = U_1(n+1, ⌊n/2⌋)`, and the
  soft-boundary formula `A_n = 2^n Σ_{Δ(G)≤k} 2^{−N_k(G)}`.
- **Theorem 2.1 (`ssm:thm:transfer`)**: for bounded `k − M/2` and
  `0 ≤ f ≤ C√M`, uniformly,
  `U_f/B = (1+o(1)) S_M^{−f} exp{ℓ²f²/(2(1+2ℓ²)M)}`
  `= (1+o(1)) Φ(ℓ)^{−f} exp{−(2θ_Mℓ/(1+2ℓ²)) f/√M + ℓ²f²/(2(1+2ℓ²)M)}`,
  `θ_M = k − M/2 + 1`; in particular `U_f/B ~ Φ(ℓ)^{−f}` for `f = o(√M)`.
- **Theorem 2.2 (`ssm:thm:matrix`)**: the display at the top, with
  `q = Φ(ℓ)e^{−ℓ²/2} = 0.61023…`, `Z_0 = exp(5ℓ²/4 − ℓ⁴/2)/√(1+2ℓ²) = 1.08387…`,
  `J = −4ℓ²/(1+2ℓ²) = −0.67740…`, `ℓ = 0.50605446898…`; each a relative
  `1 + o(1)` statement along its parity. (The write first printed
  `Z_0 = 1.08388…` and `J = −0.67741…`, roundings rather than truncations of
  `1.0838783…` and `−0.6774080…`; corrected after the independent check
  below. The article's own values in Section 2 are correct.)
- **Lemmas 3.2, 4.1, 5.1, 6.1, 6.2 and Corollary 5.2**: graphicality in the
  window, relative concentration, the capped-binomial variance and
  moment-generating bounds, the finite saddle, the product-model limits and
  exponential-square uniform integrability.
- **Proposition 9.1 (`ssm:prop:inverse`)**: the continuous inverse `r_s` of
  `F_s(t) = at² + bt + sℓ√t + c_s` satisfies `r_s(log A_n) = n + o(n^{−1})`
  and a four-term model expansion in `u = √(y/a)`.
- **Proposition 9.2 (`ssm:prop:threshold`)**: for every `ε > 0` and all large
  `x`, `⌈r_s(log x − ε)⌉_s ≤ N_s(x) ≤ ⌈r_s(log x + ε)⌉_s` (parity ceilings).

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.2 (`ssm:rem:oeis`)**: the OEIS entry, the historical table, and
  the leading formula against the 17 terms (next section).
- **Remark 9.3 (`ssm:rem:transseries`)**, with a proof: `A_{n+1} > A_n` for
  every `n ≥ 1` (`A_0 = A_1 = 1`), so `min(N_0, N_1)` is exactly the
  staircase `N_*` of `p0:def:three-inverses` (an **instance**, `n_1 = 1`),
  and the parity ceiling is exactly the residue-class ceiling of
  `p0:eq:residue-staircase` (`r = 2`, `ρ = 1 − s`). `F_s` is an admissible
  core in the sense of `p0:def:core` on `(max{1, |b|/log 2}, ∞)`, so `r_s` is
  its core solution (an **instance** of the definition), but neither of the
  two Lambert cores applies (no logarithm, no Lambert function). The
  four-term expansion (9.6) is an **instance of `p0:thm:core-reversion` after
  the change of variables** `t_vol = u^{−1/2}`, `r_s = u(1+E)`
  (`Λ = 2`, `h(w) = w²`; coefficients checked in SymPy); the analytic
  remainder is the source's. Proposition 9.2 and the rounding consequence of
  (9.5) are **analogues only** of `p0:thm:staircase` (2)–(4): `r_s` is not an
  interpolated inverse and the brackets come from two envelopes.
- **Section 12 (`ssm:sec:further`)**: the open questions.
- Section 1.2 (`ssm:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, reading
  conventions, collected non-claims), a status note after the abstract, and
  the note on the restored text in Section 7.

## The OEIS entry and the data

The live entry A027832 (revision #6, 12 November 2018, read 6 October 2026;
the revision the source inspected) is named, verbatim,

    Number of symmetric {-1, +1} matrices of order n with nonnegative row and column sums.

Its 17 data terms (offset 1) equal `data/oeis_prefix.json`, and the exact
recursion regenerates all of them. The entry has an example (`A(2) = 5`),
two references (Anderson, *Combinatorics of Finite Sets*, Ch. 3.1; "Torsten
Sillke and Achim Flammenkamp, unpublished") and a link to Greene–Kleitman;
it has no formula, program or asymptotic statement, so Theorem 2.2 is the
only asymptotic for A027832 in the entry or the repository. Nothing in the
entry is corrected; nothing was submitted to the OEIS.

The write fetched Flammenkamp's table (the source's [5]) on 6 October 2026:
"number of symmetric 0-1-matrices with each row- and columnsum >= n/2" for
`n = 1, …, 16`, equal to `A_1, …, A_16` (a row with `j` entries `+1` has sign
sum `2j − n`).

**The leading formula against the data** (the intake's numbers, batch-108
dossier, 40-digit mpmath; rerun by the write; the delivered noncertified
`data/diagnostic_receipt.json` agrees to the digits shown): `A_n` divided by
the right side of (2.6) is

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| ratio | 0.85922 | 1.01920 | 1.00947 | 1.00152 | 0.99615 | 1.00043 | 0.99616 | 1.00005 | 0.99682 |

| n | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
|---|---|---|---|---|---|---|---|---|
| ratio | 0.99985 | 0.99733 | 0.99974 | 0.99771 | 0.99967 | 0.99800 | 0.99963 | 0.99822 |

So the matrix theorem matches all 17 terms to within 0.4 % from `n = 5`:
0.9996 at `n = 16` and 0.998 at `n = 17`, which the intake read as tending
to 1 on both parities. In detail, the odd-order ratios increase from `n = 5`;
the even-order ratios stay within `4.4·10^{−4}` of 1 from `n = 6`, cross 1
between `n = 8` and `n = 10`, and from `n = 8` to `n = 16` move slowly away
from 1. Seventeen terms neither confirm nor contradict an `o(1)`; the
theorem gives the limit 1 on each parity with no rate and no sign
(Question 3).

## The delivered typesetting defect

`sections/07_transfer.tex` was delivered with two carriage-return bytes (at
offsets 4435 and 5322) where the two characters `\r` of `{\rm even}` had been
converted, so the delivered PDF printed "meven" in the subscript of the
parity indicator in (7.10) and in the display of `P(E_f)` in Section 7.4.
The placement staged the bytes unchanged under a `-text` line in
`SetTheory/Cardinals/.gitattributes`. The write restored `{\rm even}` in both
places (LF line endings, a dated `[write]` note in Section 7), and removed
that `-text` line, since the file no longer contains a CR byte; no file of
this report now contains one. This is the only change to the source's text
besides the label prefixes and the marked additions.

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.2):

- Both theorems are leading `1 + o(1)` statements: no rate, no higher count
  coefficient, no all-orders expansion, no numerically certified starting
  index; the auxiliary estimate (8.4) does not strengthen the qualitative
  error.
- The all-capped equivalent and its constants are McKay–Wanless–Wormald's,
  the bridge is Greenhill–McKay's; "broad partial-constraint ideas and the
  graph bridge are not presented as new", and the article "makes no priority
  claim".
- McKay–Wanless–Wormald's comparison theorem (their Theorem 3) is not applied
  to the weight `2^{−N_k}`.
- Nothing for `f/√M → ∞`, nonuniform caps beyond bounded offsets, or deleted
  or fixed diagonals.
- No certified finite-input rounding rule; Proposition 9.2 holds beyond an
  ineffective threshold.
- The historical search was bounded (Anderson and the unpublished
  Sillke–Flammenkamp work not inspected): "These are precise limits on the
  inspected historical record, not evidence that no earlier unpublished
  result exists".
- The constant certificate covers constants only; the diagnostics are
  noncertified; the manifest gives "integrity, not authorship or independent
  provenance"; the guards are not a sandbox; reproduction is claimed for the
  recorded toolchain only.

The write adds: Theorem 3.1's hypotheses and uniformity are the source's
reading of a paper the write did not read.

## Further questions

Section 12 of the article (`ssm:sec:further`) states every claim of the
source that is not proved in full as an open question with its source,
sketch and what is missing (Vladimir's standing rule of 4 October 2026). The
source's own five questions (Section 11: an effective remainder, higher
coefficients, `f ≫ √M`, nonuniform caps, the historical identification) stay
as printed. **Nothing in the source was found to be wrong**, and no claim
was narrowed.

1. **The imported enumeration input** (`ssm:q:inputs`): the hypotheses and
   uniformity of McKay–Wormald's Theorem 3(ii) as quoted, not checked against
   their 1990 paper; everything else imported was checked.
2. **The historical record** (`ssm:q:history`): Flammenkamp's table confirmed
   through `n = 16`; open whether Anderson's §3.1 or the unpublished
   Sillke–Flammenkamp work states an asymptotic.
3. **The next term and the parity pattern** (`ssm:q:parity`, added by the
   write, not a claim of the source): is there a second term, for instance of
   relative order `n^{−1/2}` with a parity-dependent coefficient, explaining
   the pattern of the table above?

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4):
  the 29 staged files are byte-identical to a fresh extraction of the
  archive; `MANIFEST.sha256` 30/30. The dossier read the manuscript in full
  and found no error. On a copy, `build.py --verify-only` verified 30 files;
  `exact_counts.py` and `constant_certificate.py` reproduced
  `count_receipt.json` and `certificate_receipt.json` byte for byte after
  converting line endings; `diagnostics.py` reproduced
  `diagnostic_receipt.json` except in the last one or two digits of three
  binary64 values (below); `guard_tests.py` stops on Windows at its own path
  guard; the PDF and ZIP rebuilds were not run. It evaluated the leading
  formula against all 17 terms (table above) and found the stray CR bytes.
- **Diagnostic values that differ on rerun.** In `diagnostic_receipt.json`,
  the three values `exact_over_S_based_model` at `M = 13`, `f = 1, 3, 6`
  (lines 126, 134, 142) come out as `0.9974125574751151`,
  `0.9826408876797486`, `0.9514709260683462` on the intake's Windows machine
  against the delivered `…751156`, `…797499`, `…683487` (relative differences
  below `3·10^{−15}`). The receipt labels itself
  `NONCERTIFIED_FLOATING_DIAGNOSTICS` computed with "Python binary64 float and
  platform libm"; these are platform floating-point differences, and nothing
  in the article depends on them. All other diagnostic values, and every
  exact count and certified interval, reproduce exactly.
- At the write (6 October 2026; same machine): Route B below reproduced the
  count and certificate receipts and the same three last-digit differences;
  the live OEIS entry is still revision #6 with the same 17 terms; the
  historical table matches through `n = 16`; the write rechecked by hand the
  bridge, `q^{n+1}/Φ(ℓ) = q^n e^{−ℓ²/2}`, `a²/(1−2v) = ℓ²τ²/[2(1+2ℓ²)]`, the
  switching gain (4.5), the tail bound (5.3) and the coefficients of (9.6),
  verified the change of variables and reversion coefficients of Remark 9.3
  in SymPy 1.14.0, and checked that `α(r)` of McKay–Wanless–Wormald (22) is
  half the mean of the capped sum.
- Sources read by the write: the OEIS entry; the Flammenkamp table;
  McKay–Wanless–Wormald, authors' final PDF (Corollary 2, Lemma 2, equations
  (1), (17)–(30)); Greenhill–McKay, arXiv:1103.0080v3, p. 3; the transseries
  volume (`p0:def:core`, `p0:thm:lambert-core`, `p0:prop:factorial-core`,
  `p0:thm:core-reversion`, `p0:def:three-inverses`, `p0:thm:staircase`). Not
  read: McKay–Wormald 1990; McKay–Wanless–Wormald's Theorem 3, Lemma 4 and
  (14); Greenhill–McKay's Theorem 1.4; Anderson; Greene–Kleitman;
  Dandi–Gamarnik–Zdeborová; Minzer–Sah–Sawhney; Liebenau–Wormald.
- **Independent check of the write (6 October 2026).** An adversarial check
  made by the intake after the write (`b5026035f`), with its own code, after
  fetching the OEIS entry, Flammenkamp's table, McKay–Wanless–Wormald's
  final version and Greenhill–McKay v3 again. Remark 1.2: the entry and the
  table as quoted; literal enumeration gives `A_1, …, A_5`; all 17 ratios
  reproduced with `ℓ` at 50 digits, and every statement about them (even
  ratios within `4.34·10^{−4}` of 1 from `n = 6`). Section 1.2: Corollary 2
  (`ζ_0, …, ζ_4` recomputed, `ζ_1 = q`), Lemma 2, (1), (17)–(18), (22),
  (26), (29) as read, and `α(r) = (M/2)μ_M(r)` identically in exact
  rationals (`6 ≤ M ≤ 15`); Greenhill–McKay p. 3 as quoted; the two carriage
  returns at offsets 4435 and 5322. Remark 9.3 (1)–(4) re-derived (the
  admissible-core clauses, the exact master equation, `e_1, …, e_4` by
  SymPy). For the record, the remark does not name `plt:thm:lw-template`:
  with `Z = √t`, `H = (F_s/a)^{1/4}` the model equation is a degenerate
  instance of it (`μ = 0`, no logarithm) reproducing (9.6); nothing changes.
  Archive facts and the 74/67 label and reference counts confirmed. No error
  in the article; this README printed two roundings as truncations
  (`Z_0 = 1.08388…`, `J = −0.67741…`), corrected above with a dated note.
  The check is recorded at the end of Section 9.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns sign matrices or degree-capped
graphs. Placement in the collection confers no formal status.

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`):
see Remark 9.3 above (instances: the staircase definition, the admissible-core
definition, `p0:thm:core-reversion` after a change of variables; analogues
only: `p0:thm:staircase`). No novelty is claimed for the inversions.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a138178-symmetric-packed-matrices` (symmetric matrices, a different count
and method); `a005163-diagonally-symmetric-asms` (alternating sign matrices,
unrelated despite the name); `a110058-square-contingency-tables` and
`a197458-line-sum-two-matrices` (matrices with prescribed margins, through
Canfield–McKay and Greenhill–McKay–Wang respectively);
`a307316-leafless-multigraphs` (degree-sequence counts of sparse
multigraphs). None treats A027832, degree caps near half the order, or the
McKay–Wanless–Wormald count, and none needs a reciprocal note.

**Stale claims.** Before batch 108 no file of the repository named A027832;
the source made no claim about the repository.

## Notation

A table at the end of Section 1.2 fixes the letters the manuscript reuses,
with the tempting false readings: `ℓ` (not a logarithm; not `L_M`, `L_0(T)`);
`Φ, φ` against the volume's core `Φ_0`; `q` against the masses `q_j`, `q_x`;
`v` against the volume's `v`; `S_M` (McKay–Wanless–Wormald's `S(r,k)` at the
saddle); `θ_M` (their `τ`) against the source's `τ = lim f/√M`; `h`, `h_M`;
`f`; `N_k(G)`, `N_M(d)`, `N_s(x)` (and the staircase `N_*`); `B(M,k)`, `B`
against McKay–Wanless–Wormald's `B`; `a, b`; `t, u`; `r_M, r_s`; `D, Δ`;
`W_M` (no Lambert function occurs). Symbols of the volume carry the
subscript "vol" in Remark 9.3. No symbol was renamed.

## Labels

Every label carries the prefix `ssm:` (none existed in the repository). The
manuscript's 74 labels (`eq:` 51, `sec:` 11, `lem:` 5, `prop:` 3, `thm:` 3,
`cor:` 1) were prefixed before anything cited them, and the 67 references to
them updated. The write added 7: `ssm:rem:oeis`, `ssm:sec:provenance`,
`ssm:rem:transseries`, `ssm:sec:further`, and the questions `ssm:q:inputs`,
`ssm:q:history`, `ssm:q:parity`. The report has 81 labels; builds of the
delivered text and of this one give all 74 delivered labels the same numbers
(aux files compared). The added remarks are the last statements of their
sections, the added subsection and section follow the last delivered ones in
their places, and the added displays are unnumbered.

## Files

```text
README.md                        this guide (replaces the delivery README)
article.tex                      the report's main file (delivered; [write] macros and status note)
sections/01_model.tex            Section 1, Remark 1.2 and the write's Section 1.2 (provenance, notation, non-claims)
sections/02_results.tex          Section 2, the two theorems
sections/03_enumeration.tex      Section 3, the imported enumeration
sections/04_concentration.tex    Section 4, relative concentration
sections/05_binomial.tex         Section 5, the sub-Gaussian bound
sections/06_saddle.tex           Section 6, the saddle and the product model
sections/07_transfer.tex         Section 7, the transfer proof ({\rm even} restored, note)
sections/08_explicit.tex         Section 8, the explicit correction and the matrix constants
sections/09_inverse.tex          Section 9, inversion (and Remark 9.3)
sections/10_computation.tex      Section 10, exact computations and reproducibility
sections/11_outlook.tex          Section 11, scope and questions; Section 12 (the write's)
sections/12_references.tex       bibliography
article.pdf                      compiled report, 26 pages
COMPUTATION.md                   algorithms, bounds and certificate derivation (delivered at the root)
SOURCES.md                       source attribution and its limits (delivered at the root)
code/build.py                    manifest-verified build and deterministic ZIP (delivered at the root)
code/common.py                   input bounds and exclusive output (delivered code/)
code/constant_certificate.py     rational interval certificate for the constants (delivered code/)
code/diagnostics.py              NONCERTIFIED binary64 diagnostics (delivered code/)
code/exact_counts.py             exact capped-graph recursion and small-case checks (delivered code/)
code/guard_tests.py              API, CLI, filesystem, manifest and ZIP guard tests (delivered code/)
code/reproduce_zip.py            actual-ZIP replay (delivered code/)
data/certificate_receipt.json    receipt of constant_certificate.py (delivered code/)
data/count_receipt.json          receipt of exact_counts.py (delivered code/)
data/diagnostic_receipt.json     receipt of diagnostics.py (delivered code/)
data/guard_receipt.json          receipt of guard_tests.py (delivered code/)
data/oeis_prefix.json            the 17 OEIS terms, revision 6 (delivered code/)
data/requirements.txt            no third-party packages; Python 3.11+ (delivered at the root)
```

Every file except `README.md`, `article.tex`, `sections/*.tex` and
`article.pdf` is byte-identical to the delivery; of the `sections/` files,
`07_transfer.tex` differs from the delivered bytes by the restored `\r`
characters, the label prefixes and the note.

**Not shipped**, recoverable from the arrival commit (next section):
`Report239.pdf` (the delivered 19-page PDF, 396,203 bytes); `MANIFEST.sha256`
(2,629 bytes, 30 entries, verified at placement; repository policy ships no
checksum manifests); and the delivery `README.md` (5,822 bytes), staged at
placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`code/common.py` sets `ROOT` to the parent of `code/`; `exact_counts.py`
reads `ROOT/code/oeis_prefix.json`, shipped as `data/oeis_prefix.json`, so it
does not run under the shipped names (Route B). `code/build.py` takes its own
directory as the package root, reads `MANIFEST.sha256` there and expects the
receipts in `code/`; `guard_tests.py` and `reproduce_zip.py` use the
delivered names, `build.py` and the manifest. `COMPUTATION.md`, `SOURCES.md`
and Section 10.3 of the article speak of "the public package", the PDF, the
ZIP and "a SHA-256 manifest"; those are in the arrival archive only.
`guard_tests.py` stops on Windows at its own path guard (`common.py`
rejects backslash output paths), and the PDF/ZIP builder needs POSIX and the
delivering TeX toolchain.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report239.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 01d2635f9e9001da54f0fb0954ffa40ae54c6df18b8945de7839d0354d80c1d9, 567,302 bytes
cd "$T" && unzip -q a.zip && cd Report239 && sha256sum -c MANIFEST.sha256
```

The archive's `sections/07_transfer.tex` still has the two CR bytes.

## Rerun the checks (on a scratch copy)

Python 3.11 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout** (as the delivery README gives it, from
`$T/Report239`; on a POSIX host for the guard tests and rebuilds):

```sh
python3 -B build.py --verify-only        # 30 files verified
python3 -B code/exact_counts.py          # = code/count_receipt.json
python3 -B code/constant_certificate.py  # = code/certificate_receipt.json
python3 -B code/diagnostics.py           # = code/diagnostic_receipt.json (binary64; see above)
python3 -B code/guard_tests.py
python3 -B -O code/guard_tests.py
python3 -B build.py --output-dir "$(mktemp -d)/build"   # PDF, ZIP, receipts; byte identity needs the delivering toolchain
```

The intake ran the first five on Windows (outputs equal to the receipts after
converting CRLF, except the three diagnostic digits); `guard_tests.py`
stops there at its path guard, and the rebuild and ZIP replay were not run.

**Route B, from the shipped files, any OS** (tested at the write on Windows,
about 12 s in all):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a027832-symmetric-sign-matrices
B=$(mktemp -d); mkdir "$B/code"
cp "$R/code/common.py" "$R/code/exact_counts.py" "$R/code/constant_certificate.py" "$R/code/diagnostics.py" "$B/code/"
cp "$R/data/oeis_prefix.json" "$B/code/"
cd "$B"
python3 -B code/exact_counts.py         > ec.json   # = data/count_receipt.json
python3 -B code/constant_certificate.py > cc.json   # = data/certificate_receipt.json
python3 -B code/diagnostics.py          > dg.json   # = data/diagnostic_receipt.json up to binary64 digits
```

Use `py` where `python3` is not on the path. On Windows the outputs carry
CRLF line endings and equal the receipts after conversion. Outputs must go
to standard output or to a new file outside the copy (`--output`); the
programs refuse anything else.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr,
hyperref); the bibliography is embedded in `sections/12_references.tex`.

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, after
the independent check (25 pages at the write; label numbers unchanged, aux
files compared): 26
pages; no errors, no LaTeX or package warnings, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes. The delivered preamble's `\pdfmapfile` lines
make pdfTeX print 684 "fontmap entry … already exists, duplicates ignored"
notices, as many as in a build of the delivered text (19 pages, otherwise
clean). The delivered byte-identity claims apply to `Report239.pdf` under
the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the model (ordered
symmetric `±1` matrices, diagonal included, nonnegative row sums, offset 1,
empty matrix recorded separately) and the bridge; said the article "proves
leading relative asymptotics and the critical window for specified free
graph coordinates, conditional on its cited dense-enumeration input" (the
imported theorems above) and that the programs "do not establish an
effective asymptotic remainder, a numerical onset, or all-order
expansions"; listed the files under their delivery names; gave the build,
ZIP replay and individual-check commands of Route A (Python 3.11 or later,
new output directories outside the package, "Existing outputs are never
merged or replaced"); described the seven top-level build outputs, the
private TeX format with shell escape disabled, and the replay under normal
and optimized Python; stated the per-API bounds (n ≤ 17, M ≤ 18, k ≤ 8,
diagnostics M ≤ 2001, 20–40 certificate digits); and separated what is
certified (exact integers, rational intervals) from the NONCERTIFIED
diagnostics, adding that "this package is not a sandbox against hostile
concurrent filesystem changes".

## Rights

Repository contents are MIT-0. The article and `data/oeis_prefix.json` quote
the name and the 17 terms of OEIS A027832; OEIS content is published by The
OEIS Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. No third-party PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A027832 (revision #6); McKay–Wormald,
  Eur. J. Combin. 11 (1990) 565–580; McKay–Wanless–Wormald, CPC 11 (2002)
  373–392; Greenhill–McKay, LAA 436 (2012) 901–926; Flammenkamp's homepage
  and table; Anderson (1987), §3.1; Greene–Kleitman, JCTA 20 (1976) 80–88;
  Dandi–Gamarnik–Zdeborová, arXiv:2305.03591v2; Minzer–Sah–Sawhney, Ann.
  Probab. 52 (2024); and, in `SOURCES.md` only, Liebenau–Wormald, JEMS 26
  (2024). No source was added by the write.
- Batch 108 of `docs/incoming`, bundle Report 239; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `article.tex` and `sections/` are shipped under the
  same names; the delivered programs and data as listed above.
