# All Fixed Order Asymptotics for Restricted Two-Covers and Line Graphs (OEIS A060053, A014500)

**Restricted two-covers, proper restricted two-covers and labelled line
graphs: an exact-saddle expansion to every fixed order with a pure power
remainder, transfer through arbitrary signed polynomial exponential
multipliers, explicit Lambert-W coefficients with the logarithmic remainder
their growth requires, the first effect of identifying line images
(−r⁶/(48n³)), and inverse expansions with a precise separation between model
roots and certified integer thresholds.**

A single-source report: bundle Report 224 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The text calls itself
"Reconstructed edition 2" (5 October 2026); no earlier edition was delivered.
The author line reads "Research report 224" and the PDF author field
"Research report"; the manuscript names no person, tool or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *All fixed order asymptotics for restricted two covers and line graphs* ("Research report 224", 5 October 2026, reconstructed edition 2) | `Report224.zip` (621,206 bytes, 27 files, wrapper `Report224/`; `src/report224.tex`, 44 lines, with six `\input` files, 1,383 lines in all, 21 pp.) | `a4186a946` | `article.tex` and `sections/*.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. The corrected line-graph multiplier rests
on Cameron, Prellberg and Stark's classification of the exceptional roots
(Whitney, Sabidussi), which the source imports; every other theorem has a
conventional proof in the text.

## What the report proves

`H_n = e^{-1} Σ_m (M(m))_n/m!` with `M(m) = m(m−1)/2` is a positive weighted
count of restricted two-covers; `V_n` (A060053), `U_n` (A014500) and the
labelled line graphs `L_n` are its convolutions with `e^{−x/2}`, `e^{x/2}` and
`exp(x/2 − x³/6 − x⁴/4 − x⁵/8 − x⁶/48)`; `r = W(2n)`, `s = e^r = 2n/r`.

- Section 1: the Poisson sum (1), `H = e^{x/2}V`, `U = e^x V = e^{x/2}H` (2),
  an exact Bell-moment formula (3), the corrected multiplier (4) with the
  root/line-image counts of the exceptions, the table to `n = 6`, and why the
  legacy series `O = e^{−x³/6}U` (A132219) cannot count line graphs
  (`O_4 = 66 > 2⁶`).
- **Theorem S1:** at the exact saddle, `H_n = e^{f_n(τ)−1}√(2π) σ (Σ_{ℓ≤K}
  C_ℓ + O_K(n^{−K−1}))` for every fixed `K`, with no positive power of `r` in
  the remainder; Proposition S2: growth and the adjacent ratio
  `H_{n−1}/H_n ~ r²/(2n²)`; (S21a) `H_n = S_n(1 + O(r⁴/n))`.
- **Theorem S3:** arbitrary fixed real (signed) polynomial multipliers: the
  convolution is its first `K+1` shifts up to `O(H_n (r²/n)^{K+1})`, the far
  tail super-polynomially small; a pure power error by one extra shift.
- **Theorem C1:** Lambert expansions `A_P(n) = S_n(Σ_{j≤J} a_{P,j}(r)/n^j +
  O((1+r)^{4J+4}/n^{J+1}))` with rational `a_{P,j} = O(r^{4j})` from a finite
  algebraic prescription (C3)–(C6); explicit `a_{P,1}`, `a_{P,2}` for
  `H, V, U, L`, the exact-Bell-normalized `v_1, v_2`, `v_3 ~ r¹²/663552`
  (so the remainder after `v_2/n²` is not `O(n^{−3})`), `a_{L,3} − a_{U,3} =
  −r⁶/48` and `L_n/U_n = 1 − r⁶/(48n³) + O(r¹⁶/n⁴)`.
- Section 4: the model inverse `N = x_0 + h_0(r_0)/(2r_0 − log 2) +
  O(r_0³/x_0)` (C19), a second correction (C20), every fixed order (C22), a
  Lambert seed (C23), and why arbitrary thresholds need a true-sequence
  enclosure.

(Section, equation and tag numbers are those of the committed PDF; the
source's theorems are named in bold type, not numbered environments.)

## What the report does not claim

The exact identities, the Poisson sum, the exception classification and the
leading equivalent are prior (Cameron–Prellberg–Stark); the classification is
used as a known theorem, and the small enumerations validate its consequences,
not its completeness. No worldwide novelty or priority for the higher-order
refinements; nothing is attributed to OEIS. Software caps are implementation
limits, not limits of the theorems; floating diagnostics are not interval
certificates; no effective constant or onset; a model root does not certify
an arbitrary threshold; the threshold scan is not an unbounded inverse oracle;
byte reproducibility only for the same toolchain.

## The write's findings

- **The OEIS entries** (Remark 2): A060053 (#51, 30 May 2026, Vladeta
  Jovovic; b-file by Robert Gerbicz, n = 0..100) and A014500 (#52, 30 May
  2026, Simon Plouffe and Gilbert Labelle; b-file by Alois P. Heinz, n =
  0..100) quoted; neither has an asymptotic formula or a conjecture, as the
  source says. **A132219** (#5, 7 July 2015, Jovovic), "Number of line graphs
  on n labeled nodes.", has the e.g.f. `e^{−x³/6}U(x)` of the arXiv
  version 1 of Cameron–Prellberg–Stark; its terms do not match its name
  (`a(4) = 66 > 64`; the true `L_4 = 60`, since on four vertices only the four
  claws are not line graphs). The corrected sequence 1, 1, 2, 8, 60, 729,
  11600, 228443, … is not in the OEIS. **A094089** (#13, Jovovic; b-file by
  Heinz, n = 0..150) is `2^n H_n`, which the source tabulates without naming.
  All b-file terms of the four entries equal the write's computation. No OEIS
  edit.
- **Cameron–Prellberg–Stark read:** the corrected author manuscript and arXiv
  version 1, retrieved from the ledger's URLs, have the ledger's SHA-256
  values; Proposition 3 (p. 5), the corrected Proposition 5 (p. 6, the
  multiplier of (4)), (18) (p. 16), (21)–(27) (pp. 17–18), the formula for
  `L(x)` and the referee acknowledgement (p. 19), and version 1's
  `L = e^{−x³/3!}U` are as cited.
- **Recomputed with the write's own code:** `H_n` by two exact routes
  (forward differences without Bell numbers, n ≤ 120; formula (3), n ≤ 300);
  `V, U, L, O` integral and equal to the table and all b-files; **restricted
  two-covers enumerated from the definition for n ≤ 7**, giving `U_7 =
  233238`, `V_7 = 163356` and `L_7 = 228443` as the number of distinct
  labelled line images (one edge beyond the source's endpoint check, and
  without the exception classification); the exceptional root/image counts;
  **every Lambert coefficient through order 3** for `H, V, U, L` and the Bell
  normalization by its own SymPy expansion of the saddle sum (equal to the
  printed ones and to `data/coefficients_order3.json`), `E_1`, `E_2`, `v_1`,
  `v_2`, `v_3`, (C16), (S3), (C17), the `d_1` cancellation in (C20) and the
  seed (C23) (next term `b²/(2w⁴)`, so its `O(w^{−4})` is sharp); the
  expansions against the positive sums at n = 10⁴…10⁷ (each remainder
  approaches the next coefficient); the `n = 1000` table (correct roundings;
  truncations in a dated note).
- **How slowly `v_3` reaches its leading term** (dated note, Section 3.4):
  `v_3 ~ r¹²/663552` is right, but `v_3(W(2n)) < 0` for 2190 ≤ n ≤ 130671 and
  `v_3/(r¹²/663552)` reaches 1/2 only near `n ≈ 1.2·10¹¹`; the source's bound
  `O(r¹²/n³)` is the safe reading.
- **Remark 1 (transseries volume):** growth outside `p0:def:model`; in the
  variable `r_0 = W(2x_0)` the model equation is literally the volume's
  monomial–logarithmic equation (`plt:def:lw-monomial-log-datum`, slope 1,
  logarithmic coefficient 2), so the formal expansion of `r_0` is an exact
  instance of `plt:thm:lw-template`, and the seed `w` an exact instance of
  `p0:thm:lambert-core`; the index refinements (C19)–(C22) lie below every
  order of the template's chart and are proved directly; (C22) and the
  bracket of Section 4.3 are analogues of `p0:thm:staircase`(3) and (2), not
  instances.

## Independent check of the write (7 October 2026)

An independent adversarial check of the batch-113 write (`43e0c9a22`) used
its own code.

- **Checked hardest: A132219 cannot count line graphs.** All labelled graphs
  on n ≤ 7 vertices were enumerated from the networkx graph atlas (1,252
  unlabelled graphs, weighted by n!/|Aut|, so all 2^C(n,2) are covered). Each
  was tested by two independent line-graph recognitions (van Rooij–Wilf, and
  networkx's inverse-line-graph algorithm), which agree everywhere. This route
  uses neither root graphs nor the exception classification. It gives
  1, 2, 8, 60, 729, 11600, 228443 for n = 1..7, equal to (4) and to the
  write's root enumeration. So `a(4) = 66` is impossible and the true value is
  60. Among n ≤ 12, `O_n > 2^C(n,2)` only at n = 4. The OEIS searches for the
  corrected terms return nothing.
- **OEIS and sources.** The four entries were read again live; the revisions,
  authors, names and b-file ranges quoted in Remark 2 are verbatim. An own
  exact `H_n` (Newton differences, no Bell numbers) reproduces every b-file
  term: A094089 as `2^n H_n` (151 terms), A060053 and A014500 (101 each) and
  A132219 (18). The shipped b-files equal the live ones. Both
  Cameron–Prellberg–Stark PDFs, fetched again, have the ledger's SHA-256
  values, and every cited locator was confirmed.
- **Numbers.** Recomputed: the `n = 1000` table, its truncations and the
  `n = 20` values; the Lambert remainders for H, V, U, L at n = 10⁴…10⁷ and
  every ratio quoted in Section 1.5; the roots of the `v_3` numerator (exact
  isolation) and the values of `v_3/(r¹²/663552)`; the first-order formula;
  (C17); the exact form of Φ(x_0); the seed (C23) with next term `b²/(2w⁴)`.
  All agree.
- **Transseries.** Remark 1 was checked against the volume's statements. The
  reading `(ρ, μ, β) = (1, 2, 0)` over ℚ(log 2) for `plt:def:lw-monomial-log-datum`,
  `p0:thm:lambert-core` with slope 1 and coefficient 2, and the staircase
  analogues are confirmed.
- **Precisions added (bracketed dated notes).**
  - Remark 1(3): the relative change is of order `e^{−r_0}`, not
    `r_0 e^{−r_0}`, since `d_0 ~ r_0/8` and `x_0 = r_0 e^{r_0}/2`. The
    conclusion is unchanged.
  - The `v_3` note of Section 3.4: `v_3(W(2n)) < 0` also for n ≤ 3 and for
    37 ≤ n ≤ 235. The printed interval is the last of three. The sign of the
    numerical remainder at n = 10⁴…10⁷ agrees.
- **Also confirmed.** The provenance figures (621,206 bytes, 27 files, 44 and
  1,383 lines, 21 pages, 24 manifest entries); the byte identity of the staged
  files; the README listing; and the numbering: 47 delivered labels, 0
  differences against the `.aux` of a build of the placed text, 51 tags
  unchanged.

No claim of the write was found wrong. The check is recorded at the end of
Section 1.5.

## Further questions, and the standing rule

Section 6 (the source's six questions: effective enclosures, growing orders,
exponential lattice corrections, further graph observables, uniform inverse
computation, source history), with a dated note under Vladimir's standing
rule of 4 October 2026; added from the non-claims: an independent proof of the
completeness of the exception classification, interval certificates for the
diagnostics, and the OEIS correction of A132219 (not part of this work). No
claim of the source was found false; nothing is refuted.

## Relation to the repository

No other file of the repository names A060053, A014500, A132219 or A094089.
`a307316-leafless-multigraphs` cites Cameron–Prellberg–Stark for the
labelled-edge multigraph reading of two-covers, for different objects
(unlabelled leafless loopless multigraphs); no shared result, so no reciprocal
note. No Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `tcl:`: the 47 delivered labels (5 equations, 19
Pandoc section labels, 23 tagged equations (C1)–(C23)), prefixed before
anything cited them (3 `\eqref` updated), and the write's three
(`tcl:sec:provenance`, `tcl:rem:transseries`, `tcl:rem:oeis`); 50 in all.
The write's remarks are the last statements of their sections and its
additions contain no numbered display, so every number and tag is delivered
(checked against the `.aux` of a build of the delivered text: 47 labels, 0
differences; the 51 `\tag`s unchanged). Section 1.5 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.5 with the false readings: `a`, `a_j`, `a_{P,j}`; `b`, `b_j`; Bell `B_k`
versus Bernoulli `𝖡_k`; `c_k = p_j`; `E` (exponent, its finite version, and
the error bound `E_J(k)` of Section 4.3); `F_p`/`F_J`; `H`/`h`/`h_0`; `L`;
`M`/`m`; the legacy series `O` versus the Landau symbol; `Q`/`q`; `r`, `s`,
`S_n` (defined twice, equal); `x`; `Y`/`y`.

## The write's additions

The status note after the abstract, Section 1.5 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 1 and 2,
the dated notes in Sections 1.3, 3.4, 5.2, 5.3 and 6, the label prefixes, the
bibliography entry `TSvol`, the `\file` macro and `writenote` environment,
and the six `\input` paths (`sections/…`). Everything else is delivered text.

## Files

```text
README.md                          this guide (replaces the delivered README.md)
SOURCE_LEDGER.md                   the source's ledger: retrieved sources, hashes, locators, coverage limits
article.tex                        the report's main file (delivered src/report224.tex, written)
article.pdf                        compiled report, 26 pages
code/build.py                      delivered root builder: manifest check, tests, pdfLaTeX, deterministic ZIP
code/check_saddle.py               mpmath exact-saddle diagnostics (n = 2..10000, order <= 3)
code/endpoint_check.py             enumeration of partitions of the 2n labelled endpoints (n <= 6)
code/exact_counts.py               exact H, V, U, L, O by formula (3); finite threshold scan (n <= 640)
code/generate_coefficients.py      SymPy implementation of (C3)-(C6), orders 0..3
code/test_exact.py                 regression tests against the fixtures and the retrieved b-files
code/verify_coefficients.py        checks of the displayed coefficients and cross-order identities
data/build_checks.json             delivered build receipt (root build_checks.json)
data/coefficients_order2.json      generated coefficients through order 2
data/coefficients_order3.json      generated coefficients through order 3
data/endpoints6.json               endpoint enumeration n = 0..6
data/exact80.json                  exact fixture, five models, n = 0..80
data/saddle_diagnostics.json       80-digit exact-saddle diagnostics (not certificates)
data/sources-A014500_bfile.txt     retrieved b-file of A014500 (delivered sources/A014500_bfile.txt)
data/sources-A060053_bfile.txt     retrieved b-file of A060053 (delivered sources/A060053_bfile.txt)
data/sources-A132219_bfile.txt     retrieved b-file of A132219 (delivered sources/A132219_bfile.txt)
sections/coefficients.tex          Section 3 (delivered src/coefficients.tex, written)
sections/computation.tex           Sections 5-6 (delivered src/computation.tex, written)
sections/inverses.tex              Section 4 (delivered src/inverses.tex, written)
sections/models.tex                Section 1 (delivered src/models.tex, written)
sections/references.tex            bibliography (delivered src/references.tex, written)
sections/saddle.tex                Section 2 (delivered src/saddle.tex, labels prefixed)
```

Every file except `README.md`, `article.tex`, `article.pdf` and
`sections/*.tex` is byte-identical to its delivery (the root `build.py` moved
to `code/`, `build_checks.json` and the b-files to `data/`, the ledger to the
root). Not shipped (retrievable from `60f54ea06`): the delivered
`Report224.pdf` (21 pages), `MANIFEST.sha256` (24 entries, all verified at the
write) and the delivered `README.md` (replaced by this guide).

```sh
git show 60f54ea06:docs/incoming/Report224.zip > <scratch>/r224.zip
```

**Delivered text that names the delivery layout.** `SOURCE_LEDGER.md` and
Section 5.3 name `src/report224.tex`, `sources/` and a root `build.py` (a dated
note in Section 5.3 says what is shipped). `code/test_exact.py` reads the
b-files from `sources/`, and `code/build.py` verifies the delivered manifest,
so the builder runs only in a re-extracted archive.

**Third-party data.** The three `data/sources-*_bfile.txt`, `data/exact80.json`
and `code/test_exact.py` contain OEIS terms (CC BY-SA 4.0,
https://oeis.org/LICENSE). Cameron–Prellberg–Stark's PDFs are not shipped.

## Rerunning the checks (on scratch copies)

The tests expect the delivered `sources/` directory. From this directory (Git
Bash), rebuild that layout in a scratch directory:

```sh
T=$(mktemp -d); mkdir -p "$T/code" "$T/data" "$T/sources"
cp code/*.py "$T/code/"; cp data/*.json "$T/data/"
for f in data/sources-*_bfile.txt; do b=$(basename "$f"); cp "$f" "$T/sources/${b#sources-}"; done
cd "$T"
py -B code/test_exact.py --cap 640 && py -B -O code/test_exact.py --cap 640   # standard library only
py -B code/endpoint_check.py --max-index 6                                     # compare with data/endpoints6.json
py -B code/verify_coefficients.py                                              # SymPy 1.14.0
py -B code/generate_coefficients.py --order 3 --out "$T/coef3.json"            # compare with data/coefficients_order3.json
py -B code/check_saddle.py --ns 20 50 100 200 500 1000 --dps 80 --order 3 --output-dir "$T/saddle"   # mpmath 1.3.0
```

At the write (7 October 2026, Windows, Python 3.14.4) both test runs passed
and printed exactly the `exact` block of `data/build_checks.json`; the
endpoint output equals `data/endpoints6.json`; the verifier passed its 28
identity checks; the generated order-2 and order-3 files equal the shipped
ones; `check_saddle.py` reproduced `data/saddle_diagnostics.json` exactly. The
PDF/ZIP builder was not run.

## Build

pdfLaTeX (geometry, fontenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, array, microtype, hyperref, bookmark). In a scratch copy:

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built from these files with MiKTeX pdfLaTeX (three
passes, 7 October 2026): 26 pages; no errors or warnings, no undefined
references, no multiply defined labels, no duplicate destinations, no
overfull or underfull boxes. The delivered text gives 21 pages, equally clean.
(Under MiKTeX, the delivered `\pdfmapfile{+lm.map}` lines produce 684 pdfTeX
notices of duplicate font-map entries, both in the delivered and in the written
build. These are not LaTeX warnings.) The independent check rebuilt the PDF on
7 October 2026, three passes: 26 pages, equally clean, label numbers unchanged.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 224 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: Cameron, Prellberg and Stark, Discrete Math.
  310 (2010) 230–240 (corrected author manuscript; arXiv:0707.0664v1); OEIS
  A060053, A014500, A132219; DLMF §4.13 and §5.11; and the repository's
  transseries volume (added by the write), with OEIS A094089 (added by the
  write).
