# Compositions with a Length-Dependent Minimum (OEIS A098131, A098132, A098133)

**For the number `a_s(n)` of compositions of `n` whose `k` parts are all at
least `k + s` (fixed `s ≥ 0`): with `4n = e^{2v} v(v+2)`, `t = e^{−v}`,
`D = v² + 3v + 1`,
`a_s(n) = exp{e^v v(v+1)/2 − (3+2s)v/4}/√D · (Σ_{j≤J} t^j C_{s,j}(v) + O(t^{J+1}(1+v)^{J+1}))`
for every fixed `J`, with rational `C_{s,j}`, `C_{s,1}` in closed form and a
finite exact formula for `C_{s,2}`; interlaced half-power expansions for
exact-minimum compositions; fixed rare-excess probabilities; rigorous integer
brackets for the thresholds; and the leading smooth inverse misses
`v/48 + O(1)`**

A research article dated 4 October 2026 ("Report189" of a session bundle),
built from one manuscript. Its author line reads "All fixed order asymptotics
and error aware inversion" and its PDF author field "Research report": it
names no person, tool or addressee. The package carries no "prepared for
private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 189 (batch 110) | `Minimum_Length_Compositions_Asymptotics_and_Inverses_Source.zip` (23 files, no wrapper directory, 558,048 bytes, SHA-256 `15801f3cf4f5…a2d95ecd23ecde`), arrival commit `60f54ea06`; main file `Report189.tex` (671 lines, 16 pp.) | none: the package names no ProveIt commit and no repository path | `8622ca7e5` (batch 110) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Theorem 1.1 (Lemma 3.1, Gaussian completion;
  Lemma 4.1, global Fourier bound; Lemma 5.1, a uniform Cauchy remainder that
  keeps the factor `V^{J+1}`), Corollaries 7.1, 7.2, Lemma 8.1, Theorems 8.2
  and 9.1. No proof uses a computation.
- **What rests on computation.** The coefficient algorithm of Section 6 is
  implemented by the shipped standard-library programs (and checked against a
  separately organized derivative-polynomial recurrence through `C_3`); the
  closed forms (9), (52), (60) are hand derivations, rechecked by the write.
- **What is diagnostic.** The optional mpmath and SymPy experiments.
- **What is prior.** The exact counts and generating functions (OEIS; Jovovic,
  2004), the Schreier-type interpretations (Chu–Irmak–Miller–Szalay–Zhang;
  Beanland–Chu), fixed-length smallest-part counts (Knopfmacher–Munagi), the
  theta transformation and saddle methods. The claims are "deliberately
  narrower than a claim of global novelty".

## What it proves

`a_s(n)` (1), `b_s(n) = a_s(n) − a_{s+1}(n)` (2), exact sum and generating
function (3); `v`, `t`, `V = 1 + v`, `D`, `E`, `F`, `α_s`, `β_s`, `P_s` as in (4)–(6).
Statement and equation numbers are the delivered ones.

- **Theorem 1.1 (`mlc:thm:all`)**: `a_s(n) = P_s(n){Σ_{j≤J} t^j C_{s,j}(v) +
  O_{s,J}(t^{J+1}V^{J+1})}` (7), `C_{s,0} = 1`, `C_{s,j} = O(V^j)` (8), `C_{s,1}` (9);
  `−C_{s,1} = v/48 − (s − 1/2)²/4 + O_s(v^{−2})` (49); `C_{s,2}` by the finite
  formula (52), `C_{s,2} = v²/4608 + O_s(v)` (53).
- **Corollary 7.1 (`mlc:cor:half`)**: interlaced half powers for `b_s(n)` (55),
  (56); **Corollary 7.2 (`mlc:cor:rare`)**: `Pr(X_n ≥ s)` and `Pr(X_n = s)` for the
  excess `X_n = min x_i − k` (57), (58); `a_1(n)/a_0(n)` (59), (60).
- **Lemma 8.1 (`mlc:lem:monotonic`)**: eventual strict increase of `a_s` and
  `b_s`; **Theorem 8.2 (`mlc:thm:brackets`)**: monotone envelopes (65), (66) and
  `⌈r_+⌉ ≤ N_s(y) ≤ ⌈r_−⌉` (67), width `O(t^J V^{J+1})` (68); the same for
  `T_s(y)` (73).
- **Theorem 9.1 (`mlc:thm:shift`)**: `x_1 = x_0 − C_{s,1}(v_0) + O_s(t_0V_0²)` (76),
  the corrected bracket (77), and the divergent displacement
  `x_1 − x_0 = v_0/48 − (s − 1/2)²/4 + …` (78); the coarse Lambert equivalent
  (79).

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.2 (`mlc:rem:oeis`)**: the OEIS entries quoted (next section).
- **Remark 9.2 (`mlc:rem:transseries`)**: the inverses against the
  transseries volume, statement by statement.
- Section 1.1 (`mlc:sec:provenance`: provenance, the sources as the write read
  them, what was checked, relation to the repository, collected non-claims,
  reading conventions); a status note after the opening paragraph; dated notes
  at the end of Section 6 (a numerical test through order two) and in Section
  11 (the standing rule).

## The OEIS entries (Remark 1.2)

Read on 7 October 2026 in the internal format; quoted verbatim in the
article. All three are by Vladeta Jovovic, 27 September 2004.

- **A098131** (revision #23, 23 January 2024): "Number of compositions of n
  where the smallest part is greater than or equal to the number of parts.";
  "G.f.: Sum_{k>=0} x^(k^2)/(1-x)^k."; b-file `n = 0..10000` (Kotěšovec).
- **A098132** (revision #23, 20 May 2024): "… where the smallest part is
  greater than the number of parts."; "G.f.: Sum_{n>=0} x^(n*(n+1)) /
  (1-x)^n."; b-file `n = 1..10000` (Kotěšovec); links the Chu et al. preprint.
- **A098133** (revision #20, 13 March 2026): "… in which the smallest part is
  equal to the number of parts."; "G.f.: Sum_{m>=1} (x^(m^2) -
  x^(m*(m+1)))/(1-x)^m."; b-file `n = 1..1000` (Alois P. Heinz).

None of the three states an asymptotic formula or a conjecture, so the
report neither proves nor refutes an OEIS claim. The write recomputed all
10001 + 10000 + 1000 b-file terms from the exact sum (3): all agree. Nothing
was submitted to the OEIS.

## What is not claimed

From the source, collected in Section 1.1 of the article:

- No worldwide priority; the exact counts, generating functions, Schreier
  interpretations, Poisson summation and saddle methods are prior.
- Error constants and onsets are not effective; nothing is uniform in growing
  `s` or `J`; no convergence, optimal truncation or resurgent interpretation.
- No asymptotic contribution of an individual nonzero Poisson harmonic, no
  convergent transseries, no limit law for the number of parts, no
  rare-event law for growing excess.
- The inverse envelopes are eventual existence statements, with no effective
  onset or certified floating evaluation; an interval of width `o(1)` need
  not give a single ceiling; the Lambert form (79) is a relative equivalent
  only.
- Finite checks are evidence for the implementations, not proofs of the
  asymptotic statements.

The write adds: its checks are exact finite or floating computations; it
claims no novelty for any inversion.

## Further questions

Section 11 of the article (`mlc:sec:questions`) keeps the source's five
questions: explicit onset and constants (certified brackets); a growing
shift `s = s(n)`; the number of parts (centering, variance, local limit);
minima `> k^p` from the nonlinear Schreier literature; nonzero Poisson
sectors and optimal truncation. Together with the five restrictions of
Section 10 they are kept as stated. Under Vladimir's standing rule of
4 October 2026 the write found no further unproved claim and no wrong claim
in the source. **Nothing was refuted.**

## Checks made at intake

- At placement (batch-110 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 22/22;
  `code/check_exact.py` normal and `-O` byte-identical to
  `generated/exact_checks.json` (12,366 checks, 87 input rejections); its own
  binomial sums gave the OEIS prefixes and ratios to the leading term 0.99978,
  0.99971, 1.00205 at `n = 4·10^5` (`s = 0, 1, 2`).
- At the write (7 October 2026; Python 3.14.4, SymPy 1.14.0, mpmath 1.3.0;
  scripts in the intake record): every proof read line by line; `Q_2 = 2D`,
  `Q_3 = 2E`, `Q_4 = 2F`; `C_{s,1} = 𝒢(q_2 + q_1²/2)` equal to (9) symbolically in
  `s` and `v`; (60); the large-`v` form (49); from the printed `q_1, …, q_4` and
  (52), for `s = 0, 1, 2`, the denominator `4608D⁶` and `C_{s,2} = v²/4608 + O(v)`;
  a numerical test of Theorem 1.1 through order two with exact counts, where
  `(a_s(n)/P_s(n) − 1 − tC_{s,1})/t²` equals `C_{s,2}(v)` to about three
  significant digits at `n = 10^6` and `4·10^6` (`s = 0, 1, 2`; table in the
  note at the end of Section 6); the 21,001 b-file terms; Route B below.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`89b899bf3`), with
its own code, after fetching again A098131 (#23), A098132 (#23), A098133 (#20)
and their b-files.

- **Remark 1.2.** Every quotation, revision, date and author line confirmed,
  and that no entry states an asymptotic formula or conjecture (the formula
  lines are the generating functions only). The 10001 + 10000 + 1000 b-file
  terms recomputed by a second route, coefficient extraction from the
  generating functions (and the exact sum for `n ≤ 300`): all agree.
- **Coefficients.** Directly from the definition (30) of `K` by SymPy series
  in `ε`, not through the printed `q_r`: `q_1, …, q_4` equal (47)–(51),
  `B_{s,1}`, `B_{s,2}` equal (23), `C_{s,1}` equals (9) symbolically in `s`
  and `v`, and `C_{s,2}` has the common denominator `4608 D^6` with
  `C_{s,2} = v²/4608 + O_s(v)`; also `Q_2 = 2D`, `Q_3 = 2E`, `Q_4 = 2F`, the
  derivative formula (45) for `r ≤ 5`, (60), and the `O_s(v^{−2})` remainder of
  (49).
- **The numerical test** (end of Section 6) reproduced in every entry with the
  check's own `C_{s,2}`, and the dossier's ratios 0.99978, 0.99971, 1.00205 at
  `n = 4·10^5`.
- **Remark 9.2.** (a), (b) and the Lambert instance of (c) re-derived against
  the volume; **one correction**: (74) is an admissible core in the sense of
  `p0:def:core`, so "not a core of the volume" is wrong as stated (dated note
  in the article; "Relation to the repository" below).
- **Provenance.** Archive facts, staged bytes, the 100 delivered label numbers
  and 68 references, Route B (`check_exact.py` normal and `-O` byte-identical
  to the recorded output, 12,366 checks, 87 rejections) confirmed. No error
  found in the source's proofs.

The check is recorded at the end of Section 11.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remark
9.2(a) is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about `a_s(n)` is.

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
Remark 9.2: (a) `N_s(y)` and `T_s(y)` are, for large `y`, **instances** of the
staircase of `p0:def:three-inverses`(1), so `p0:thm:staircase`(1) applies;
(b) the brackets (67), (73), (77) are **analogues** of `p0:thm:staircase`(2)
(the source itself states its failure mode); (c) the coarse Lambert
equivalent (79) inverts its leading balance `v + 2 log v = log(2L)` as an
**instance** of `p0:thm:lambert-core` (`a = 1`, `b = 2`); the exact equation
(74) for `v_0` is not a core of the volume. (Corrected after the independent
check of 7 October 2026: its right side, as a function of `v_0`, is not one of
the two explicit cores `p0:eq:two-cores` that the volume inverts by Lambert
W, but it is an admissible dominant core in the sense of `p0:def:core` on a
half-line, with core solution `v_0`; whether Theorem 9.1's correction is an
instance of `p0:thm:core-reversion` is not shown.)

**Neighbouring reports.** No report of the collection treats compositions
with a length-dependent minimum, so no reciprocal note is proposed.

**Stale claims.** Before batch 110 no file of the repository named A098131,
A098132 or A098133.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `a_s(n)` against `a = 1/2 − s`; `F_s(q)`
against the polynomial `F`; `E` against the error scale `E_{s,J}` (the source
says so); `D`, `V`, `t`, `v`; `B`, `B_{s,r}`, `b_s(n)`; `P_s`, `p_m`, `q_r`, `q`;
`H`, `h_t`; the integrand `K` against the envelope constant `K` and `K_s'`;
`L_s(z)`, `L = log y`, `ℓ`; `N_s`, `T_s`, `X_n`; `M_{s,J}`, `A_{s,J}`, `M̃_{s,J}`;
`α_s`, `β_s`, `λ`, `ε`, `δ`, `ζ`; `c`, `c_s`, `C_{s,j}`; `W`, `r_±`, `x_0`, `x_1`. No
symbol was renamed; the volume's colliding letters carry the subscript "vol"
in Remark 9.2.

## Labels

Every label carries the prefix `mlc:` (none existed in the repository). The
manuscript's 100 labels (`eq:` 79, `sec:` 11, `lem:` 4, `thm:` 3, `cor:` 2,
`subsec:` 1) were prefixed before anything cited them, and the 68 references
to them (56 `\eqref`, 12 `\ref`) updated. The write added 3:
`mlc:sec:provenance`, `mlc:rem:oeis`, `mlc:rem:transseries`. The report has 103
labels; builds of the delivered text and of this one give all 100 delivered
labels the same numbers (aux files compared). The added remarks are the last
statements of their sections, the added subsection follows the last delivered
text of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                            this guide (replaces the delivery README)
article.tex                          the report (delivered Report189.tex; labels prefixed, [write] additions)
article.pdf                          compiled report, 20 pages
DATA_SOURCES.md                      delivered data-source and attribution notes
README_REPRODUCIBILITY.md            delivered reproducibility guide (delivered names)
code-README.md                       delivered guide to the code (delivered code/README.md)
data-README.md                       delivered guide to the fixture (delivered data/README.md)
code/check_exact.py                  mandatory finite exact checks (delivered code/)
code/compositions.py                 exact counts and independently multiplied generating functions (delivered code/)
code/coefficients.py                 all fixed-order coefficients C_{s,j}(v), exact (delivered code/)
code/independent_coefficients.py     separate derivative-polynomial check through C_3 (delivered code/)
code/check_symbolic.py               optional SymPy C_1/C_2 algebra check (delivered code/)
code/diagnose_float.py               optional mpmath diagnostics (delivered code/)
code/reproduce.py                    replay in normal and -O isolated Python (delivered at the root)
code/build.py                        PDF and ZIP builder; TeX Live (delivered at the root)
code/test_build.py                   builder and manifest tests (delivered at the root)
code/verify_manifest.py              release-inventory checker (delivered at the root)
data/oeis_fixtures.json              72 attributed OEIS integer values (delivered data/)
data/generated-exact_checks.json     recorded check_exact output (delivered generated/)
data/generated-verification.json     recorded verification result (same)
data/generated-build_guards.json     recorded build guards (same)
data/generated-BUILD_INFO.json       recorded build information (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `code/verify_manifest.py` is the report's own
release checker (it differs from the generic helper of other reports).

**Not shipped**, recoverable from the arrival commit (next section):
`Report189.pdf` (the delivered 16-page PDF, 397,898 bytes); the checksum
manifest `SHA256SUMS.json` (3,180 bytes, 22 entries), verified at placement
(repository policy ships no checksum manifests); and the delivery `README.md`
(3,334 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`README_REPRODUCIBILITY.md`, `code-README.md`, `data-README.md` and
`DATA_SOURCES.md` (`Report189.tex`, `code/`, `data/README.md`, `generated/`,
`SHA256SUMS.json`, root scripts); the programs (they locate `code/` and
`data/` relative to the package root, and `reproduce.py` and `build.py`
require the exact authoring inventory, including the delivery `README.md` and
no `generated/` directory); `data/generated-*.json` (delivered paths); and
Section 10 of the article ("The accompanying source archive …"). So no
program runs under the shipped names; use Route B below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Minimum_Length_Compositions_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 15801f3cf4f5a5c6079569f84ef61de4c7a84937aec323d008a2d95ecd23ecde, 558,048 bytes
cd "$T" && unzip -q a.zip
```

`SHA256SUMS.json` maps the 22 other files to their SHA-256 values.

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only (the optional scripts need SymPy
or mpmath). Never run anything in the repository.

**Route A, delivered layout** (as the delivery README gives it), in the
extraction `$T`: `python3 -I -S -B code/check_exact.py` (also with `-O`),
`python3 -I -S -B reproduce.py`, `python3 -I -S -B test_build.py`; `build.py`
needs TeX Live. `reproduce.py` and `build.py` check the exact source
inventory, so they run only in the unmodified extraction.

**Route B, from the shipped files** (tested at the write on Windows): rebuild
the layout under the delivered names, then run the exact checker.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a098131-minimum-length-compositions
B=$(mktemp -d); cd "$B"; mkdir code data generated
cp "$R/article.tex" Report189.tex; cp "$R/DATA_SOURCES.md" "$R/README_REPRODUCIBILITY.md" .
cp "$R/code-README.md" code/README.md; cp "$R/data-README.md" data/README.md
for f in build reproduce test_build verify_manifest; do cp "$R/code/$f.py" .; done
for f in check_exact check_symbolic coefficients compositions diagnose_float independent_coefficients; do cp "$R/code/$f.py" code/; done
cp "$R/data/oeis_fixtures.json" data/
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
python -I -S -B code/check_exact.py > n.json; python -I -S -B -O code/check_exact.py > o.json
cmp n.json o.json; cmp n.json generated/exact_checks.json
```

At the write both comparisons were silent (byte-identical; 12,366 checks and
87 input rejections, `"status": "passed"`) in a few seconds. In this layout
`reproduce.py` stops with "source inventory mismatch" (the delivery
`README.md` is missing and `generated/` is present); take the delivered
archive (Route A) for it. Use `py` where `python` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, microtype, hyperref, enumitem, longtable); the
bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (19
pages), and rebuilt after the independent check of the same day (label
numbers unchanged, aux files compared): 20 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes
(the delivered text also builds without any, 16 pages). The article keeps the
delivered preamble lines that suppress PDF dates and trailer identifiers.

## From the delivery README

The delivery README (replaced by this guide) described the families
`a_s(n)` and `b_s(n)` and the OEIS normalizations (A098131 = `a_0` including
`n = 0`, A098132 = `a_1`, A098133 = `b_0`); said that "No worldwide priority,
growing-s uniformity, effective onset, convergent transseries, or automatic
single-ceiling inverse formula is asserted"; gave the quick-start commands
(the exact checker "prints canonical JSON with 12,453 checks, including 87
explicit input rejections"; 258 build-guard tests) and the release build (a
new output directory, no downloads, no overwriting); described the
mathematical programs; and stated the package scope ("72 attributed integer
fixture values"; "no full OEIS records, third-party articles, source-page
downloads, private research or audit files").

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A098131, A098132 and A098133, and `data/oeis_fixtures.json` holds 72
of their terms; OEIS content is published by The OEIS Foundation Inc. under
CC BY-SA 4.0 (https://oeis.org/LICENSE), and that content remains under that
licence. No third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A098131, A098132, A098133;
  Chu–Irmak–Miller–Szalay–Zhang, Integers 24A (2024); Beanland–Chu, J.
  Integer Seq. 27 (2024); Knopfmacher–Munagi (2013); DLMF 20.7 and 24.2.
- Batch 110 of `docs/incoming`, bundle Report 189; arrival `60f54ea06`,
  placement `8622ca7e5`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report189.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
