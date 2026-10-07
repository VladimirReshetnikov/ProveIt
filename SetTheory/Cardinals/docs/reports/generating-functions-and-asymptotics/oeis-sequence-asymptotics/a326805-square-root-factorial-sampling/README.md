# Hidden Oscillations in Square-Root Factorial Sampling (OEIS A326805)

**For `S(x) = Σ_{k≥0} x^{√k}/Γ(1+√k)` and `a(n) = ⌊S(n)⌋`: Kotěšovec's
conjecture `a(n) ~ 2n e^n` is proved, with `a(n)/(2ne^n) = 1 + o(n^{−r})` for
every `r`; the discrepancy `S(x) − 2xe^x` has every fixed order of a
Lambert-W chirp, `−A_1 Im{e^{iθ_1} Σ d_{1,j} y_1^{−j}}`, and the exact
subsequential-limit set `[−C_*, C_*]` after division by
`n^{1/8}(log n)^{3/8}`, `C_* = 4(4π)^{−7/8}`; an exact finite-harmonic
formula; a complex-sector bound; a convergent Lagrange inverse; and the naive
threshold `⌈W(Y/2)⌉` fails infinitely often in both directions**

A research article dated 3 October 2026 ("Report187" of a session bundle),
built from one manuscript. Its author line reads "OEIS A326805, Exact
harmonics, all fixed orders, and inverse thresholds" and its PDF author field
"Research report": it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data (`DATA_SOURCES.md` says "Raw research records and private
review notes are excluded", a statement about what was left out).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 187 (batch 110) | `Square_Root_Factorial_Sampling_Oscillations_and_Inverses_Source.zip` (30 files, no wrapper directory, 708,567 bytes, SHA-256 `75420111809b…cc206fbfbc4dbf`), arrival commit `60f54ea06`; main file `Report187.tex` (888 lines, 20 pp.) | none: the package names no ProveIt commit; it cites three ProveIt expositions by their GitHub paths | `8622ca7e5` (batch 110) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Every theorem: Lemma 3.1 (Abel–Plana at the
  square-root endpoint), Theorem 1.3 (finite harmonic resolution, Section 4),
  Lemmas 5.1, 5.2 and Section 6 (each fixed mode to every fixed order),
  Theorem 1.1 and Corollary 1.2 (Section 7), Theorem 8.1 (sector bound),
  Theorem 9.1 and Corollary 9.2 (inverse), Theorem 10.1, Proposition 11.1. No
  proof uses a computation.
- **What rests on computation.** The coefficients `d_{m,j}` (exact rational
  complex arithmetic in powers of `π^{−1}`, by the shipped generator) and the
  rational tail inequalities (67) for `n ≤ 34`.
- **What is diagnostic.** The optional 55/75-digit replay of the 35 OEIS
  floors and the Gaussian-line mode values of Section 12 ("not
  interval-certified").
- **What is prior.** The sequence (Paul D. Hanna, 14 September 2019), the
  conjecture (Kotěšovec, 16 September 2019); Abel–Plana, complex Stirling, the
  Volterra–Ramanujan identity (Garrappa–Mainardi, Theorem 3.1), analytic
  Lagrange inversion. "No new general summation, Stirling, stationary-phase or
  inverse theorem is claimed."

## What it proves

`M(x) = 2xe^x`, `D = S − M`, `L = log x`; for mode `m`: `q = 4πm`,
`α = 1/(8m)`, `β = 1/2 − α`, `y_m = W(qx)/q`, `θ_m = qy²/2 + y − π/(32m)`,
`A_m = 4x^α y^β/√q` (5). Statement and equation numbers are the delivered ones.

- **Theorem 1.1 (`srf:thm:main`)**: for every fixed `K`, (6), with exact
  `d_{m,j} ∈ Q(i)[π^{−1}]`, `d_{1,1} = −1/(8π) + 11i/384`,
  `d_{1,2} = 3/(128π²) − 2137/294912 + 79i/(3072π)` (7); the same at integers
  for `a(n) − 2ne^n`.
- **Corollary 1.2 (`srf:cor:sharp`)**: the subsequential limits of
  `(a(n) − 2ne^n)/(n^{1/8}(log n)^{3/8})` are exactly `[−C_*, C_*]` (9);
  `a(n) ~ 2ne^n` and (10).
- **Theorem 1.3 (`srf:thm:finite`)**: `S = M − 2N_1 + 1/2 + 2Re Σ_{m≤M} J_m +
  R_{M+1}` (12), `N_1 = O(L^{−2})` (13), `R_{M+1} = O(x^{1/(8(M+1))+ε})` (14), and
  each mode to every fixed order (15).
- **Sections 3–6**: Lemma 3.1 (`srf:lem:abel`), the exact kernel and the
  origin constant `+1/2`, Lemma 5.1 (`srf:lem:negative`), Lemma 5.2
  (`srf:lem:localization`), and the finite coefficient generator (45)–(49).
- **Theorem 8.1 (`srf:thm:sector`)**: `|D(z)| ≤ C_a|z|^a` in a sector, for every
  `a > 1/8` (53), and `D^{(r)}(x) = O(x^{a−r})` (54).
- **Theorem 9.1 (`srf:thm:inverse`)**: with `w = W(Y/2)`, the Lagrange series
  (57) for `S^{−1}(Y) − w` converges, remainder (58); the first terms (59);
  **Corollary 9.2 (`srf:cor:invosc`)**: (60), (61).
- **Section 10**: `N(Y) = ⌈X(Y)⌉` (63) and the enclosure (64); **Theorem
  10.1 (`srf:thm:failure`)**: `N(Y)` and `⌈W(Y/2)⌉` differ by at most one, and
  differ infinitely often in each direction (65), (66).
- **Proposition 11.1 (`srf:prop:logconcavity`)**: `a(n)` strictly increasing for
  `n ≥ 0`, eventually strictly log-concave.

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.4 (`srf:rem:oeis`)**: the OEIS entry quoted, and the conjecture
  proved (next section).
- **Remark 10.2 (`srf:rem:transseries`)**: the inverses against the
  transseries volume, statement by statement.
- Section 1.1 (`srf:sec:provenance`: provenance, the sources as the write read
  them, what was checked, relation to the repository, collected non-claims,
  reading conventions); a status note after the opening paragraph; dated notes
  in Section 13 (the conjecture still printed; the standing rule).

## The OEIS entry and the conjecture proved (Remark 1.4)

Read on 7 October 2026 in the internal format; quoted verbatim in the article.

- **A326805** (revision #16, 21 March 2020; Paul D. Hanna, Sep 14 2019): "a(n) =
  floor( Sum_{k>=0} n^sqrt(k) / Gamma(sqrt(k) + 1) ), where Gamma is Euler's
  gamma function."; 35 terms; "Conjecture: a(n) ~ 2*n*exp(n). - _Vaclav
  Kotesovec_, Sep 16 2019"; a table of the sums for `0 ≤ n ≤ 20`.

**Proved.** Corollary 1.2 proves the conjecture exactly as stated (and the
much stronger relative estimate (10), with an unbounded two-sided absolute
discrepancy). The write recomputed `S(n)`, `0 ≤ n ≤ 34`, at 50 digits with its
own code (floating, not interval): all 35 floors equal the OEIS data, and the
smallest distance to an integer is `0.00169001377462648…` at `n = 17`, the
value printed in Section 12 and consistent with the OEIS table
(`821268392.99830998…`). Nothing was submitted to the OEIS. The comparison
with A336293 ("a(n) = Sum_{k=0..n} binomial(n,k)^2 * binomial(2*k,k) *
(n-k)!.", treated by the transseries exposition
`Late_Growth_Bessel_Counting_Coefficients`) concerns a different object, as
the source says.

## What is not claimed

From the source, collected in Section 1.1 of the article:

- No new general summation, Stirling, stationary-phase or inverse theorem; no
  worldwide priority; the overlap checks "support a scoped description of the
  work, not an exhaustive literature or worldwide novelty determination".
- No uniform growing-harmonic expansion, no convergent infinite asymptotic
  harmonic sum, no effective onset; estimates are fixed in `m`, `M`, `K`.
- Expansions are additive on a positive envelope, "never relative to a sine
  near its zeros".
- The infinite Stirling series is formal; the convergent Lagrange inverse
  concerns powers of the exact discrepancy only.
- The big-`O` results give no effective constants and no certified finite-`Y`
  thresholds; the floating diagnostics are "strong consistency evidence" but
  "not interval-certified".

The write adds: its checks are exact finite or floating computations; it
claims no novelty for any inversion.

## Further questions

Section 13 of the article (`srf:sec:scope`) keeps the source's four
questions: the boundary exponent of the finite-harmonic remainder; uniformity
in a growing number of harmonics; interval quadrature for certified
discrepancy and threshold values; the general sampler
`Σ x^{k^ρ}/Γ(1 + k^ρ)`. Under Vladimir's standing rule of 4 October 2026 the
write found no further unproved claim and no wrong claim in the source; a
dated note assigns the unproved aside after Theorem 8.1 ("The same pairing
could be used for higher exact-mode remainders", not used) to Question 1.
**Nothing was refuted.**

## Checks made at intake

- At placement (batch-110 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 29/29;
  `reproduce.py` on a copy PASS in 4 s, certificates byte-identical,
  `RESULT.json` equal to `generated/verification.json` modulo CR.
- At the write (7 October 2026; Python 3.14.4, SymPy 1.14.0, mpmath 1.3.0;
  scripts in the intake record): every proof read line by line (the arc
  constant, the cancellation identity, `C_*`, the second-order inverse terms,
  the inequalities of Theorem 10.1, `M(n)² − M(n−1)M(n+1) = 4e^{2n}`); by a
  direct series of (46) with the moments (45), not the recursion (48)–(49),
  `d_{1,1}`, `d_{1,2}`, `d_{1,3}`, `d_{2,1}`, `d_{2,2}`: all equal the shipped
  certificate; the 35 floors; Route B below (three certificates
  byte-identical, normal = optimized, 9 s). The optional Gaussian-line
  diagnostics were not rerun.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`6ec1f3f92`), with
its own code, after fetching again A326805 (#16) and A336293.

- **Remark 1.4.** Every quotation, revision, date and author line confirmed,
  the 35 terms and the table line for `n = 17`; the check's 70-digit sums give
  all 35 floors, and the smallest distance to an integer is at `n = 17`,
  `0.00169001377462648414…` (the smallest fractional part alone is at
  `n = 22`, `0.00317…`).
- **The conjecture, checked hardest.** The proof chain of Corollary 1.2
  re-read; Theorem 1.3 with `M = 0` already gives `D(x) = O(x^{1/8+ε})` and so
  `a(n) ~ 2ne^n`. Its exact foundation (Lemma 3.1 with (17)) tested
  numerically: `S(x) − 2xe^x = −2N_1(x) + 1/2 − 2∫ Im F_x(it)/(e^{2πt} − 1) dt`
  to `10⁻²³` at `x = 3, 10, 25`, confirming the endpoint constant `+1/2`. The
  first row of the Gaussian-line table recomputed by direct quadrature on the
  ray: at `log x = 40`, `2 Re J_1 = −72.5984597595149`, normalized error
  `−4.47274633408·10⁻⁵`, as printed.
- **Coefficients.** `d_{1,1}, d_{1,2}, d_{1,3}, d_{2,1}, d_{2,2}` from (46) and
  (45) by SymPy series: all equal the shipped certificate; `B_2(1/8) = 11/192`;
  `C_* = 0.436768551345747…`; the second-order terms of (59) and the arc
  constant (28) re-derived.
- **Remark 10.2.** (a)–(e) re-derived against the volume (in (e) only the term
  `m = n` of `p0:eq:core-lagrange` survives, giving (57) exactly); **one
  correction**: the Lean declarations for (b) and (c) are
  `Fabius.staircase_separation` and `Fabius.staircase_separation_fails`, not
  `Fabius.staircase_ceil` (dated note in the article; "Relation to the
  repository" below).
- **Provenance.** Archive facts, staged bytes, the `DATA_SOURCES.md` sentence,
  the three cited expositions, the 89 delivered label numbers and 69
  references, Route B (three certificates byte-identical, normal = optimized,
  5 s) confirmed. No error found in the source's proofs.

The check is recorded at the end of Section 13.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remark
10.2 is formalized generically in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`: (a)
as `Fabius.staircase_ceil`, (b) as `Fabius.staircase_separation`, and the
abstract failure mode that (c) realizes as
`Fabius.staircase_separation_fails`; nothing about `S` or `a(n)` is.
(Corrected after the independent check of 7 October 2026: the write named
only `Fabius.staircase_ceil`, for (a)–(b).)

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`,
which the source cites), Remark 10.2: (a) `N(Y) = ⌈X(Y)⌉` (63) is an
**instance** of `p0:thm:staircase`(1) for `A_n = S(n)` with the admissible
interpolation `S` itself (`n_1 = 0`); (b) the enclosure (64), when its ceilings
agree, is `p0:thm:staircase`(2) (**instance**); (c) Theorem 10.1 is an
explicit realization of the failure mode named in `p0:thm:staircase`(2), with
an exponentially small `η`; (d) `w = W(Y/2)` and the mode saddle `y_m` are
**instances** of `p0:thm:lambert-core` (`a = b = 1`; `a = q_m`, `b = 1`);
(e) the inverse equation of Theorem 9.1 is a formal **instance** of
`p0:thm:core-reversion` (`Λ = 1`, `h = 0`, `f(t,u) = tD(w+u)Q_w(u)`, `t = 1/Y`),
whose closed formula is exactly (57); the convergence is the source's own.

**Neighbouring material.** The source compares with
`Analysis/Transseries/docs/series-and-transseries/Action_Accumulation_Nonlinear_Inversion/`
and `…/Late_Growth_Bessel_Counting_Coefficients/` (A336293); both treat
different objects and no question of either is answered, so no reciprocal
note is proposed. No report of the collection treats A326805.

**Stale claims.** Before batch 110 no file of the repository named A326805.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `M(x)` against the number of modes `M`;
`S`, `D`, `I`; `K`, `K_p`, `K_m^−` (the source distinguishes these itself);
`A_m`, `C_*`, `C_r`, `C`; `N_0`, `N_1`, `N(Y)`, `N`; `R_{M+1}`, `R_a`, `R`; `W`, `w`;
`y_m`, `Y`; `q`, `α`, `β`; `F_x`, `F_m`, `f_x`, `h_x`; `H`, `H_j`, `𝒢_q`; `E_w`, `Q_w`,
`Q`, `b_w`, `c_w`; `c`, `μ`, `δ`, `η`, `ρ` (three uses); `L`, `X(Y)`, `X̂`; `θ_m`,
`Φ`. No symbol was renamed; the volume's colliding letters carry the
subscript "vol" in Remark 10.2.

## Labels

Every label carries the prefix `srf:` (none existed in the repository). The
manuscript's 89 labels (`eq:` 65, `sec:` 13, `thm:` 5, `lem:` 3, `cor:` 2,
`prop:` 1) were prefixed before anything cited them, and the 69 references to
them (57 `\eqref`, 12 `\ref`) updated. The write added 3:
`srf:sec:provenance`, `srf:rem:oeis`, `srf:rem:transseries`. The report has 92
labels; builds of the delivered text and of this one give all 89 delivered
labels the same numbers (aux files compared). The added remarks are the last
statements of their sections, the added subsection follows the last delivered
text of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered Report187.tex; labels prefixed, [write] additions)
article.pdf                               compiled report, 25 pages
DATA_SOURCES.md                           delivered data-source and attribution notes
README_REPRODUCIBILITY.md                 delivered reproducibility guide (delivered names)
optional-README.md                        delivered guide to the optional programs (delivered optional/README.md)
code/reproduce.py                         replay driver, normal and -O, byte comparison (delivered at the root)
code/build.py                             PDF and ZIP builder; TeX Live (delivered at the root)
code/test_build.py                        builder and manifest tests (delivered at the root)
code/verify_manifest.py                   package-inventory checker (delivered at the root)
code/verify_source_data.py                checks the attributed OEIS fixture against its hashes (delivered at the root)
code/exact_coefficients.py                exact d_{m,j} generator (delivered code/)
code/positive_tail.py                     rational tail inequalities (67) (delivered code/)
code/test_mathematical_guards.py          corruption tests (delivered code/)
code/optional-replay_oeis.py              optional 55/75-digit OEIS replay (delivered optional/)
code/optional-stable_modes.py             optional Gaussian-line mode integrals (delivered optional/)
code/optional-diagnostics_sympy.py        optional exact SymPy cross-check, orders 0..4, modes 1, 2 (delivered optional/)
data/oeis_prefix.json                     the 35 displayed OEIS terms (delivered data/)
data/SOURCE_DATA_HASHES.json              hashes of the third-party data (delivered data/)
data/certificates-formal_coefficients.json  recorded certificate (delivered certificates/)
data/certificates-mathematical_guards.json  recorded certificate (same)
data/certificates-positive_tails.json     recorded certificate (same)
data/generated-verification.json          recorded verification result (delivered generated/)
data/generated-build_guards.json          recorded build guards (same)
data/generated-BUILD_INFO.json            recorded build information (same)
data/optional-oeis_replay_full.json       recorded optional output (delivered optional/)
data/optional-stable_modes_full.json      recorded optional output (same)
data/optional-stable_modes_quick.json     recorded optional output (same)
data/optional-sympy_check.json            recorded optional output (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `code/verify_manifest.py` is a generic helper
with byte-identical copies in other reports of this collection; it is shipped
here so that the package reruns on its own.

**Not shipped**, recoverable from the arrival commit (next section):
`Report187.pdf` (the delivered 20-page PDF, 445,251 bytes); the checksum
manifest `SHA256SUMS.json` (2,821 bytes, 29 entries), verified at placement
(repository policy ships no checksum manifests); and the delivery `README.md`
(3,269 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`README_REPRODUCIBILITY.md`, `DATA_SOURCES.md` and `optional-README.md`
(`Report187.tex`, `certificates/`, `generated/`, `optional/`,
`SHA256SUMS.json`, root scripts); the programs (they locate `code/`, `data/`,
`certificates/` and `optional/` relative to the package root);
`data/generated-*.json` (delivered paths); and Section 12 of the article
("The source archive contains …"). So no program runs under the shipped
names; use Route B below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Square_Root_Factorial_Sampling_Oscillations_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 75420111809b575f4a9b37201acdfb1921bbf9a61d8cff2a71cc206fbfbc4dbf, 708,567 bytes
cd "$T" && unzip -q a.zip
```

`SHA256SUMS.json` maps the 29 other files to their SHA-256 values.

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only (the optional scripts need SymPy
or mpmath). Never run anything in the repository.

**Route A, delivered layout** (as `README_REPRODUCIBILITY.md` gives it), in the
extraction `$T`: `python3 verify_manifest.py`, `python3 reproduce.py` (or
`--output-dir` a new directory outside the package), `python3 build.py
--output …` (TeX Live).

**Route B, from the shipped files** (tested at the write on Windows): rebuild
the delivered layout under the delivered names, then run the driver.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a326805-square-root-factorial-sampling
B=$(mktemp -d); cd "$B"; mkdir code certificates generated optional data
cp "$R/article.tex" Report187.tex; cp "$R/DATA_SOURCES.md" "$R/README_REPRODUCIBILITY.md" .; cp "$R/optional-README.md" optional/README.md
for f in build reproduce test_build verify_manifest verify_source_data; do cp "$R/code/$f.py" .; done
for f in exact_coefficients positive_tail test_mathematical_guards; do cp "$R/code/$f.py" code/; done
for f in "$R"/code/optional-*.py "$R"/data/optional-*.json; do n=$(basename "$f"); cp "$f" "optional/${n#optional-}"; done
cp "$R/data/SOURCE_DATA_HASHES.json" "$R/data/oeis_prefix.json" data/
for f in "$R"/data/certificates-*; do n=$(basename "$f"); cp "$f" "certificates/${n#certificates-}"; done
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
O=$(mktemp -d)/out; python -B reproduce.py --output-dir "$O"
for f in "$O"/normal/*.json; do cmp "$f" "certificates/$(basename "$f")"; done; diff -r "$O/normal" "$O/optimized"
```

At the write the driver printed `"status": "PASS"` in about 9 s; the three
normal-mode certificates were byte-identical to the shipped ones, the normal
and optimized outputs identical, and `RESULT.json` equal to
`generated/verification.json` modulo CR (Windows writes CRLF). The layout
differs from the delivery only by the missing `README.md`, `Report187.pdf`
and `SHA256SUMS.json`. Use `py` where `python` is not on the path. The
optional programs write beside themselves: run them only in such a copy.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, microtype, hyperref, enumitem, longtable); the
bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026, and
rebuilt after the independent check of the same day (label numbers
unchanged, aux files compared): 25 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes
(the delivered text also builds without any, 20 pages). The article keeps the
delivered preamble lines that suppress PDF dates and trailer identifiers.

## From the delivery README

The delivery README (replaced by this guide) described the package and the
model ("The principal term is 2*x*exp(x), while the leading absolute
discrepancy has an oscillating, unbounded envelope of order
x^(1/8)*(log x)^(3/8)"); gave the quick checks (`python -B reproduce.py`,
`python -B test_build.py`, the same with `-O`, and `python -B
verify_manifest.py` in an extracted release) and the build command
(`python -B build.py --output ../report187-release`, a new directory; no
overwriting, no network); and separated the mandatory exact checks (the
coefficient algebra in rationals and powers of `1/π`, the rational tail
inequalities for `n = 1, …, 34`) from the optional ones (mpmath floor replay
and completed-line quadrature, "floating consistency checks, not interval
certificates"; an independent SymPy expansion), adding that the analytic
results "are proved in the manuscript; the scripts are not finite-data proofs
of the theorem or effective onset bounds".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A326805 and A336293, and `data/oeis_prefix.json` holds the 35
displayed terms of A326805; OEIS content is published by The OEIS Foundation
Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that content remains
under that licence. No third-party PDF is shipped. Nothing was submitted to
the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A326805; Garrappa–Mainardi, Analysis
  36 (2016); DLMF 2.10 and 5.11; three ProveIt expositions
  (`Transseries_And_Inversion`, `Action_Accumulation_Nonlinear_Inversion`,
  `Late_Growth_Bessel_Counting_Coefficients`).
- Batch 110 of `docs/incoming`, bundle Report 187; arrival `60f54ea06`,
  placement `8622ca7e5`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report187.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
