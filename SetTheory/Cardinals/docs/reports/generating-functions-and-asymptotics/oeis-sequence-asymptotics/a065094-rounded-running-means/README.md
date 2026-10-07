# Rounded Running Means (OEIS A065094, A065095)

**Every bounded additive perturbation of the running-mean recurrence
`a_{n+1} = a_n + S_n/n` has `a_n = A L_{n−1}(−1) + O(√n)`, with an exact
positive-weight formula for `A`, a pointwise optimal error interval and nested
rational bounds for `A` from any finite trajectory; hence the two OEIS
modified-Bessel growth conjectures are proved: `a_n^± ~ C_± I_0(2√n)`, with
`A_− = 0.7347779481…`, `A_+ = 1.2942770099…` certified to 69 truncated
digits; every fixed order; eventual strict log-concavity; the range inverse
to every fixed order; two-ceiling threshold brackets**

A research article dated 3 October 2026 ("Report186" of a session bundle),
built from one manuscript. Its author line reads "Exact amplitude selection
and all order asymptotics" and its PDF author field "Research report": it
names no person, tool or addressee. The package carries no "prepared for
private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 186 (batch 110) | `Rounded_Running_Means_Bessel_Asymptotics_and_Inverses_Source.zip` (33 files, no wrapper directory, 617,579 bytes, SHA-256 `5a8332939ea7…8cea55487d0ef1`), arrival commit `60f54ea06`; main file `Report186.tex` (760 lines, 19 pp.) | none: the package names no ProveIt commit and no repository path | `8622ca7e5` (batch 110) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Theorem 1.1 (exact Green formula, positive
  weights of mass one, the sharp envelope), Theorem 1.2 (nested rational
  brackets), Lemma 2.1 (Casoratian), Theorem 4.1, Proposition 8.1, Theorems
  9.1 and 10.1. The one special-function input is the classical Perron
  expansion of `L_m(−1)` to every fixed order, as stated by
  Deaño–Huertas–Marcellán (formula (3)), used with the index shift `n = m + 1`.
- **What rests on computation.** The 70-place amplitude intervals and the
  69-digit truncations of `A_±`, `C_±`, `c_±` (Section 7): exact integer and
  rational arithmetic at `N = 10000`, with rational enclosures of `e^{1/2}`
  and `π`, by the shipped standard-library programs; the coefficient tables
  (43), (71), (74), (75) are finite exact computations (and were rederived by
  the write).
- **What is diagnostic.** The optional 120-digit residual and inverse
  experiments.
- **What is prior.** The sequences (Schimke), the unrounded Laguerre solution
  (A376995, Kotěšovec), the numerical constants (Kotěšovec, 12 October 2024),
  the Perron expansion and its coefficient methods. The source claims "No
  worldwide novelty determination, proof-assistant certification, effective
  asymptotic onset, or distributional assumption about rounding errors".

## What it proves

`a_n^−`, `a_n^+` are A065094 (floor) and A065095 (ceiling); `P_n = L_{n−1}(−1)`,
`T_n = Σ_{j≤n} P_j` (3); `Q_n`, `w_n` (4); `H_n = (n−1)P_{n−1}Q_n`. Statement and equation
numbers are the delivered ones.

- **Theorem 1.1 (`rrm:thm:shadow`)**: for every forcing in `[ℓ, u]`, the
  amplitude (5) satisfies the exact identity (6), the pointwise optimal
  envelope (7), `H_n ~ √n/2`, so `a_n = A P_n + O(√n)`.
- **Theorem 1.2 (`rrm:thm:certificate`)**: `(S_N + Nℓ)/T_N ≤ A ≤ (S_N + Nu)/T_N`
  (9), nested, width `N(u − ℓ)/T_N ~ 2√π e^{1/2}(u − ℓ)N^{3/4}e^{−2√N}` (10).
- **Corollary 1.3 (`rrm:cor:oeis`)**: `a_n^± = A_± P_n + O(√n)` and
  `a_n^± ~ C_± I_0(2√n) ~ c_± n^{−1/4}e^{2√n}` (12), `C_± = A_± e^{−1/2}`,
  `c_± = A_± e^{−1/2}/(2√π)` (13).
- **Theorem 4.1 (`rrm:thm:allorders`)**: every fixed order (39), with the
  coefficients `c_j` of `L_{n−1}(−1)` (33), (43), common to both sequences;
  the relative perturbation error is `O(n^{3/4}e^{−2√n})`.
- **Section 7**: the certified intervals at `N = 10000` and the decimals (56),
  (57). **Section 8**: `a_n^+/a_n^− = A_+/A_− + O(n^{3/4}e^{−2√n})` (62); the
  ratio expansion (63); **Proposition 8.1 (`rrm:prop:logconcavity`)**:
  eventual strict log-concavity.
- **Theorem 9.1 (`rrm:thm:rangeinverse`)**: with the Lambert root (72),
  `n = t_0²/4 + 17/48 + 1/(48t_0) − 539/(2880t_0²) − 51/(640t_0³) −
  25517/(241920t_0⁴) + O(t_0^{−5})` (75) along the range, and every fixed order.
- **Theorem 10.1 (`rrm:thm:threshold`)**: for arbitrary thresholds,
  `⌈x_+(Y)⌉ ≤ N(Y) ≤ ⌈x_−(Y)⌉` (79), root width `O(t_0^{−M})` (80).

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.4 (`rrm:rem:oeis`)**: the OEIS entries quoted, and what is proved
  (next section).
- **Remark 10.2 (`rrm:rem:transseries`)**: the inverses against the
  transseries volume, statement by statement.
- Section 1.1 (`rrm:sec:provenance`: provenance, the sources as the write read
  them, what was checked, relation to the repository, collected non-claims,
  reading conventions); a status note after the opening paragraph; dated notes
  in Sections 12 (the records still ask for the proof) and 13 (the standing
  rule; a residual diagnostic for Question 1).

## The OEIS entries and the conjectures proved (Remark 1.4)

Read on 7 October 2026 in the internal format; quoted verbatim in the article.

- **A065094** (revision #19, 12 October 2024; Ulrich Schimke): "a(1) = 1, a(n+1)
  is the sum of a(n) and floor( arithmetic mean of a(1) ... a(n) )." Unsigned
  comment: "It seems that a(n) is asymptotic to C*BesselI(0,2*sqrt(n)) where C
  is a constant C = 0.44... and BesselI(b,x) is the modified Bessel function of
  the first kind. Can someone prove this?" Kotěšovec (Oct 12 2024):
  "Numerically, a(n) ~ c * exp(2*sqrt(n)) / n^(1/4), where c =
  0.12571987512700920098166979884420897638511306007242..." and "C =
  0.445665353608456118285630970456186510059368576678...".
- **A065095** (revision #20, 30 September 2026; Schimke): the ceiling analogue,
  the same unsigned question with "C = 0.78...", and Kotěšovec's "c =
  0.2214496835182522607818590241239262909281832289078...", "C =
  0.78501868866746800511978860290796656518270697588...".
- **A376995** (#16, Kotěšovec): `floor(b(n))` for the unrounded recurrence,
  "a(n) ~ exp(-1/2) * BesselI(0, 2*sqrt(n))", "a(n) =
  floor(A160617(n-1)/A160618(n-1))" (numerator and denominator of
  `L_n(−1)`), so `b(n) = P_n`.

**Proved.** Corollary 1.3 proves both unsigned statements exactly as asked
(`a_n^± ~ C_± I_0(2√n)`, `C_− = 0.4456…`, `C_+ = 0.7850…`) and Kotěšovec's
numerical equivalents; his four decimals (50, 48, 49 and 47 places) are
truncations of the certified values, as are the source's 48-place values. The
transcription slips the source mentions are A065094's comment
"A241772(n) = a(n+1) - a(n) = (Sum_{1..n} a(k)) / n." (no floor) and
A065095's example "… = 7 + floor(14/4) = 7 + 4 = 11." (a ceiling written as
floor). Both b-files (Harry J. Smith, `n = 1..1000`) are byte-identical to the
shipped ones, and the write's own recomputation agrees with all 2000 terms.
Nothing was submitted to the OEIS.

## What is not claimed

From the source, collected in Section 1.1 of the article:

- No worldwide novelty, proof-assistant certification, effective onset or
  distributional assumption about rounding errors; the source review "is not
  an exhaustive literature search".
- The `O(√n)` envelope is sharp for the bounded-forcing class only; it is "not
  a lower bound on either actual rounded residual".
- "All orders" means one theorem per fixed order; no convergence or
  uniformity in the order.
- Agreement with the published constants is a consistency check; the proof is
  the exact inequalities. Finite and floating observations are not onset
  certificates.
- No effective onset for the all-order remainder, log-concavity,
  nearest-integer recovery or the threshold comparison functions; the range
  inverse needs the exact amplitude; the threshold theorem is not an
  executable finite certificate, and one ceiling of a truncation is not
  asserted to give the threshold.

The write adds: its checks are exact finite or floating computations; it
claims no novelty for any inversion.

## Further questions

Section 13 of the article (`rrm:sec:questions`) keeps the source's six
questions: the actual residual scale; fractional parts; effective onsets;
general rounding rules (positivity of `A`); zero amplitude and constant
forcing; dependence on the errors. Under Vladimir's standing rule of
4 October 2026 the write found no further unproved claim and no wrong claim
in the source. A dated note records a diagnostic for Question 1, not a
theorem: with the certified 69-digit amplitudes, `|a_n^− − A_− P_n| ≤ 3.30`
(largest at `n = 946`) and `|a_n^+ − A_+ P_n| ≤ 4.08` (largest at `n = 1528`)
for `n ≤ 2500`, where the envelope is about `√n/2 ≈ 25`; averages over
`(n/2, n]` lie in `[0.43, 0.69]` (floor) and `[−0.65, −0.37]` (ceiling) at
`n = 100, 500, …, 2500`. No growth rate is inferred. **Nothing was refuted.**

## Checks made at intake

- At placement (batch-110 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 32/32;
  `reproduce.py --output-dir` on a copy PASS in 13 s, normal-mode
  certificates byte-identical to the six recorded ones, `RESULT.json` equal to
  `generated/verification.json` modulo CR.
- At the write (7 October 2026; Python 3.14.4, SymPy 1.14.0; scripts in the
  intake record): every proof read line by line (impulse response, tails,
  envelopes, positivity, width, ratio expansion, the constant-forcing
  example); with its own SymPy code `c_1, …, c_6` from the recurrence, the
  `b_j`, the five coefficients of `δ` (74) and the range inverse (75), and the
  DHM shift `c_1 = d_1 − 1`, `c_2 = d_2 − d_1 + 3/4`: all agree; both orbits
  and the brackets at `N = 3000` from the positive sum (55): equal to the
  certified table in 40 places; every OEIS and source decimal a truncation of
  the certified 69 digits; Route B below (six certificates byte-identical,
  normal = optimized, 19 s).

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`1ebd8c33c`), with
its own code, after fetching again A065094 (#19), A065095 (#20), A376995
(#16), the names of A160617, A160618, and both b-files.

- **Remark 1.4.** Every quotation, revision, date and author line confirmed
  (Kotěšovec's comment is quoted in two fragments; the elided words are "It
  follows that the constant above is equal to"). Both b-files byte-identical
  to the shipped ones; the check's own orbits agree with all 2000 terms.
- **The conjectures.** The proof chain of Corollary 1.3 re-read. By a route
  different from the brackets (9) — `A = 1 + Σ w_k ε_k` (5) with
  `w_k = k(Q_k − Q_{k+1})` from a Miller backward recurrence for the minimal
  solution, normalized by `Q_1 = e E_1(1)` — `A_±` to 80 digits, agreeing with
  the `N = 10000` brackets to `3·10⁻⁸²`. The four tabulated endpoints are the
  outward 70-place roundings of the exact brackets; the 69-digit common
  truncations hold; Kotěšovec's four decimals (50, 48, 49, 47 places) and the
  source's 48-place values are truncations; `N/T_N < 8.0967911913136482·10⁻⁸⁴`.
- **Coefficients.** `c_1, …, c_6` by an ansatz in the three-term recurrence
  (14) itself, not through the operator (40); `b_1, …, b_5`, (74), (75), the
  prefactor shift, `c_1 = d_1 − 1`, `c_2 = d_2 − d_1 + 3/4`, the ratio
  expansion (63): all agree. `T_N` by the positive sum equals (53) at
  `N = 150, 3000`; the `N = 3000` brackets agree with `N = 10000` to 40 places.
- **Residual diagnostic** (Section 13) reproduced: 3.294 at `n = 946`, 4.073
  at `n = 1528`, `H_2500 = 24.50`, the twelve averages; both orbits satisfy
  the envelopes (30), (31) for `n ≤ 2500`.
- **Remark 10.2.** (a)–(e) re-derived against the volume (including
  `z(L) = −2D²/Y²` and `L_c = (1 + log 2)/2`); **one correction**: the Lean
  declaration for (c) is `Fabius.staircase_round`, not `Fabius.staircase_ceil`
  (dated note in the article; "Relation to the repository" below).
- **Provenance.** Archive facts, staged bytes, the 101 delivered label numbers
  and 63 references, Route B (six certificates byte-identical, normal =
  optimized, 20 s) confirmed. No error found in the source's proofs.

The check is recorded at the end of Section 13.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remark
10.2(a) is formalized generically as `Fabius.staircase_ceil`, and that of
10.2(c) (`p0:thm:staircase`(3), nearest-integer recovery) as
`Fabius.staircase_round`, both in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about `a_n^±` is. (Corrected after the independent check of 7
October 2026: the write named only `Fabius.staircase_ceil` for both.)

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
Remark 10.2: (a) `N(Y)` is an **instance** of the staircase of
`p0:def:three-inverses`(1) (`n_1 = 1`); (b) Theorem 10.1 is an **analogue** of
`p0:thm:staircase`(2); (c) the nearest-integer recovery of Theorem 9.1 is an
**instance** of `p0:thm:staircase`(3); (d) the Lambert root (72) is an
**instance** of `p0:thm:lambert-core` (`a = 1`, `b = −1/2`), including its
branch rule (`W_{−1}` for `b < 0`); (e) the displacement equation (73) is a
formal **instance** of `p0:thm:core-reversion` (`Λ = 1`, `h = 0`,
`f(t,u) = −½ log(1 + tu) + Σ b_j t^j (1 + tu)^{−j}`); the analytic remainder
argument is the source's.

**Neighbouring reports.** No report of the collection treats rounded
recurrences or Laguerre amplitudes, so no reciprocal note is proposed.

**Stale claims.** Before batch 110 no file of the repository named A065094,
A065095 or A376995. The source's sentence that both records "explicitly asked
for a proof" carries a dated note: they still do, and Corollary 1.3 answers.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `A`, `A_±`; `C_±`, `c_±`, `c_j`, `c`, `C(h)`;
`L_m` (Laguerre), `L_N` (lower bracket), `L_M` (lower comparison function);
`U_N`, `U_M`; `P_n`, `Q_n`, `T_n`, `S_n`; `H_n`, `h`; `D`, `d_j`; `δ`, `d_r`; `t`,
`t_0`, `v`; `E_1`, `E_m`, `R_m`; `F_n`, `F_M`, `f_n`, `f_J`; `G_{n,k}`, `W_n`, `w_n`;
`β_N`, `b_j`, `B_n`, `b_n`; `κ`, `ℓ`, `u`, `r`; `N`, `N(Y)`, `M`, `K`. No symbol
was renamed; the volume's colliding letters carry the subscript "vol" in
Remark 10.2.

## Labels

Every label carries the prefix `rrm:` (none existed in the repository). The
manuscript's 101 labels (`eq:` 80, `sec:` 13, `thm:` 5, `cor:` 1, `lem:` 1,
`prop:` 1) were prefixed before anything cited them, and the 63 references
to them (58 `\eqref`, 5 `\ref`) updated. The write added 3:
`rrm:sec:provenance`, `rrm:rem:oeis`, `rrm:rem:transseries`. The report has 104
labels; builds of the delivered text and of this one give all 101 delivered
labels the same numbers (aux files compared). The added remarks are the last
statements of their sections, the added subsection follows the last delivered
text of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                    this guide (replaces the delivery README)
article.tex                                  the report (delivered Report186.tex; labels prefixed, [write] additions)
article.pdf                                  compiled report, 23 pages
DATA_SOURCES.md                              delivered data-source and attribution notes
README_REPRODUCIBILITY.md                    delivered reproducibility guide (delivered names)
code/reproduce.py                            replay driver, normal and -O, byte comparison (delivered at the root)
code/build.py                                PDF and ZIP builder; TeX Live (delivered at the root)
code/test_build.py                           builder and manifest tests (delivered at the root)
code/verify_manifest.py                      package-inventory checker (delivered at the root)
code/verify_source_data.py                   source-data receipt check against data/SOURCE_DATA_HASHES.json (delivered at the root)
code/certify_amplitudes.py                   orbits to N = 10000, rational amplitude enclosures (delivered code/)
code/audit_positive_sum.py                   independent positive-sum replay (delivered code/)
code/check_common_truncations.py             69-digit truncations of the six constants (delivered code/)
code/check_exact.py                          b-files, prefixes, Laguerre sums, Casoratians (delivered code/)
code/formal_series.py                        rational forward and inverse coefficients (delivered code/)
code/test_mathematical_guards.py             corruption tests (delivered code/)
code/optional-derive_coeffs_sympy.py         optional SymPy coefficient derivation (delivered optional/)
code/optional-diagnostics_sympy.py           optional SymPy diagnostics (delivered optional/)
code/optional-diagnostics_mpmath.py          optional 120-digit diagnostics (delivered optional/)
data/b065094.txt                             OEIS A065094 b-file, n = 1..1000 (Harry J. Smith; CC BY-SA 4.0)
data/b065095.txt                             OEIS A065095 b-file, n = 1..1000 (Harry J. Smith; CC BY-SA 4.0)
data/oeis_prefixes.json                      the displayed OEIS prefixes (delivered data/)
data/SOURCE_DATA_HASHES.json                 hashes of the third-party data (delivered data/)
data/certificates-amplitude_certificate.json recorded certificate (delivered certificates/)
data/certificates-common_truncations.json    recorded certificate (same)
data/certificates-exact_checks.json          recorded certificate (same)
data/certificates-formal_coefficients.json   recorded certificate (same)
data/certificates-mathematical_guards.json   recorded certificate (same)
data/certificates-positive_sum_audit.json    recorded certificate (same)
data/generated-verification.json             recorded verification result (delivered generated/)
data/generated-build_guards.json             recorded build guards (same)
data/generated-BUILD_INFO.json               recorded build information (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `code/verify_manifest.py` is a generic helper
with byte-identical copies in other reports of this collection; it is shipped
here so that the package reruns on its own. The two b-files are
byte-identical to the live OEIS files of 7 October 2026.

**Not shipped**, recoverable from the arrival commit (next section):
`Report186.pdf` (the delivered 19-page PDF, 406,407 bytes); the checksum
manifest `SHA256SUMS.json` (3,141 bytes, 32 entries), verified at placement
(repository policy ships no checksum manifests); and the delivery `README.md`
(3,711 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`README_REPRODUCIBILITY.md` and `DATA_SOURCES.md` (`Report186.tex`,
`certificates/`, `generated/`, `optional/`, `SHA256SUMS.json`, root scripts);
the programs (they locate `code/`, `data/` and `certificates/` relative to
the package root); `data/generated-*.json` (delivered paths); and Sections
7 and 11 of the article (`certificates/common_truncations.json`,
`code/*.py`, "From an extracted archive, the principal commands are …"). So no
program runs under the shipped names; use Route B below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Rounded_Running_Means_Bessel_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 5a8332939ea79cf8b812cf6423414b7d90621a0c821da21acf8cea55487d0ef1, 617,579 bytes
cd "$T" && unzip -q a.zip
```

`SHA256SUMS.json` maps the 32 other files to their SHA-256 values.

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
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a065094-rounded-running-means
B=$(mktemp -d); cd "$B"; mkdir code certificates generated optional data
cp "$R/article.tex" Report186.tex; cp "$R/DATA_SOURCES.md" "$R/README_REPRODUCIBILITY.md" .
for f in build reproduce test_build verify_manifest verify_source_data; do cp "$R/code/$f.py" .; done
for f in audit_positive_sum certify_amplitudes check_common_truncations check_exact formal_series test_mathematical_guards; do cp "$R/code/$f.py" code/; done
for f in "$R"/code/optional-*.py; do n=$(basename "$f"); cp "$f" "optional/${n#optional-}"; done
for f in SOURCE_DATA_HASHES.json b065094.txt b065095.txt oeis_prefixes.json; do cp "$R/data/$f" data/; done
for f in "$R"/data/certificates-*; do n=$(basename "$f"); cp "$f" "certificates/${n#certificates-}"; done
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
O=$(mktemp -d)/out; python -B reproduce.py --output-dir "$O"
for f in "$O"/normal/*.json; do cmp "$f" "certificates/$(basename "$f")"; done; diff -r "$O/normal" "$O/optimized"
```

At the write the driver printed `"status": "PASS"` in about 19 s; the six
normal-mode certificates were byte-identical to the shipped ones, the normal
and optimized outputs identical, and `RESULT.json` equal to
`generated/verification.json` modulo CR (Windows writes CRLF). The layout
differs from the delivery only by the missing `README.md`, `Report186.pdf`
and `SHA256SUMS.json`. Use `py` where `python` is not on the path.

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
unchanged, aux files compared): 23 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes
(the delivered text also builds without any, 19 pages). The article keeps the
delivered preamble lines that suppress PDF dates and trailer identifiers.

## From the delivery README

The delivery README (replaced by this guide) described the archive
("the manuscript, compiled report, attributed short source data, exact replay
programs, mathematical corruption checks, and an isolated deterministic
offline builder"); gave the commands `python3 -B verify_manifest.py`,
`python3 -B reproduce.py --output-dir …` and `python3 -B build.py --output …`
(new output directories outside the package; no network); listed what each
mandatory program checks (among them `formal_series.py`: "c0 through c9,
logarithmic and inverse coefficients"); and, under "Interpretation", said that
"The all-orders classical Laguerre expansion is credited prior work", that the
narrow rational intervals certify 69 common truncated digits while the printed
70-place endpoints of ceiling `A` share only 68, that "No finite onset is
certified for log-concavity, asymptotic bounds or arbitrary-threshold
inversion", and that the optional SymPy and mpmath scripts "do not replace
interval certificates".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A065094, A065095 and A376995, and the shipped `data/b065094.txt`,
`data/b065095.txt` and `data/oeis_prefixes.json` are OEIS data (b-files by
Harry J. Smith); OEIS content is published by The OEIS Foundation Inc. under
CC BY-SA 4.0 (https://oeis.org/LICENSE), and that content remains under that
licence. No third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A065094, A065095 (with Smith's
  b-files), A376995; Deaño–Huertas–Marcellán, arXiv:1301.4266v2; DLMF 10.40.1.
- Batch 110 of `docs/incoming`, bundle Report 186; arrival `60f54ea06`,
  placement `8622ca7e5`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report186.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
