# Distinct Multiplicity Values in Integer Partitions (OEIS A373271 and A373273)

**Part I: the mean number of distinct multiplicity values of a partition of
`n` is `(6n)^{1/4} − 23/16 + K n^{−1/4} + O(n^{−1/2})`,
`K = (π/6^{1/4})(12365/82944 + 15/(8π²))`, where `−23/16` needs an exact
telescoping tail `−1/2`; total counts, eventual increase and a shrinking
two-ceiling inverse. Part II: the mean sum of the distinct multiplicity
values has the five scales `√n log n`, `√n`, `n^{1/4}`, `log n`, `1` with error
`O(n^{−1/4})`, leading term `√(6n) log n/(4π)`, the constant involving a
delta square and a finite-difference tail in which `ζ′(−1)` cancels; absolute
expansion, eventual increase and a shrinking two-ceiling inverse. One exact
identity `Σ a_n qⁿ = P(q) Σ_m w(m)(1 − Q_m(q))` with `w = 1` and `w(m) = m`**

A research report bound from two manuscripts dated 4 October 2026 ("Report
197" and "Report 198" of a session bundle). Their author lines and PDF author
fields read "Report 197" and "Report 198": they name no person, tool or
addressee. Neither package carries a "prepared for private review" line, an
e-mail address or personal data.

| Part | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | Report 197 (batch 111, base) | `Report197_TeX_and_Reproducible_Code.zip` (14 files, no wrapper directory, 793,611 bytes, SHA-256 `192aeca1a0b8…bc038875d653adc`), arrival commit `60f54ea06`; main file `Report197.tex` (759 lines, 18 pp.) | none | `d451ef3d8` (batch 111) | Part I, Sections 1–11, labels `dmv:cnt:` |
| II | Report 198 (batch 111) | `Report198_TeX_and_Reproducible_Code.zip` (17 files, no wrapper directory, 909,536 bytes, SHA-256 `8d10255b48c3…8eacce24e871492`), arrival commit `60f54ea06`; main file `Report198.tex` (663 lines, 17 pp.) | none | `d451ef3d8` (batch 111) | Part II, Sections 12–24, labels `dmv:sum:` |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## How the merge was made

- **Base and order.** Report 197 is the base: its `Report197.tex` was staged
  as `article.tex`, it arrived first, and Report 198's package was adapted
  from it. Report 198 is printed second. Neither Part cites the other, and
  Report 198's README says that "No A373271 theorem or coefficient is used as
  a mathematical premise"; the merge claims no result relating the two
  statistics beyond the shared identity.
- **What binds them.** The same identity with weights `1` and `m`; the same
  whole-circle bound through the positive products `P_m = P Q_m`; the same
  local saddle transfer; and Part II answers Part I's Question 4 (weighted
  occupied values) for `w(m) = m`, leaving `m^α` open (Part II's Question 2).
  A373271's OEIS entry itself points to A373273.
- **Duplication.** Part II re-derives the sector estimates (its Section 14,
  against Part I's Sections 3–4), the whole-circle bound (Section 19, against
  Section 6) and the monomial transfer (Section 20, against Lemma 7.1); each
  is kept with a dated note naming Part I's counterpart, because Part II's
  later statements cite them by their own labels, the circle bound carries
  the weight's factor `n(n+1)`, and the transfer is a second route proved for
  complex `s`.
- **Numbering.** Sections are continuous. Part I keeps every delivered
  number; Report 198's Section `k` is Section `k + 11` here and its equation
  `(k.m)` is `(k+11.m)`; its Table 1 keeps its number.
- **Bibliography.** Merged; the two OEIS keys (both delivered as `oeis`) are
  `oeisA373271` and `oeisA373273`; the four shared works are printed once
  with each Part's own inspection note.

## Trust boundaries

- **What is proved by hand.** Both Parts' exact identities, uniform sector
  expansions with summed matched remainders (Part I Proposition 4.2,
  Theorem 5.1; Part II Lemma 15.1, Proposition 18.1), whole-circle
  localization, local saddle transfer (Part I Lemma 7.1; Part II Section 20,
  including differentiation in `s`), the means and totals, monotonicity and
  the inverses. No proof uses a computation.
- **What rests on computation.** Nothing in the proofs; the packages check
  the rational identities in exact `Fraction` arithmetic.
- **What is diagnostic.** Part I's table of `T(n)` and Part II's Table 1, the
  floating diagnostics of Part II, and all finite agreements. Remainder
  constants and onsets are existential.
- **What is prior.** Ralaivaosaona's multiplicity limit theorems (the
  `n^{1/4}` transition that "naturally suggests" Part I's leading mean),
  the Grabner–Knopfmacher–Wagner transfer scheme, the modular identity,
  Corteel–Pittel–Savage–Wilf and Lugo (overlap not excluded: abstract-level
  and targeted reading only).

## What it proves

`M_j` is the multiplicity of the size `j`; `A = π²/6`, `τ = √(A/(n − 1/24))`.
Statement and equation numbers are those of this file (Part II shifted by
eleven sections).

**Part I** (`D(λ)` = number of distinct positive values of the `M_j`;
`a(n) = Σ D`, A373271):

- **Proposition 2.1 (`dmv:cnt:prop:gf`)**: `Σ a(n)qⁿ = P(q) Σ_m (1 − Q_m(q))`.
- **Theorem 5.1 (`dmv:cnt:thm:radial`)**: `g(t) = √π t^{−1/2} − 23/16 +
  √π d t^{1/2} + O(|t|)` in a sector, `d = 12365/82944`; the constant needs
  the telescoping `Σ δ_m = −1/2` (3.9).
- **Theorem 1.1 (`dmv:cnt:thm:mean`)**: the three-term mean (1.3)–(1.4),
  `K = 0.68058214956683591885…`.
- **Theorem 1.2 (`dmv:cnt:thm:total`)**: `a(n) = C e^{Bx} x^{−3/2}(1 + b_1
  x^{−1/2} + b_2 x^{−1} + O(x^{−3/2}))`, `x = √(n − 1/24)`; eventual strict
  increase.
- **Theorem 1.3 (`dmv:cnt:thm:inverse`)**: `⌈Z(Y) − C_1 x_0^{−1/2}⌉ ≤ N(Y) ≤
  ⌈Z(Y) + C_1 x_0^{−1/2}⌉`, `x_0` a Lambert `W_{−1}` root.

**Part II** (`W(λ)` = sum of the distinct positive values; `a_n = Σ W`,
A373273):

- **(13.3)**: `Σ a_n qⁿ = P(q) Σ_m m(1 − Q_m(q))`.
- **Proposition 18.1 (`dmv:sum:prop:radial`)**: `w(t) = (½ log(1/t) + c)/t −
  7√π/(16√t) + (1/24) log(1/t) + K + O(√|t|)`, `c = 3/2 − γ/2`,
  `K = 9607/20736 − γ/24`.
- **Theorem 12.1 (`dmv:sum:thm:mean`)**: the five-scale mean (12.3)–(12.4).
- **Theorem 12.2 (`dmv:sum:thm:absolute`)**: `a_n = C_N[…]` (12.5); eventual
  strict increase.
- **Theorem 12.3 (`dmv:sum:thm:inverse`)**: two ceilings for the first
  crossing `ν(Y)`, unrounded endpoints `v_Y + O((log Y)^{−1/2}/log log Y)`.

Added by the write (7 October 2026), marked `[write]`:

- **Guide to this report** (`dmv:sec:guide`, before Part I): the Parts, the
  comparison table, the merge choices, provenance, sources read, checks,
  relation to the repository, collected non-claims of both Parts, and a
  two-column table of reading conventions.
- **Remark 1.4 (`dmv:cnt:rem:oeis`)** and **Remark 12.4
  (`dmv:sum:rem:oeis`)**: the OEIS entries (next section).
- **Remark 9.1 (`dmv:cnt:rem:transseries`)**: (a) **instance**: `N(Y)` is the
  staircase of `p0:def:three-inverses`, so `p0:thm:staircase`(1) applies;
  (b) **instance**: `x_0(Y)` is `p0:thm:lambert-core`(3), `b < 0`, in
  `X_vol = x` (`a_vol = B`, `b_vol = −3/2`, `L_vol = log(Y/C)`);
  (c) **formal instance**: the envelopes are exactly exponential–power with
  `δ_vol = 1/2`, and the centre of (9.3) is `p0:prop:two-grid` with
  `δ = 1/2`; the volume's analytic reversion is for `δ = 1` only, so the
  remainder is the source's, whose residual-over-slope step is
  `p0:thm:backward-error`; (d) **analogues**: (1.10) and (9.5) of
  `p0:thm:staircase`(2).
- **Remark 21.1 (`dmv:sum:rem:transseries`)**: (a) **instance** of
  `p0:thm:staircase`(1); (b) **not shown to be an instance**: `log Φ` contains
  `log log x`, outside `p0:def:model`; it is an admissible core of
  `p0:def:core` only by definition, and the initializer (21.4) is not shown to
  be an instance of `p0:thm:flattening`; (c) **instance**: the root error
  (21.3) is `p0:thm:backward-error`; (d) **analogue**: (12.9) of
  `p0:thm:staircase`(2).
- Notes: the three Part I counterparts in Part II (end of Sections 14, 19,
  20); the question notes at the ends of Part I's Questions and Part II's
  Section 24; the merged-bibliography note.

## The OEIS entries (Remarks 1.4 and 12.4)

Read on 7 October 2026 in the internal format.

- **A373271** (revision #15, 2 June 2024; _Olivier Gérard_, 29 May 2024),
  offset 1: "a(n) = sum for all integer partitions of n of the number of
  distinct multiplicities in each partition."; row sums of A373269 and
  A373270; "If all distinct multiplicities of all parts of all integer
  partitions are summed, one gets A373273 (1, 3, 5, 11, 18, 29, 48, 74, 107,
  161, ...)."; b-file by Alois P. Heinz (`1 ≤ n ≤ 200`). No formula,
  asymptotic or conjecture. Report 197 could not open the b-file; the write
  fetched it (SHA-256 `b30df65d4321…ae401d`): all 200 terms agree with the
  shipped table, as do the 45 data terms. The bibliography's quoted name
  ("Sum of number of distinct multiplicities over all partitions of n.") is a
  paraphrase; kept, and Remark 1.4 says so.
- **A373273** (revision #14, 1 June 2024, the revision Report 198 read;
  _Olivier Gérard_): "a(n) = sum of all distinct multiplicities in every
  integer partition of n."; 43 terms; "Sum of the rows of triangle A373272.".
  The live text is identical to the shipped `data/198-sum-A373273.seq`. No
  formula, asymptotic or conjecture.
- The write enumerated all partitions of `n ≤ 55` by multiplicity vectors and
  computed both statistics: all agree with the shipped tables. Nothing was
  submitted to the OEIS.

## What is not claimed

From both Parts, kept in the article (collected in the Guide):

- **Part I**: finite order only; no explicit constants or onset; no variance,
  fluctuation or central limit theorem; no exact single-ceiling inverse (no
  values of `C_1`, `Y_0`); no interpolation assumed; no absolute novelty,
  complete coverage or priority (Corteel–Pittel–Savage–Wilf read only at
  abstract level, Lugo at targeted passages); no b-file comparison by the
  source.
- **Part II**: no explicit onset or certified constant, no all-orders
  expansion, no distributional theorem, no single exact ceiling for every
  `Y`, no numerical `X, M, n_0`, no exponentially small final remainder, no
  new general transfer theorem, no novelty; comparisons with Archibald et
  al., Fill–Janson–Ward, Corteel–Pittel–Savage–Wilf and Lugo are not
  exclusion certificates; diagnostics and the inverse root calculation are
  not interval-certified.

The write adds: its checks are floating, finite or hand computations; the
transseries remarks claim no novelty for any inversion; the merge claims no
relation between the two statistics beyond the shared identity.

## Further questions

Part I's Section 11.2 keeps its five questions (one further matched order;
variance and fluctuations; effective error bounds; weighted occupied values;
the literature comparison) and Part II's Section 24 its five (the next matched
order; other weights `m^α`; explicit inverse certification; weighted
fluctuations; a fuller source comparison). Dated notes record that Part II
answers Part I's Question 4 for `w(m) = m` only, that `α = 0` and `α = 1` are
the two Parts and the family `m^α` stays open, that both tables increase
strictly from `n = 1` (no onset proved), and that under Vladimir's standing
rule of 4 October 2026 nothing was moved or refuted. **No claim of either
source was found to be wrong or unproved.**

## Checks made at intake

- At placement (batch-111 dossier, 7 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; both delivered suites reproduce
  their outputs on copies (failures only Windows artifacts).
- At the write (7 October 2026; same machine; Python 3.14.4, mpmath 1.3.0):
  all four checksum manifests verified (13 + 7, 16 + 9 entries); every proof
  of both Parts read line by line (the Guide lists the steps rechecked by
  hand); the two regularized integrals of Part II (`∫ y b′² = −13/72 −
  2ζ′(−1) − γ/6 = 0.05408412102842415943…`, `R_D = −ζ′(−1) − γ/12 =
  0.11731983829198985749…`) and `∫ y b″(2y) dy = −1/8` numerically; `K` of
  Part I (the printed digits are a truncation); every entry of Part I's
  `T(n)` table and of Part II's Table 1 (all printed digits agree); bounded
  residuals of both mean expansions and of the absolute expansions; the
  brute force to 55; partition numbers to 2500 by Euler's recurrence; both
  b-files. Rerun from the shipped files (routes below): Part I `verify.py`
  (≈ 30 s) and `symbolic_checks.py`, Part II `verify.py` (≈ 30 s),
  `symbolic_checks.py` and `diagnostics.py`: receipts and term tables
  byte-identical to the shipped records, except the sector Boltzmann rows of
  Part II's floating diagnostics, whose 15 residual values agree with the
  record only to about ten significant digits (floating library and platform;
  the delivered README promises no cross-platform floating identity; the
  other diagnostic rows are identical).
- Sources read by the write: the OEIS entries; the transseries volume
  (labels in the Guide). Not read: the cited literature.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remarks
9.1(a) and 21.1(a) is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about these sequences is formalized.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a239964-sizes-equal-max-multiplicity` (batch 111; kept apart at placement
because `D = M` is not an occupied-value functional and no source cites
another) and `a239950-maximal-schreier-supports` (batch 111). They share the
Boltzmann occupancy setting and the damping argument, not a result; no
reciprocal note is proposed.

**Stale claims.** Before batch 111 no file of the repository named A373271 or
A373273.

## Notation

The Guide's table puts the two Parts side by side: `a(n)`, `a_n`; `D`
(Part I's statistic, Part II's delta correction), `W` (Part II's statistic)
and Lambert's `W_{−1}`; the two `K` and the two `d`; `c`, `k`; `B` and the
Bose factor (`𝓑` in Part I, `B(z)` in Part II); `C`, `C_N`, `C_0`; `ν` and `N`
swapped between the Parts (`ν = n − 1/24` and `N(Y)` in Part I,
`N = n − 1/24` and `ν(Y)` in Part II); `ℓ`; `Φ` (a template for `log a(n)` in
Part I, for `a_n` in Part II) and `H_±`; `x`; `Z`; `L`; `E`; `G`, `F`; `T`;
`M`, `X`; `a = s + 1/2` and `β`. No symbol was renamed.

## Labels

Report 197's 89 labels (`eq:` 69, `sec:` 11, `thm:` 4, `lem:` 3, `prop:` 2) carry
`dmv:cnt:` and Report 198's 78 (`eq:` 59, `sec:` 13, `thm:` 3, `lem:` 1,
`prop:` 1, `tab:` 1) carry `dmv:sum:`; the 50 and 44 references to them
(36 and 38 `\eqref`, 14 and 6 `\ref`) were updated. The write added 7:
`dmv:sec:guide`, `dmv:cnt:part`, `dmv:sum:part`, `dmv:cnt:rem:oeis`,
`dmv:cnt:rem:transseries`, `dmv:sum:rem:oeis`, `dmv:sum:rem:transseries`.
The report has 174 labels. Builds of the two delivered texts and of this one
were compared: all 89 Part I labels keep their numbers, and all 78 Part II
labels keep theirs up to the shift of eleven sections (Table 1 unchanged).

## Files

```text
README.md                                          this guide (replaces Report 197's delivery README)
article.tex                                        the merged report (Report197.tex and Report198.tex; labels prefixed, [write] additions)
article.pdf                                        compiled report, 41 pages
code/197-count-verify.py                           Part I exact checks: Q-product to 2000, positive DP to 400, Ferrers gaps to 45 (delivered verify.py)
code/197-count-symbolic_checks.py                  Part I Fraction identities (delivered symbolic_checks.py)
code/197-count-build.py                            Part I deterministic builder (delivered build.py)
code/197-count-guard_tests.py                      Part I guard and rebuild tests (delivered guard_tests.py)
code/198-sum-verify.py                             Part II exact checks: Q-product to 2500, positive DP to 450, Ferrers gaps to 43 (delivered verify.py)
code/198-sum-symbolic_checks.py                    Part II Fraction identities, 35 checks (delivered symbolic_checks.py)
code/198-sum-diagnostics.py                        Part II floating diagnostics (delivered diagnostics.py)
code/198-sum-build.py                              Part II deterministic builder (delivered build.py)
code/198-sum-guard_tests.py                        Part II guard and rebuild tests (delivered guard_tests.py)
data/197-count-exact_A373271.txt                   n, a(n), p(n) for n = 0..2000 (delivered data/)
data/197-count-generated-exact_terms.txt           recorded terms (delivered generated/; byte-identical to the previous file)
data/197-count-generated-verification.json         recorded verification (delivered generated/)
data/197-count-generated-guard_results.json        recorded guard results (same)
data/197-count-generated-BUILD_INFO.json           recorded build parameters (same)
data/198-sum-exact_A373273.txt                     n, a_n, p(n) for n = 0..2500 (delivered data/)
data/198-sum-A373273.seq                           OEIS internal record of A373273, revision #14 (delivered data/)
data/198-sum-generated-exact_terms.txt             recorded terms (delivered generated/; byte-identical to exact_A373273.txt)
data/198-sum-generated-verification.json           recorded verification (delivered generated/)
data/198-sum-generated-diagnostics.json            recorded floating diagnostics (same)
data/198-sum-generated-guard_results.json          recorded guard results (same)
data/198-sum-generated-BUILD_INFO.json             recorded build parameters (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Within each Part, the exact table and the
recorded `exact_terms.txt` are byte-identical; both are shipped as delivered
records.

**Not shipped**, recoverable from the arrival commit: `Report197.pdf` (18
pages, 388,482 bytes) and `Report198.pdf` (17 pages, 386,127 bytes); the
checksum manifests (Report 197: `MANIFEST.json` 1,962 bytes, 13 entries;
`SOURCE_MANIFEST.json` 1,098 bytes, 7 entries; Report 198: 2,379 bytes, 16
entries; 1,369 bytes, 9 entries), verified at the write; Report 198's
`Report198.tex` (44,640 bytes; it is Part II of `article.tex`) and its
delivered `README.txt` (12,013 bytes); and Report 197's `README.txt` (10,387
bytes), staged at placement as `README.md` and replaced by this guide (both
READMEs summarized below).

**Delivered text that names the delivery layout or files not shipped.** The
programs (under their delivered names, with `data/` beside them; the
builders and guard tests require the manifests, README and TeX of their
package), and Sections 10 and 22 of the article ("See its `README.txt`", "The
code archive contains the TeX source…", "The accompanying README gives exact
commands").

## Retrieving the delivered packages

```sh
T=$(mktemp -d); cd "$T"
for r in 197 198; do
  git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Report${r}_TeX_and_Reproducible_Code.zip > $r.zip
  mkdir $r && (cd $r && unzip -q ../$r.zip)
done
sha256sum 197.zip 198.zip
# 192aeca1a0b861c1394c06845b1c542aa0292b8623e69dde4bc038875d653adc  (793,611 bytes)
# 8d10255b48c353ec3f9d203348e91c5e9e78f47281a13f2238eacce24e871492  (909,536 bytes)
```

## Rerun the checks (on a scratch copy)

Python 3.9 or later, standard library only. Never run anything in the
repository.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a373271-distinct-multiplicity-values
B=$(mktemp -d)
for r in 197-count 198-sum; do
  mkdir -p "$B/$r/data"
  for f in "$R"/code/$r-*.py; do n=$(basename "$f"); cp "$f" "$B/$r/${n#$r-}"; done
done
cp "$R/data/197-count-exact_A373271.txt" "$B/197-count/data/exact_A373271.txt"
cp "$R/data/198-sum-exact_A373273.txt" "$B/198-sum/data/exact_A373273.txt"
cp "$R/data/198-sum-A373273.seq" "$B/198-sum/data/A373273.seq"
(cd "$B/197-count" && python -I -S -B verify.py --output "$B/v197.json" --terms-output "$B/t197.txt" && python -I -S -B symbolic_checks.py)
(cd "$B/198-sum" && python -I -S -B verify.py --output "$B/v198.json" --terms-output "$B/t198.txt" && python -I -S -B symbolic_checks.py && python -I -S -B diagnostics.py > "$B/d198.json")
cmp "$B/v197.json" "$R/data/197-count-generated-verification.json"
cmp "$B/t197.txt" "$R/data/197-count-generated-exact_terms.txt"
cmp "$B/v198.json" "$R/data/198-sum-generated-verification.json"
cmp "$B/t198.txt" "$R/data/198-sum-generated-exact_terms.txt"
diff "$B/d198.json" "$R/data/198-sum-generated-diagnostics.json"
```

At the write the four `cmp` were silent and both symbolic checks printed
`"status": "PASS"`; the `diff` showed only the sector Boltzmann residuals,
equal to about ten significant digits (and line endings on Windows). Use `py` where `python` is not on
the path. The builders and guard tests were not rerun by the write; take
their packages from the archives.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, xcolor, enumitem, fancyhdr, hyperref, and
longtable for the Guide); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026 (41
pages): no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered texts also build without any, 18 and 17
pages).

## From the delivery READMEs

Report 197's README (replaced by this guide) defined the statistic, said that
exact computations "check definitions, coefficient algebra, and
reproducibility; they do not replace the analytic proof" and that "No central
limit theorem, proved variance asymptotic, all-fixed-orders theorem,
effective onset/error constant, exact single-ceiling inverse, or exhaustive
worldwide novelty claim is made"; gave the commands; described the
Q-product algorithm, the positive DP through 400, the Ferrers-gap check
through 45 and the pentagonal check through 2000; said the 45 displayed OEIS
terms were compared and "No comparison with the linked OEIS b-file is
claimed"; and described the manifests, deterministic builds and guard tests.
Report 198's README (not shipped) did the same for the weighted sum (Q-product
through 2500, positive DP through 450, Ferrers gaps through 43, 35 exact
symbolic checks, floating diagnostics "never" supplying a remainder constant,
the pinned `A373273.seq` record) and stated that its infrastructure was
"adapted from the preceding Report197 reproducibility package" and that "No
A373271 theorem or coefficient is used as a mathematical premise."

## Rights

Repository contents are MIT-0. The article and this README quote OEIS entries
A373271 and A373273, and `data/198-sum-A373273.seq` is the OEIS internal
record of A373273 (Olivier Gérard); OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that
content remains under that licence. No third-party PDF is shipped. Nothing
was submitted to the OEIS.

## Provenance

- Sources cited by the manuscripts: OEIS A373271, A373273, A373272;
  Ralaivaosaona, Ann. Comb. 16 (2012); Grabner–Knopfmacher–Wagner, CPC 23
  (2014); Corteel–Pittel–Savage–Wilf, RSA 14 (1999); Lugo, PhD thesis (2010);
  Archibald et al., AJC 66 (2016); Fill–Janson–Ward, EJC 19 (2012). Nothing
  added by the write.
- Batch 111 of `docs/incoming`, bundle Reports 197 and 198; arrival
  `60f54ea06`, placement `d451ef3d8`, written 7 October 2026.
