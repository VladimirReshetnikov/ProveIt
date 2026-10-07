# Certified Asymptotics for Tableau Defect Clusters (OEIS A394326)

**With `a_0 = 0`, `|a_n − c ρ^{−n}| ≤ 2500 (100/63)^n` for every `n ≥ 0`, where
`0.6180397469174016 < ρ < 0.6180397783636036` and `0.1838102868 < c < 0.1838120734`
(a computer-certified unique simple dominant pole of a signed trace-class
Fredholm quotient); so the growth constant `1/ρ < 1.6180189139` is strictly
below the golden ratio, and the two asymptotic formulas of the OEIS entry,
`a(n) ~ A φ^n` and `a(n) ~ a(n−1) + a(n−2)`, are false; every fixed finite
spectral order; strict growth from `n = 600`; explicit two-ceiling threshold
brackets; a local span-marker theorem**

A research article dated 3 October 2026 ("Report183" of a session bundle),
built from one manuscript. Its author line reads "A mathematical and
computational reproducibility report" and its PDF author field "Research
report": it names no person, tool or addressee. The package carries no
"prepared for private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 183 (batch 110) | `Tableau_Defect_Clusters_Certified_Asymptotics_Source.zip` (39 files, no wrapper directory, 2,104,583 bytes, SHA-256 `442b90dea28f…95aef9676d04fb`), arrival commit `60f54ea06`; main file `Report183.tex` (835 lines, 21 pp.) | none: the package names no ProveIt commit; it cites one ProveIt report by GitHub path and blob | `8622ca7e5` (batch 110) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. Theorem 1.1 rests on a
computer certificate (exact integer and outward dyadic interval arithmetic in
Python), replayed by the shipped programs, not on a proof assistant.

## Trust boundaries

- **What is proved by hand.** The identification of the OEIS hard-rod
  extraction with the first-return quotient `C = 1 − t/J` (Section 2, Lemma
  2.1), the signed trace-class operators and the quotient `C = 1 − D/N`
  (Lemma 3.1, Proposition 3.2), the Schur-complement homotopy argument
  (Section 4), Theorem 7.1 (finite spectral expansions), the inverse arguments
  of Section 8 and Theorem 9.1 (local marker).
- **What rests on computation.** Theorem 1.1's zero count, location, residue
  and constant `M = 2500`: an exact integer computation on 8192 rational
  points of `|q| = 63/100` with a degree-bounded proof that the height-8
  polynomial `N_8` (degree 161) is the determinant (Section 4), and outward
  dyadic interval linear algebra at height 20 with frozen proposals
  (`data/inverse_proposals.json`, 1,125,229 bytes, an input of the mandatory
  certificate) accepted only through residual tests (Section 5).
  Corollary 1.2, Theorem 8.1 and `Y_0` inherit it.
- **What is diagnostic.** The refinements `ρ ≈ 0.6180397634035489`,
  `c ≈ 0.183811179648135`; the generated coefficients beyond the OEIS prefix.
- **What is prior.** The sequence, the extraction and the hard-rod recursion
  (Brydensholt, OEIS A394326; the jOEIS translation by Irvine); ballot paths,
  renewal, Fredholm determinants (Bornemann, Simon), Lagrange inversion. The
  source screen "is not a worldwide priority determination".

## What it proves

`a_n` is A394326 for `n ≥ 1`, `a_0 = 0`, `C(q) = Σ a_n q^n`, `R = 63/100`,
`M = 2500`. Statement and equation numbers are the delivered ones.

- **Theorem 1.1 (`tdc:thm:main`)**: `C` continues meromorphically to `|q| < 1`;
  `q = ρ` is its only singularity in `|q| ≤ R`, a simple pole with principal
  part `c/(1 − q/ρ)`; the bounds (1), (2); the error (3) for every `n ≥ 0`;
  `1.6180188314 < λ = 1/ρ < 1.6180189139 < φ` (4); `c = D(ρ)/(ρ N′(ρ))` (5).
- **Corollary 1.2 (`tdc:cor:empirical`)**: `a_{n+1} > a_n > 0` for `n ≥ 600`;
  `a_n/φ^n → 0`; `(a_n − a_{n−1} − a_{n−2})/a_n → 1 − ρ − ρ² ∈ (−0.00001295,
  −0.00001287)` (6).
- **Lemma 2.1 (`tdc:lem:span`)**, (9), (10): `C(t,q) = 1 − t/J(t,q)`,
  `C(q) = 1 − 1/I(q)`; **Lemma 3.1 (`tdc:lem:trace`)**, **Proposition 3.2
  (`tdc:prop:quotient`)**: `I = N/D`, `C = 1 − D/N` (15).
- **Sections 4–6**: the global count, the real location and residue (34),
  (35), the boundary resolvent bound and Cauchy estimate.
- **Theorem 7.1 (`tdc:thm:spectral`)**: every fixed zero-free radius `r < 1`
  gives a finite pole expansion (39) with `|E_{r,n}| ≤ M_r r^{−n}`.
- **Section 8**: the growth gate (40), the 125-digit `Y_0` (41); **Theorem 8.1
  (`tdc:thm:inverse`)**: `⌈x_−(y)⌉ ≤ n(y) ≤ ⌈x_+(y)⌉` (44) for `y > Y_0`,
  `x_±` the roots of `cλ^x ± MR^{−x} = y`; **Proposition 8.2
  (`tdc:prop:lagrange`)**: convergent Lagrange expansions (46), (47); the
  spectral inverse (48) with width `O(y^{−β_r})` (49).
- **Theorem 9.1 (`tdc:thm:marker`)**: an analytic marked pole `ρ(t)` and
  amplitude `c(t)` near `t = 1` with `A_n(t) = c(t)ρ(t)^{−n} + O(R^{−n})`.

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.3 (`tdc:rem:oeis`)**: the OEIS entries quoted (next section).
- **Remark 1.4 (`tdc:rem:refuted`)**: **the two OEIS asymptotic formulas
  refuted, with proof** (the section after next).
- **Remark 8.3 (`tdc:rem:transseries`)**: the inverses against the
  transseries volume, statement by statement.
- Section 1.1 (`tdc:sec:provenance`: provenance, the sources as the write read
  them, what was checked, relation to the repository, collected non-claims,
  reading conventions); a label `tdc:sec:open` on Section 10.3; a status note
  after the opening paragraph; dated notes in Sections 10.2 (the b-file) and
  10.3 (the standing rule, Questions 7 and 8).

## The OEIS entries (Remark 1.3)

Read on 7 October 2026 in the internal format; quoted verbatim in the article.

- **A394326** (revision #15, 6 April 2026; Morten Brydensholt, Mar 16 2026):
  "Total number of connected defect cluster types of weight n in the
  span-stratified cluster expansion for the row-word inversion statistic on
  standard Young tableaux of shape (m,m,m)." Forty terms; b-file `n = 1..100`
  (Sean A. Irvine); Brydensholt's Python program. Formula lines:
  "a(n) ~ A * phi^n where phi = (1+sqrt(5))/2, verified to 4 significant
  figures for n = 30..40." and "a(n) ~ a(n-1) + a(n-2) for large n
  (empirical)." Comment: "The Fibonacci residual |a(n) - a(n-1) - a(n-2)|/a(n)
  < 0.0002 for n >= 30, confirmed by Hankel determinant analysis showing
  2-state asymptotic dynamics."
- **A393486** (#28) and **A393487** (#34), Brydensholt, 16 March 2026:
  excess-tail triangles of the same clusters; not treated here.

The b-file, fetched on 7 October 2026, agrees in all 100 terms with the
write's own exact generator, and terms 1–65 with the shipped
`data/exact_coefficients.json`. Nothing was submitted to the OEIS.

## The OEIS formulas refuted (Remark 1.4)

The source states both failures (Corollary 1.2); the write records them under
Vladimir's standing rule with an explicit proof.

- **`a(n) ~ A φ^n` is false for every constant `A`.** `a_n > 0` forces `A > 0`.
  By Theorem 1.1, `a_n = c ρ^{−n}(1 + O((ρ/R)^n))`, `c > 0`, and
  `ρ > 0.6180397469 > 0.618034 > 1/φ` (`0.618034² + 0.618034 − 1 =
  6289/(25·10^{10}) > 0`), so `ρφ > 1` and `a_n/φ^n → 0`.
  `λ/φ < 0.9999907`.
- **`a(n) ~ a(n−1) + a(n−2)` is false.** `(a_{n−1} + a_{n−2})/a_n → ρ + ρ²
  ∈ (1.00001287, 1.00001295)`, not 1.
- **The observations were right as observations.** `(λ/φ)^{10} > 0.99990`, so
  the drift of `a_n/φ^n` is invisible at four significant figures over
  `30 ≤ n ≤ 40` (exact: 0.18384… at `n = 30`, 0.18375… at 40, 0.18329… at
  300). The residual comment is compatible: the limit is `−0.0000129…`, and
  the largest `|residual|` over `30 ≤ n ≤ 300` is 0.000163… (at `n = 33`);
  between 300 and about 1000 it is not certified here (Question 8). The
  "Hankel determinant analysis" is not assessed.
- **Trust boundary.** The refutation rests on the certified bracket (1), i.e.
  on the computer certificate, which the intake replayed. Independently of it,
  the write's own exact generator (the first-return walk, truncated by height;
  a larger truncation changes nothing) gives `a_1, …, a_300`, with
  `a_300/a_299 = 1.61801887065161…` inside (4) and the residual
  `−1.29125514…·10^{−5}` inside (6): corroboration, not proof.

## What is not claimed

From the source, collected in Section 1.1 of the article:

- No worldwide priority; the sequence, its extraction and the classical
  methods are credited.
- The model identification does not prove that every cluster coefficient is
  nonnegative; no bounded infinite gauge and no Perron–Frobenius argument for
  the signed operator.
- The refinements of `ρ`, `c` are not certified; `M = 2500` is transparent,
  not sharp.
- Only the dominant pole is certified: no convergent pole sum, no uniformity as
  `r ↑ 1`, no simplicity of later zeros.
- The Lagrange series expand bounding roots, not the step function; the
  spectral inverse constants are existential, and no errors `O(y^{−K})`,
  `K > 1`, are available.
- Theorem 9.1 certifies no marker radius, derivative or variance and gives no
  probability law or CLT.
- The certificates are not a machine-checked proof; hashes are not
  mathematical evidence; no publication or record edit is part of the work.

The write adds: its checks are exact finite or floating computations; it
claims no novelty for any inversion.

## Further questions

Section 10.3 of the article (`tdc:sec:open`) keeps the source's six
questions: sharper certified numerics; subdominant poles; finite-index
positivity of the cluster coefficients; span statistics; the unit circle
(continuation, accumulation, natural boundary); exact structure. Under
Vladimir's standing rule of 4 October 2026 the write found no further
unproved claim of the source and no wrong one, and adds two finite questions
its own computations leave open:

7. **Monotonicity below 600**: exact terms give `a_{n+1} > a_n` for
   `4 ≤ n < 300`; Corollary 1.2 gives `n ≥ 600`. Missing: the terms
   `300 ≤ n ≤ 600`.
8. **The OEIS residual comment for every `n ≥ 30`**: true for `30 ≤ n ≤ 300`
   and for all large `n`; the envelope (3) is effective only near `n ≈ 1000`.
   Missing: terms to that range, or a sharper envelope.

**Refuted, with proof (Remark 1.4):** A394326's `a(n) ~ A*phi^n` and
`a(n) ~ a(n-1) + a(n-2)`. **Nothing in the source was found to be wrong.**

## Checks made at intake

- At placement (batch-110 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 38/38. The
  delivered `code/run_all.py` fails on Windows only inside its two subprocess
  unit tests (CRLF text-mode output compared with LF bytes); an in-process
  driver ran the same chain: global, local, remainder, inverse, coefficients
  (65, equal to `data/exact_coefficients.json`), independent global check,
  polynomial regeneration (equal to `data/N_H8.json`), local tests — all equal
  to the delivered certificates, in 22 s. `code/generate_proposals.py`
  (mpmath 1.3.0) regenerated `inverse_proposals.json` in 19 s, identical
  modulo CRLF (the package says a regeneration need not reproduce the frozen
  proposal).
- At the write (7 October 2026; Python 3.14.4, mpmath 1.3.0; scripts in the
  intake record): every proof read line by line; in exact rationals the bounds
  (4), the value `6289/(25·10^{10})`, the band (6), the growth gate (40) and
  all 125 digits of `Y_0` (41); its own exact generator to `n = 300`
  (`ρ = 0.618039763403548969…`, `c ≈ 0.183811179648135`, matching the source's
  refinements); the 100 b-file terms; Route B below (all certificates equal,
  45 s).

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic of Remark
8.3(a) is formalized generically as `Fabius.staircase_ceil` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
nothing about `a_n` is.

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
Remark 8.3: (a) `n(y)` for `y > Y_0` is an **instance** of the staircase of
`p0:def:three-inverses`(1) (`n_1 = 600`), so `p0:thm:staircase`(1) applies;
(b) Theorem 8.1 and the spectral inverse (48) are **analogues** of
`p0:thm:staircase`(2) (direct brackets about roots of envelopes that do not
interpolate the sequence); (c) the centre `x_0` is the case `b = 0` of
`p0:thm:lambert-core`, and the equation `w = εμ(1 + w)^α` of Proposition 8.2
is a formal **instance** of `p0:thm:core-reversion` (`Λ = 1`, `h = 0`,
`f = −εt(1 + u)^α`); the source's formula for `log(1 + w)` and its
convergence are its own.

**Neighbouring reports.** The source compares with
`SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/cluster-variable-log-concavity-counterexample`
(cluster variables of a cluster algebra: only the word "cluster" is shared).
No report shares a result, so no reciprocal note is proposed.

**Stale claims.** Before batch 110 no file of the repository named A394326,
A393486 or A393487. The source's sentence that the b-file was not used carries
a dated note (Section 10.2).

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `C(q)`, `C(t,q)`, `C_0`; `c`, `c_{w,s}`,
`c(t)`; `K`, `L` (the operator) against `L = log λ` in Section 8; `D`, `N`,
`N_8`, `n`; `R`, `Res`, `r`, `r_*`; `M`, `M_r`; the states `A`, `B`, `E`
against the blocks `A_0`, `B_0`, the matrices `A_8`, `B_8`, a proposal `B`,
`A_n(t)`, `A_r(t)`, `E_{r,n}`; `I`, `Id`, `J`, `F`, `F_m`, `Z`; `G` (potential,
and `C − c/(1−q/ρ)`), `g`, `g_0`; `h` (vector, and height), `H_ζ`, `H_r`; `κ`,
`δ`, `τ`, `η`; `λ`, `ρ`, `φ`; `α`, `β`, `μ`, `x_0`, `x_±`; `x`, `y`; `u`, `v`
(`z³e_E`, and `e^{L(x−x_0)}`), `w`; `t`, `ε` (sign, and marker radius), `ε`;
`S`, `Σ`, `𝒯_s`, `T_0`; `P_j`, `𝒫_r`, `Q_n`. No symbol was renamed; the
volume's colliding letters carry the subscript "vol" in Remark 8.3.

## Labels

Every label carries the prefix `tdc:` (none existed in the repository). The
manuscript's 71 labels (`eq:` 51, `sec:` 11, `thm:` 4, `lem:` 2, `prop:` 2,
`cor:` 1) were prefixed before anything cited them, and the 59 references to
them (42 `\eqref`, 17 `\ref`) updated. The write added 5: `tdc:sec:provenance`,
`tdc:sec:open`, `tdc:rem:oeis`, `tdc:rem:refuted`, `tdc:rem:transseries`. The
report has 76 labels; builds of the delivered text and of this one give all 71
delivered labels the same numbers (aux files compared). The added remarks are
the last statements of their sections, the added subsection follows the last
delivered text of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                    this guide (replaces the delivery README)
article.tex                                  the report (delivered Report183.tex; labels prefixed, [write] additions)
article.pdf                                  compiled report, 25 pages
README_REPRODUCIBILITY.md                    delivered reproducibility guide (delivered names)
code/reproduce.py                            replay driver: run_all in normal and -O subprocesses, byte comparison (delivered at the root)
code/build.py                                PDF and ZIP builder; TeX Live (delivered at the root)
code/test_build.py                           builder and manifest tests (delivered at the root)
code/verify_manifest.py                      release-manifest checker (delivered at the root)
code/run_all.py                              runs the certificate chain and unit tests (delivered code/)
code/rigorous.py                             exact outward dyadic arithmetic for the local certificates (delivered code/)
code/certify_rational_circle.py              global zero count on |q| = 63/100 (delivered code/)
code/certify_local.py                        local signs, residue interval (delivered code/; reads data/inverse_proposals.json)
code/certify_consequences.py                 remainder, growth gate, Y_0, inverse (delivered code/)
code/independent_global_check.py             second global winding check (delivered code/)
code/regenerate_polynomial.py                regenerates N_8 exactly (delivered code/)
code/exact_coefficients.py                   65 cluster coefficients from the deficit paths (delivered code/)
code/generate_proposals.py                   optional mpmath regeneration of the dyadic proposals (delivered code/)
code/test_rational_circle.py                 unit tests with corruptions (delivered code/)
code/test_local.py                           unit tests with corruptions (delivered code/)
code/test_exact_coefficients.py              unit tests (delivered code/)
data/N_H8.json                               the degree-161 core polynomial (delivered data/)
data/adjugate_H8.json                        its adjugate (delivered data/)
data/exact_coefficients.json                 a_0..a_65 and I (delivered data/)
data/inverse_proposals.json                  frozen exact dyadic inverse proposals, 1,125,229 bytes (delivered data/)
data/certificates-global.json                recorded certificate (delivered certificates/)
data/certificates-global_independent.json    recorded certificate (same)
data/certificates-local.json                 recorded certificate (same)
data/certificates-remainder.json             recorded certificate (same)
data/certificates-inverse.json               recorded certificate (same)
data/certificates-polynomial_regeneration.json  recorded certificate (same)
data/certificates-summary.json               recorded summary (same)
data/certificates-tests_global.json          recorded test output (same)
data/certificates-tests_local.json           recorded test output (same)
data/certificates-tests_coefficients.json    recorded test output (same)
data/generated-verification.json             recorded release verification (delivered generated/)
data/generated-build_guards.json             recorded build guards (same)
data/generated-BUILD_INFO.json               recorded build information (same)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `code/verify_manifest.py` is a generic helper
with byte-identical copies in other reports of this collection; it is shipped
here so that the package reruns on its own.

**Not shipped**, recoverable from the arrival commit (next section):
`Report183.pdf` (the delivered 21-page PDF, 440,799 bytes); the checksum
manifest `SHA256SUMS.json` (3,722 bytes, 38 entries), verified at placement
(repository policy ships no checksum manifests);
`certificates/coefficients.json`, a byte copy of
`data/exact_coefficients.json`; and the delivery `README.md` (5,113 bytes),
staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`README_REPRODUCIBILITY.md` (`Report183.tex`, `certificates/`, `generated/`,
`SHA256SUMS.json`, root `reproduce.py`); the programs (they read `data/` and
write or compare `certificates/` relative to the package root, and
`reproduce.py` runs `code/run_all.py`); `data/certificates-summary.json` and
`data/generated-*.json` (delivered paths and hashes); and Section 10.1 of the
article (the command `python3 reproduce.py` "from the extracted archive
directory"; "The package README gives the individual commands"). So no program runs under the shipped names; use Route B
below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Tableau_Defect_Clusters_Certified_Asymptotics_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 442b90dea28f01a61b66b047922dd68a6db2ee56c00c834495aef9676d04fb, 2,104,583 bytes
cd "$T" && unzip -q a.zip
```

`SHA256SUMS.json` maps the 38 other files to their SHA-256 values. The frozen
proposals can also be regenerated (`python3 code/generate_proposals.py`,
mpmath 1.3.0, about 20 s; the package does not promise byte identity).

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout, POSIX** (as `README_REPRODUCIBILITY.md` gives
it), in the extraction `$T`: `python3 verify_manifest.py`,
`python3 reproduce.py`, `python3 test_build.py`. On Windows `reproduce.py` and
`run_all.py` fail inside the two subprocess unit tests (CRLF text-mode output),
not mathematically.

**Route B, from the shipped files** (tested at the write on Windows): rebuild
the delivered layout, then run the certificate chain in-process and compare.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a394326-tableau-defect-clusters
B=$(mktemp -d); cd "$B"; mkdir certificates generated data
cp -r "$R/code" .; mv code/build.py code/reproduce.py code/test_build.py code/verify_manifest.py .
for f in N_H8 adjugate_H8 exact_coefficients inverse_proposals; do cp "$R/data/$f.json" data/; done
for f in "$R"/data/certificates-*; do n=$(basename "$f"); cp "$f" "certificates/${n#certificates-}"; done
cp data/exact_coefficients.json certificates/coefficients.json
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
cp "$R/article.tex" Report183.tex; cp "$R/README_REPRODUCIBILITY.md" .
python -B -c "
import sys, json; from pathlib import Path; sys.path.insert(0, 'code')
import certify_rational_circle as g, certify_local as l, certify_consequences as k, exact_coefficients as e
import independent_global_check as i, regenerate_polynomial as p, test_local as t
d = Path('data'); r = {'global': g.run(d), 'local': l.run(d)}
r['remainder'] = k.remainder_certificate(r['global'], r['local']); r['inverse'] = k.inverse_certificate(r['local'], r['remainder'])
r['coefficients'] = e.generate(65); r['global_independent'] = i.run(d); r['tests_local'] = t.run(d)
print('N_H8', p.run() == json.loads((d / 'N_H8.json').read_text()))
[print(n, v == json.loads(Path('certificates', n + '.json').read_text())) for n, v in r.items()]"
```

At the write every line printed `True` (eight certificates and the polynomial)
in about 45 s. The layout then differs from the delivery only by the missing
`README.md`, `Report183.pdf` and `SHA256SUMS.json`; on a POSIX host Route A
also runs in it. Use `py` where `python` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, microtype, hyperref, enumitem, longtable); the
bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026: 25 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes
(the delivered text also builds without any, 21 pages). The article keeps the
delivered preamble lines that suppress PDF dates and trailer identifiers.

## From the delivery README

The delivery README (replaced by this guide) stated the main result and that
"The source's strict golden-ratio and Fibonacci asymptotic equivalents
therefore fail; its weaker observed small relative Fibonacci residual remains
compatible"; listed what the report proves and that it "does not claim
all-index coefficient positivity, a probability law or CLT, a list of later
poles, continuation through the unit circle, or worldwide priority"; credited
the extraction to Brydensholt and the inspected implementation to Irvine's
jOEIS translation (blob `e59ad7a42e0c96f832b97b6457ea9b5cb1d4a851`), with no
third-party source redistributed; gave the POSIX verification commands (about
36 s; replay in temporary storage outside the archive); said that the
inverse proposals "are exact dyadic candidates, not trusted approximate
answers"; and gave the PDF and ZIP rebuild commands. "No external publication
or repository submission is part of this package."

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A394326, A393486 and A393487; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that
content remains under that licence (`code/exact_coefficients.py` embeds the
forty printed terms as a check). No third-party program or PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A394326; Irvine's jOEIS
  `A394326.java`; Bornemann, Math. Comp. 79 (2010) and its erratum; Simon,
  Adv. Math. 24 (1977); the ProveIt cluster-variable report; Li's 2026
  ribbon-tableau manuscript. Added by the write: OEIS A393486, A393487 (named
  by the source, now cited in Remark 1.3).
- Batch 110 of `docs/incoming`, bundle Report 183; arrival `60f54ea06`,
  placement `8622ca7e5`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report183.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
