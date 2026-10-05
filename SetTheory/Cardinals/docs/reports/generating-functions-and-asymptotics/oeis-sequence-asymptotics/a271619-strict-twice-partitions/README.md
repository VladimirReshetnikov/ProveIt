# Strict Twice Partitions

**Phase-resolved asymptotics for A271619, and nested partitions with distinct block lengths (A358836)**

> **Read this first: Part I's main theorem is an eventual result only.**
> Report 182 says so itself, before its table of contents: its expansion
> holds as `n → ∞` with a non-effective onset, and it is not a practical
> approximation at moderate sizes. At `n = 5000` its leading two-charge
> formula divided by the exact `a(5000)` is about `0.00177838`, i.e. the
> formula is about **562 times too small**; with the first correction the
> ratio is `0.00486243` (about 206 times too small). An ordinary single
> Gaussian happens to give `1.00047777` there, which proves nothing about
> its eventual validity. There is no finite-`n` accuracy theorem.

This is a research report built on 5 October 2026 (write batch 100) from
two manuscripts of one external research session, Reports 182 and 181 of
the session bundle of Reports 1–243, both dated 3 October 2026. Both count
*twice partitions with a strict outer level*: finite collections of
ordinary partitions (blocks) in which no two blocks share the value of one
statistic.

- **Part I** (Report 182, the base): OEIS
  [A271619](https://oeis.org/A271619), `a(n) = [qⁿ] ∏_{k≥1} (1 + p(k) qᵏ)`,
  blocks of distinct **sizes**. A phase-resolved expansion to every fixed
  relative order, through two effective charges that exchange dominance near
  the triangular phase `9/16`, with a persistent low-hole cloud.
- **Part II** (Report 181): OEIS [A358836](https://oeis.org/A358836),
  `a_n = [qⁿ] ∏_{k≥1} (1 + qᵏ/(q;q)_k)`, blocks of distinct **lengths**
  (numbers of parts). Every fixed order of the free energy and of the
  exact-saddle Edgeworth expansion, an elementary relative equivalent,
  controlled inversion, and Gaussian and Gumbel limit laws.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Report182: Phase resolved asymptotics for A271619* (base); author line "A rigorous asymptotic and reproducibility report" | 182 | `Strict_Twice_Partitions_Phase_Asymptotics_Source.zip` (2,961,159 bytes, 38 files; `Report182.tex`, 1,148 lines, 30 pp.) | none (cites `main` URLs of the A022629 README and the A291698 article) | `36571ae0e` | Part I, Sections 4–15 |
| *Nested Partitions with Distinct Block Lengths: All fixed asymptotic orders, explicit relative growth, inverse bounds and conditioned limits for OEIS A358836*; author line "Research report 181" | 181 | `Nested_Partitions_Asymptotics_and_Inverses_Source.zip` (692,760 bytes, 32 files; `Report181.tex`, 898 lines, 21 pp.) | none (its source audit records the git blob hashes `ef1b42ed`, `1100837c`, `36949d3f` of the A022629 README and the A291698 README and article; all three equal the repository files at the write) | `36571ae0e` | Part II, Sections 16–27 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `36571ae0e` (batch 100, cluster DPP) removed them from
`docs/incoming/`. The write is batch 100's "Write batch 100: strict twice
partitions and nested partitions as the new report
a271619-strict-twice-partitions".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Part I's author line, "A rigorous asymptotic and
reproducibility report", is **the manuscript's description of itself**, not
an assessment by a referee or by this repository; the reviews named in its
"Review record" belong to the delivering session and their records are not
part of the delivery. Neither manuscript names an author, says it is
AI-assisted, or carries "prepared for private review" wording; Report 182
says it was not submitted externally. Every result, proof, example, remark,
question and limitation of both manuscripts is printed.

## Files

The directory holds 63 files: 9 at the root, 24 in `code/`, 30 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 182, prefix `182-strict-`**: 33 files besides the article (3 at the
root, 14 in `code/`, 16 in `data/`); its `Report182.tex` is the base of
`article.tex`. Root: the package's code guide, source/build audit and
optional-diagnostics guide. `code/`: the exact core (`exact.py`,
`verify.py`, `regenerate.py`), the second-order supplement
(`second_order.py`, `verify_second_order.py`, `second_order_guard_tests.py`),
the guard and build tests, the builder, the manifest checker, the optional
binary64 diagnostics and two frozen historical checkers (`references-*`).
`data/`: certificates, provenance records, the generated receipts of the
delivered build, the frozen partition-number table `p(0..10000)` and frozen
reference results.

```
182-strict-README_CODE.md
182-strict-SOURCE_AUDIT.md
182-strict-optional-README.md
code/182-strict-build.py
code/182-strict-exact.py
code/182-strict-guard_tests.py
code/182-strict-optional-frozen_float_diagnostics.py
code/182-strict-optional-run_diagnostics.py
code/182-strict-references-exact_checks_frozen.py
code/182-strict-references-independent_a2_check_frozen.py
code/182-strict-regenerate.py
code/182-strict-second_order.py
code/182-strict-second_order_guard_tests.py
code/182-strict-test_build.py
code/182-strict-verify.py
code/182-strict-verify_manifest.py
code/182-strict-verify_second_order.py
data/182-strict-PROVENANCE.json
data/182-strict-SECOND_ORDER_PROVENANCE.json
data/182-strict-certificates.json
data/182-strict-generated-BUILD_INFO.json
data/182-strict-generated-build_guards.json
data/182-strict-generated-second_order_guards.json
data/182-strict-generated-second_order_verification.json
data/182-strict-generated-verification.json
data/182-strict-generated-verification_guards.json
data/182-strict-optional-reference_results.json
data/182-strict-references-exact_results.json
data/182-strict-references-independent_a2_check_frozen.json
data/182-strict-references-partitions_0_10000.txt
data/182-strict-references-reference_hole_constants.json
data/182-strict-references-second_order_root_brackets.json
data/182-strict-second_order_certificate.json
```

**Report 181, prefix `181-nested-`**: 27 files (3 at the root, 10 in
`code/`, 14 in `data/`). Root: the package's code guide, source and overlap
audit, and optional-diagnostics guide. `code/`: the exact core, guard and
build tests, the builder, the optional diagnostics wrapper and three frozen
mpmath scout scripts. `data/`: the certificate, provenance, generated
receipts of the delivered build, frozen exact terms `a_0..a_600`, frozen
scout and audit results, and the optional requirements.

```
181-nested-README_CODE.md
181-nested-SOURCE_AUDIT.md
181-nested-optional-README.md
code/181-nested-build.py
code/181-nested-exact.py
code/181-nested-guard_tests.py
code/181-nested-optional-run_diagnostics.py
code/181-nested-optional-scout-verify_marked.py
code/181-nested-optional-scout-verify_maximum.py
code/181-nested-optional-scout-verify_nested_partitions.py
code/181-nested-regenerate.py
code/181-nested-test_build.py
code/181-nested-verify.py
data/181-nested-PROVENANCE.json
data/181-nested-certificates.json
data/181-nested-generated-BUILD_INFO.json
data/181-nested-generated-build_guards.json
data/181-nested-generated-verification.json
data/181-nested-generated-verification_guards.json
data/181-nested-optional-requirements.txt
data/181-nested-references-FROZEN.json
data/181-nested-references-exact_terms_0_600.txt
data/181-nested-references-independent_checks.json
data/181-nested-references-marked_formal_coefficients.json
data/181-nested-references-marked_verification.json
data/181-nested-references-maximum_verification.json
data/181-nested-references-verification.json
```

**Not shipped** (all retrievable from `60f54ea06`): both PDFs
(`Report182.pdf`, `Report181.pdf`); both `SHA256SUMS.json` manifests
(verified 37/37 and 31/31 at placement; repository policy drops checksum
manifests); both delivery READMEs (182's was staged and is replaced by this
guide; 181's was not staged); `Report181.tex` (printed as Part II); 181's
`verify_manifest.py` (byte-identical to `code/182-strict-verify_manifest.py`);
and 182's `data/references/coefficients_0_5000.txt` (1,426,621 bytes,
`a(0..5000)`), which `code/verify.py` reads and pins — see "Reconstructing
the excluded data".

## Labels and numbering

Label prefix **`stp:`**: Part I uses `stp:sum:` (Report 182's 105 labels),
Part II `stp:len:` (Report 181's 81 labels); the front matter and the
appendix use `stp:` (`stp:sec:guide`, `stp:sec:notation`,
`stp:tab:notation`, `stp:sec:limits`, `stp:app:provenance`,
`stp:tab:crosswalk`), and the write added `stp:sum:part`, `stp:len:part`,
`stp:sum:sec:further` and `stp:sum:sub:floating`. 196 labels in all.

Sections are numbered continuously, so the manuscripts' numbers shift:
Part I's Section `k` is Report 182's Section `k − 3`; Part II's Section `k`
is Report 181's Section `k − 15`; theorems are numbered within sections and
shift with them. Equation numbers are continuous: Part I's are Report
182's (1)–(83), and Part II's equation (`j`) is Report 181's (`j − 83`). The
delivered READMEs, audits and code use the manuscripts' own numbers.
Appendix A's Table 2 maps every numbered result; for example Report 182's
Theorem 1.1 is Theorem 4.1 here, and Report 181's Theorem 8.1 is Theorem 23.1.

## Notation

No symbol was renamed. Each Part keeps its manuscript's letters; Section 2
(Table 1) lists every letter with different meanings in the two Parts,
with the tempting false reading. The most dangerous is **`b`**: in Part I
the constant `b = π√(2/3)` (so `log p(k) ~ b√k`), in Part II the variance
`b = L''(t_n) ~ 6A²t_n⁻⁵`. Others: `a` (Part I's `a = 21/5` against Part
II's `a = A²/2 = π⁴/72`), `B_n` (a Bernoulli variable against a tier
constant), `E_2` (an Eisenstein series or a charge carrier against the
second Edgeworth correction), `F` (a logarithm in Part I, a generating
function in Part II), `L`, `M`, `μ`, `Q_2`, `T_m`, `Z`, and the inverse
counting functions `N` (Part I: `min{n : log a(n) ≥ Y}`; Part II:
`max{n : a_n ≤ x}`, which differ by one at a non-attained threshold). Both
Parts use `A = π²/6`, `E`, `Var`, `q = e^{-t}` and `K_n` (the number of outer
blocks) in the same sense.

## What the report claims

**Part I (A271619).**
- Theorem 4.1: for every fixed `J`, `a(n) = 𝒜_J(n)(1 + O_J(M^{-(J+1)/2}))`
  with `M = ⌊(√(8n+1) − 1)/2⌋` and an explicit smooth carrier
  `𝒜_J = C_0 Σ_j μ_j/j! E_{J−j}^{(j)}`, uniformly through triangular
  boundaries and the crossover; `C_0 = ∏(1 + 1/p(k))`, `μ_j` the moments of
  the limiting hole energy. Explicit first and second corrections
  `B_1(c)`, `B_2(c)` (eqs. (12), (72)) with relative errors `O(M⁻¹)` and
  `O(M^{-3/2})`.
- Theorem 4.2: integer inverse enclosures with two ceilings,
  `|x_J(Y) − N(Y)| ≲ D_J M^{-J/2}`.
- Proposition 5.2: `log a(n) = (2b/3)(2n)^{3/4} + O(√n log n)`, constant
  `4π2^{1/4}/(3√3) ≈ 2.87598`; Lemma 5.1: `a(n+1) > a(n)` for `n ≥ 1`.
- Section 6: a single central minor-arc bound fails; resonances at
  `θ = 2πℓ/X` have `log|φ_t| ~ −12ℓ²t`.
- Section 7: the exact low-hole filling bijection and
  `a(n) = Σ_{H⊂[1,L]} A_L(n + h(H))/p(H)`.
- Theorem 8.1: the tame edge expansion to every fixed order via Frobenius
  coordinates, Bloch–Okounkov brackets and a Bessel transfer rule;
  `A_1(c) = b(21c²/80 + c^{5/2}/5)`, `A_2` explicit.
- Theorem 9.1: localization to the two charges `M`, `M − 1` (Bellman envelope,
  crossing at `9/16`, per-hook gap Lemma 9.2).
- Section 11: crossover centre
  `φ_*(M) = 9/16 + 15/(4b√M)[log M + log(36√3/25) − 1] + O(log²M/M)`, width
  `M^{-1/2}`; the expansion of `log P_M` with the constant `C_P`.
- Theorem 12.1: total-variation approximation of (filled charge, low holes)
  by (Bernoulli, independent hole cloud), `O(M^{-1/2})`; mean and variance of
  the outer count.
- Section 13: pure-integer enclosures of `C_0 = 7.6015029336…`,
  `μ_1 = 6.0863425716…`, `μ_count = 1.6933481352…`,
  `σ²_count = 1.2113099088…` (40 digits printed, 100 in the data).

**Part II (A358836).**
- Section 17: the exact reduction `F = D(z)·P/M·R(z)` (moving-argument
  Jacobi product, partition and MacMahon products, finite-end factor),
  zero-free on disks `|z − t| ≤ ct²`; `h_1..h_10` (Proposition 17.2).
- Theorem 18.1: the free energy to every fixed order, differentiated, e.g.
  `L(t) = a/t³ + (Aℓ/2 − Z)/t² + (ℓ²/8 + 35A/24)/t + (7/48)log t − …`.
- Lemma 19.1 (all-angle bound) and Theorem 20.1 (every fixed Edgeworth order,
  `E_1 ~ −35t³/(4π⁴)`).
- Theorems 21.1–21.2: `log a_n = (4π/(3·24^{1/4}))n^{3/4} − (√6/24)n^{1/2}log n + O(n^{1/2})`
  (constant `≈ 1.89250`) and an elementary relative equivalent with error
  `O(n^{-1/4} log⁴ n)`.
- Section 22: inversion — Proposition 22.1, Theorem 22.2
  (`N(x) = ν_2(log x) + O(1)`), Theorem 22.3 (two-floor envelopes of any
  fixed accuracy; the `t⁴` interpolation barrier).
- Theorem 23.1: Gaussian number of blocks, `Var K_n ~ 1/(3t)`,
  `K_n/√n → √(2/3)`, mean shift `t/(3A) + O(t²|log t|)`; Theorem 24.1:
  Gumbel largest length, jointly independent of the count.

**Added by the write** (all marked `[write]`): proofs of two steps Part II
gives in outline — the sharpened mean shift (after the proof of Theorem
23.1, with a binary64 comparison against the frozen exact means at
`n ≤ 600`: the first-order identity agrees to within `4·10⁻⁴` at `n = 600`,
while the limit constant `1/(3A)` is approached slowly) and the
marker-derivative bounds in the proof of Theorem 24.1 (an independent
check after the write found both valid, recomputing `a_n` and `E K_n`
exactly for `n ≤ 600` and following the correction to `t = 0.001`, where
it is `0.2032 t` against `1/(3A) = 0.20264`; it is recorded in a dated
note, with the complex-`z` form of the Bell-polynomial bound and the
reliance on Part II's uniform complex-marker remainder now stated); a one-line
justification that first corrections move Part I's crossover centre only at
order `M⁻¹`; a check that Part I's stretched-amplitude law reduces to its
proved resonance formula at `α = 1/2`; dated notes; the front matter.

## What the report does not claim

Every limitation is printed in place and collected in Section 3. In short:
**Part I** is an eventual theorem with a non-effective onset (see the box
above); no finite-`n` accuracy theorem, no convergence or uniformity in a
growing order, no reconstruction of every exponentially smaller charge; the
inverse need not decide rounding near an integer; `α = 1/3` is a modulus
observation only; no certified `C_P`; `9/16` is not a finite-`M` threshold
(equal-weight phase `1.02188` at `M = 1000`); bounded source screen, no
novelty claim. **Part II**: no effective onset, no convergence of the formal
series, no growing-order uniformity or optimal truncation, no interval
certificates for asymptotic errors, no universal exact floor rule, no
arbitrary accuracy against the fixed interpolant; the product (Howroyd) and
composition model (Wiseman) are prior and the methods classical; bounded
source search, no priority claim. **Both packages**: finite exact checks
prove no asymptotic statement; floating diagnostics are uncertified; the
manifests are not signatures and the builders are not sandboxes.

## Further questions, and the standing rule

Each Part closes with "Further questions and research" (Sections 15 and
27). Under Vladimir's standing rule of 4 October 2026 the write moved there
every claim stated without proof, with source, sketch and what is missing:

- Part I (i): the stretched-amplitude modulus law and the `α = 1/3`
  threshold (Report 182 calls it an observation); (ii) a certified value of
  `C_P`.
- Part II (vii): "The full fixed-order [marked] expansion also holds"
  (Section 23.2), argued by reference to the unmarked proof; nothing in
  Part II uses more than its first-order form.

Report 182's four "Further directions" and Report 181's six questions stay
as printed. Two outline steps of Report 181 were proved in the write
instead (see above). **Nothing in either manuscript was found to be wrong**;
one wording is corrected in a dated note (a `exp(−ct^{−2δ})` bound called
"exponentially small" in the proof of Theorem 20.1).

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`:

- `a291698-moving-fugacity-partitions` (`∏(1 + n^α q^k)`): its exact Jacobi
  decomposition (11), taken at complex fugacity `u = e^{μ(z)}`, is Part II's
  expansion (96) of `log D(z)`; Part II derives it independently and adds the
  dual-term bound on its moving disk. Its Section 10.3 asks for the regime
  `log u ≍ n^{1/6}`; Part II's effective fugacity has `log u ≍ n^{1/4}` and
  depends on `q` itself, so it is a neighbouring model, not an answer
  (Report 181's own audit says substitution is not justified).
- `a022629-distinct-partition-norms` (`∏(1 + k^α q^k)^μ`): its question 7
  asks for regularly varying weights preserving a single crossing; `p(k)` is
  not regularly varying and Part I shows two competing charges instead — a
  different regime, not an answer. Report 93 (written into that report as
  Section 22 in batch 100) is the same phenomenon class as Part I's
  Section 6 (near-modulus-one Fourier peaks), for a different product.
  Part II's question 3 (Poisson process of extreme lengths) is the
  counterpart of its question 5.
- `a126348-stable-hilbert-series` (new in batch 100, Report 84):
  `∏(1 + q^k/(1−q))`, another `q`-dependent fugacity treated with Jacobi's
  triple product and the eta transformation; no shared theorem.
- No other report treats A271619, A358836 or A261049 (searched 5 October
  2026). Neither manuscript answers a question another report names, so no
  existing report's text is changed by this write. The a126348 report's own
  write already points here; pointers in the other two reports are a
  separate commit.

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of
this report is formalized. The one classical identity both Parts start
from, Jacobi's triple product, is formalized in Lean as
`Fabius.hasSum_jacobi_triple_product` in
`Analysis/FabiusFunction/Lean/FabiusFunction/JacobiTripleProduct.lean`
(`Σ_k (−1)^k q^{k(k−1)/2} z^k = (z;q)_∞ (q/z;q)_∞ (q;q)_∞`, `‖q‖ < 1`,
`z ≠ 0`); Part I's (29) is its instance `z = −q^{1/2}` and Part II's (95)
its instance `z = −e^{−μ}`. Nothing sequence-specific is formalized.

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (checked against the archives at the
  write: 0 differences); only names changed (table at the end). The delivered
  code and markdown use delivery paths (`code/verify.py`,
  `data/references/…`, `generated/…`, `optional/…`, `Report181.tex`,
  `Report182.tex`, `README.md`), several of which are not shipped or are
  shipped under other names. The scripts resolve paths relative to the
  package root, so **none runs in this directory**.
- `code/182-strict-verify.py` reads and pins the unshipped
  `data/references/coefficients_0_5000.txt`; `code/181-nested-verify.py` and
  `code/181-nested-guard_tests.py` read the marked OEIS prefix of the
  unshipped `Report181.tex`. Both need files from the arrival archive.
- `verify_manifest.py` needs the unshipped `SHA256SUMS.json` and PDFs; it was
  run (PASS) on fresh extractions at placement.
- **CRLF hazard (Report 182)**: on Windows, `guard_tests.py` writes its
  *valid* fixture with `Path.write_text('0 1\n1 1\n')`, which produces CRLF;
  the strict LF reader then rejects it and the suite fails with
  "noncanonical sequence row at index 0". This is a platform artifact, not a
  data defect: with `newline='\n'` forced in its four `write_text` calls (on a
  scratch copy only) it passes. The delivered file is unchanged.
- **FIFO tests (both)**: the build and guard tests skip their FIFO cases
  where `os.mkfifo` is missing (Windows). Report 181's `test_build.py`
  therefore reports 115 rejections there, not the 120 its `README_CODE.md`
  states; Report 182's reports 115 as well.
- The frozen scripts (`code/182-strict-references-*_frozen.py`,
  `code/182-strict-optional-frozen_float_diagnostics.py`,
  `code/181-nested-optional-scout-*.py`) are historical copies: they read
  files beside themselves or an unshipped workspace directory
  (`oeis_scout_oct3_1935`), and write their outputs beside themselves. Never
  run them in the repository.
- `182-strict-README_CODE.md` and `182-strict-optional-README.md` give
  `/tmp/…` output paths; use a scratch directory outside the repository.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. The simplest
route recreates the delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Strict_Twice_Partitions_Phase_Asymptotics_Source.zip > s182.zip
git show 60f54ea06:docs/incoming/Nested_Partitions_Asymptotics_and_Inverses_Source.zip > s181.zip
mkdir r182 r181 && unzip -q s182.zip -d r182 && unzip -q s181.zip -d r181
cd r182
py -I -S -B verify_manifest.py
py -I -S -B code/verify.py              # also with -O
py -I -S -B code/verify_second_order.py
py -I -S -B second_order_guard_tests.py
py -I -S -B guard_tests.py              # fails on Windows (CRLF fixture), see above
py -I -S -B test_build.py
py -I -S -B code/regenerate.py --output ../c182.json --compare data/certificates.json
cd ../r181
py -I -S -B verify_manifest.py
py -I -S -B code/verify.py              # also with -O
py -I -S -B guard_tests.py
py -I -S -B test_build.py
py -I -S -B code/regenerate.py --output ../c181.json --compare data/certificates.json
```

Equivalently, copy the shipped files to their delivered paths (the table at
the end) and add `data/references/coefficients_0_5000.txt` and
`Report181.tex` from the archives; the write did this and found every shipped
file equal to its archive member. Python 3.10 or later and its standard
library suffice; `build.py` additionally needs pdfLaTeX and writes only to
a new output directory.

Results at the write (5 October 2026, Python 3.14.4, Windows, on such a
copy): Report 182 `code/verify.py` PASS in 36 s, normal and `-O` outputs
identical and equal to `data/182-strict-generated-verification.json`
(`p` to 10000, `a` to 5000, 81,156 partitions, 174 hole cases / 8,898
triples); `verify_second_order.py` PASS (equal to the recorded receipt);
`second_order_guard_tests.py` PASS (330 rejections); `test_build.py` PASS (46
acceptances, 115 rejections); `regenerate.py` byte-identical to
`data/182-strict-certificates.json`; `guard_tests.py` FAIL as described, PASS
(166 rejections) with the LF-forced copy. Report 181 `code/verify.py` PASS in
14 s, normal and `-O` identical and equal to
`data/181-nested-generated-verification.json`; `guard_tests.py` PASS (140
rejections); `test_build.py` PASS (43 acceptances, 115 rejections);
`regenerate.py` byte-identical to `data/181-nested-certificates.json`. The
full `build.py` runs were not repeated, and the optional mpmath diagnostics
were not run (they prove nothing).

## Reconstructing the excluded data

`data/references/coefficients_0_5000.txt` of Report 182 (1,426,621 bytes,
lines `n a(n)` for `0 ≤ n ≤ 5000`, SHA-256 `37685454a702…` as pinned in
`code/182-strict-verify.py`) was not staged because of its size. Retrieve it
from the arrival archive:

```
git show 60f54ea06:docs/incoming/Strict_Twice_Partitions_Phase_Asymptotics_Source.zip > s182.zip
unzip -p s182.zip data/references/coefficients_0_5000.txt > coefficients_0_5000.txt
```

The same numbers are recomputed by `code/182-strict-exact.py` inside every
`verify.py` run (about half a minute here), which compares them with this
file.

## Rights

Repository contents are MIT-0. The sequence terms printed in the article and
contained in the data and code (`a(n)` of A271619, `a_n` of A358836, `p(k)`)
are recomputed by the shipped programs; their initial values agree with the
OEIS entries, whose data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). The OEIS entries are credited
for the sequences, the products and the combinatorial interpretations
(Wiseman 2016 for A271619; Wiseman 2022, Howroyd's product 2022 and
Wiseman's composition model 2024 for A358836). Nothing was submitted to the
OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 61 pages, no errors, no undefined or multiply defined references, no
duplicate destinations, no overfull or underfull boxes. The log carries two
"Infinite glue shrinkage found in box being split" messages, one from each
longtable that breaks across a page (the notation table, Table 1, and the
numbering crosswalk, Table 2), as in other reports with
longtables (for example `a196460-clipping-tables`).

## Delivered path → shipped path

Report 182 (`182-strict-`; `README.md` replaced by this guide):

| Delivered | Shipped |
|---|---|
| `Report182.tex` | `article.tex` (Part I) |
| `README_CODE.md`, `SOURCE_AUDIT.md`, `optional/README.md` | `182-strict-README_CODE.md`, `182-strict-SOURCE_AUDIT.md`, `182-strict-optional-README.md` |
| `build.py`, `guard_tests.py`, `second_order_guard_tests.py`, `test_build.py`, `verify_manifest.py` | `code/182-strict-<name>` |
| `code/<name>.py` (exact, regenerate, second_order, verify, verify_second_order) | `code/182-strict-<name>.py` |
| `optional/frozen_float_diagnostics.py`, `optional/run_diagnostics.py` | `code/182-strict-optional-<name>.py` |
| `data/references/exact_checks_frozen.py`, `data/references/independent_a2_check_frozen.py` | `code/182-strict-references-<name>.py` |
| `data/<name>.json` (PROVENANCE, SECOND_ORDER_PROVENANCE, certificates, second_order_certificate) | `data/182-strict-<name>.json` |
| `data/references/<name>` (other five files) | `data/182-strict-references-<name>` |
| `generated/<name>.json` (six files) | `data/182-strict-generated-<name>.json` |
| `optional/reference_results.json` | `data/182-strict-optional-reference_results.json` |
| `Report182.pdf`, `SHA256SUMS.json`, `data/references/coefficients_0_5000.txt` | not shipped |

Report 181 (`181-nested-`):

| Delivered | Shipped |
|---|---|
| `Report181.tex` | not shipped; printed as Part II of `article.tex` |
| `README_CODE.md`, `SOURCE_AUDIT.md`, `optional/README.md` | `181-nested-README_CODE.md`, `181-nested-SOURCE_AUDIT.md`, `181-nested-optional-README.md` |
| `build.py`, `guard_tests.py`, `test_build.py` | `code/181-nested-<name>` |
| `code/<name>.py` (exact, regenerate, verify) | `code/181-nested-<name>.py` |
| `optional/run_diagnostics.py`, `optional/scout/<name>.py` | `code/181-nested-optional-run_diagnostics.py`, `code/181-nested-optional-scout-<name>.py` |
| `optional/requirements.txt` | `data/181-nested-optional-requirements.txt` |
| `data/PROVENANCE.json`, `data/certificates.json` | `data/181-nested-<name>.json` |
| `data/references/<name>` (seven files) | `data/181-nested-references-<name>` |
| `generated/<name>.json` (four files) | `data/181-nested-generated-<name>.json` |
| `README.md`, `Report181.pdf`, `SHA256SUMS.json`, `verify_manifest.py` | not shipped (`verify_manifest.py` is byte-identical to Report 182's) |

## Provenance

Two manuscripts (bundle Reports 182 and 181) → one report; base 182. Arrival
`60f54ea06`, placement `36571ae0e`, write batch 100 (5 October 2026). Neither
manuscript pins a ProveIt commit. Merge choices (base, order, separate
bibliography entries for the two neighbouring reports, the OEIS citation key
`oeisA358836` of Part II) and every editorial change are listed in the
article's Appendix A.
