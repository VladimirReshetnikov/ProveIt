# Proving Two Arithmetic Conjectures for OEIS A321941

**Part I: a nonlinear product identity, integral polynomial deformations, sharp denominator bounds, and asymptotic inversion. Part II: signs, factorial divergence, and an order-two Borel singularity**

This research report has two Parts, built from two manuscripts of
ProveIt's incoming-reports intake. Part I is dated 1 October 2026 and
Part II 4 October 2026. Both author lines read "ChatGPT".

| Part | Source | Batch, manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|---|
| I | *Proving Two Arithmetic Conjectures for OEIS A321941* (main file `article.tex`, 18-page PDF as delivered, files at the archive root) | batch 73 (cluster O1), manuscript 45 | `A321941_Arithmetic_Conjectures.zip` | `0a6d798c5` | `c79d64038` | `9df4ba51a` | Part I: Sections 1–12 and Appendices A–B |
| II | *Signs, Factorial Divergence, and Bell Normalization. New results for OEIS A321941, A088714, and A088713* (main file `oeis_research.tex`, 36-page PDF as delivered, files under `oeis_research/`) | batch 86 (placement 86A), manuscript 02 | `oeis_research_bundle.zip` | `b7e4f25b6` | `ae9baa422` | `0f084afa9` | Part II: Sections 13–21 and Appendices C–D, from the manuscript's Part I (its Sections 2–7 and Appendix A) and the A321941 portions of its shared Sections 1, 13–15 and Appendix B |

- **Part I's pin** `0a6d798c5f39775b2fb4d85fef643fef996c87cf` is the
  commit at which its manuscript inspected the root README, the
  `Transseries_And_Inversion` README and `QuadraticCoreCatalan.lean`.
- **Part II's pin** `b7e4f25b6e79cc669fb245cba520017a0f4228b7` is the
  commit at which its manuscript inspected this report's `article.tex`
  (blob `10873a84`, the text now printed as Part I) and the A088714
  report. The manuscript covers two subjects and was split by subject at
  placement. Its Part II (Sections 8–12, the Bell normalization of
  A088714 and A088713) is printed as **Part V of
  [`a088714-bell-scale-growth`](../../generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth/)**,
  which also holds the manuscript's shared driver, run records and
  source audit (see "Files"). No other manuscript of either batch treats
  A321941, so nothing was merged.

The delivered READMEs, PDFs and Part II's manuscript source are not
shipped. They survive in the arrival commits (`git show
<arrival>:docs/incoming/<archive>`). Part I's archive had no checksum
ledger; Part II's `MANIFEST.sha256` (24 entries, all verified at
placement) is not shipped, as repository policy requires.

**Status: AI-assisted, unrefereed, not formalized.** Part II's source
audit records internal reviews by its own pipeline, with
`external_peer_review`, `proof_assistant_formalized` and
`worldwide_priority_exhaustively_verified` all `false`. The intake
reran every shipped program on a copy and made independent checks (see
"Rerunning the scripts"). It did not re-derive every proof.

## Files

```
README.md                                 this guide
article.tex                               the report, Parts I and II (LaTeX, internal bibliography)
article.pdf                               the compiled report, 36 pages (unnumbered title page, then pages 1-35)
SOURCES.md                                Part I's source audit (BGG 2019, OEIS, ProveIt pin), as delivered
code/verify.py                            Part I: exact integer and rational checks; optional SymPy and mpmath checks
code/02-sign-finite_certificate.py        Part II: the exact sign certificate for 3 <= k <= 31 (the listing of Appendix C)
code/02-sign-verify_sign.py               Part II: exact signs for 3 <= k <= 128, BGG's recurrence for k <= 64,
                                          13 OEIS terms, the cutoff-32 constants
code/02-sign-independent_check.py         Part II: BGG's Lemma 14 against a second heat-coefficient construction, k <= 64
code/02-sign-large_order.py               Part II: the large-order coefficients c_0, ..., c_8 and the polynomials F_m
code/02-sign-asymptotic_check.py          Part II: an independent SymPy derivation of c_0, ..., c_8
data/coefficients.csv                     Part I: k, r_k, d_k (numerator, denominator), v_2(r_k), s_2(k) for k = 0..256
data/polynomials.txt                      Part I: P_0(t), ..., P_8(t)
data/numerical_checks.csv                 Part I: normalized product and inverse errors at n = 25, 100, 400
data/verification_output.txt              Part I: console output of the recorded run
data/verification_metadata.json           Part I: versions, ranges and status of the recorded run
data/BUILD_NOTES.txt                      Part I: the delivered PDF's build and inspection receipt
data/02-sign-sign_verification.json       Part II: output of verify_sign.py (r_k, h_k and h_k/(-gamma_k) for k <= 128)
data/02-sign-independent_check.json       Part II: output of independent_check.py (d_k for k <= 64, margins, bounds)
data/02-sign-large_order_coefficients.json  Part II: output of large_order.py
data/02-sign-asymptotic_check.txt         Part II: output of asymptotic_check.py 8
data/02-sign-requirements-symbolic.txt    Part II: sympy==1.14.0, the pinned version for asymptotic_check.py
```

Every file except `article.tex`, `article.pdf` and `README.md` is
byte-identical to its delivery. `data/coefficients.csv` and
`data/numerical_checks.csv` are CRLF as delivered (kept by `-text` lines
in `SetTheory/Cardinals/.gitattributes`); Part II's files contain no CR
bytes. The Appendix C listing is byte for byte
`code/02-sign-finite_certificate.py`.

Shipped with Part V of `a088714-bell-scale-growth`, not here, and serving
both reports: `code/05-bell-norm-run_checks.py` (the manuscript's driver,
which runs the five Part II programs above together with its three
A088714 programs), `data/05-bell-norm-verification_run.txt` and
`data/05-bell-norm-verification_summary.json` (that driver's recorded
run), and `data/05-bell-norm-SOURCE_AUDIT.json` (the manuscript's source
audit, covering both subjects).

## Labels and edits

Every label carries the prefix `bgg:`. Part I's 83 labels are unchanged
(the batch-73 write added `bgg:sec:collection` and `bgg:app:audit` to
the manuscript's 81). The batch-86 write added 55, so the report has
138:

- `bgg:part:arithmetic` (Part I's heading);
- 47 labels of the manuscript, unchanged after the prefix `bgg:sg:`
  (`part:sign`, `sec:scope`, the 41 labels of its Sections 1.1 and 2–7 and
  Appendix A, `sec:changes`, `tab:boundary`, `sec:future`,
  `app:sources`);
- 7 new ones for the write's own material and the unlabelled questions:
  `bgg:sg:sec:collection`, `bgg:sg:sec:establish`,
  `bgg:sg:tab:notation`, `bgg:sg:q:region`, `bgg:sg:q:continuation`,
  `bgg:sg:q:arithmetic`, `bgg:sg:q:formal`.

A build's `.aux` confirms that no number of Part I changed: its 83
labels have the same section, equation, theorem and table numbers as
before. Part I is wrapped in `\part{Integrality, congruences, and
inversion}`; Part II follows Part I's appendices, continues the section
numbers (13–21) and the appendix letters (C–D), and has its own hyperref
anchor names.

**Part I** is printed as delivered, apart from the label prefix and
notes marked `[Write note, batch 73O1]` (a title-page line, Section 1.2,
paragraphs in Section 9 and Appendix B) and, since batch 86, notes
marked `[Write note, batch 86A, 4 October 2026]`: a title-page line;
after the open-negativity sentence of Section 1.1 and at the end of
Section 1.2 (both now superseded); after Theorem 5.2 (the edge P_k(0) is
the leading scale of P_k(1)); after the finite sign observation of
Section 9.2; at questions 1 (**answered**) and 4 (**answered in part**:
growth law and the positive Borel singularity; continuation open) of
Section 11; and after the ledger of Appendix A. The preamble gained
`mathrsfs`, `tabularx`, `listings`, a `question` theorem style and a
`\lstset`; no existing macro changed.

**Part II** prints the manuscript's text as delivered, except:

- labels prefixed and cross-references re-pointed: the manuscript's
  source report is now Part I, its other part is "Part V of the A088714
  report", and its BGG citation uses Part I's bibliography entry `BGG`;
  four DLMF entries were added to the bibliography;
- symbols renamed to avoid Part I's meanings (Table 4 of the article):
  α_n, η_n → a_n, b_n (the manuscript used Greek letters only to free a_n
  for A088714; these are Part I's own a_n, b_n); β_j → γ_j (Part I's β_k
  are inverse coefficients); the majorant M(t), M_ℓ → 𝓜(t), 𝓜_ℓ (Kummer's
  M keeps its letter); the fixed order R → N (Part I's R(z) is a series);
  e_k → ε_k in the Borel proof (Part I's e_{j,ℓ} are weights). No
  normalization changed. Table 4 also lists the symbols kept with a
  different meaning in Part I (t, h_k, H, q, S_k, G_n, F, W, ψ_m, λ_m, u,
  x, J, and B, T, E of the certificate) with the false reading beside
  the true one;
- the manuscript's shared material divided by subject: Section 13 prints
  the A321941 portions of its Section 1 (opening, Section 1.1 with
  Theorems 1.1 and 1.2, Section 1.3); Section 20 the A321941 rows,
  paragraph and check items 1–4 of its Sections 13–14 and its Section
  14.3; Section 21 its research questions 15.6–15.9; Appendix D the
  A321941 parts of its Appendix B. The A088714 portions are printed in
  Part V of `a088714-bell-scale-growth`;
- write notes: Section 13 (scope), Section 13.1 "Place in the ProveIt
  collection" (provenance, edits, status, shipped layout, relation to
  Part I, notation table), and short notes in Sections 20 and 21 and
  Appendices C and D.

The manuscript's Theorems 1.1, 1.2 and 7.1 are Theorems 13.1, 13.2 and
19.1; its Sections 2–7 are Sections 14–19; its Appendix A is Appendix C.
"Poincare" is spelled as delivered.

## What is claimed

**Part I.** Brent, Glasser and Guttmann (J. Integer Seq. 22 (2019),
Article 19.4.7, Corollary 9) proved ρ_n = a_n b_n ~ −(1/(2n^{3/2})) Σ_k
d_k n^{−k}, where a_n = [z^n] exp(z/(1−z)) (so n! a_n is A000262) and
b_n = [z^n] e^{1/(1−z)} E_1(1/(1−z)). That analytic expansion is **cited
input**, not claimed. With r_k = 64^k d_k (A321941) Part I proves:

- **Theorem 1.1:** r_0 = 1 and r_k is an even integer for every k ≥ 1
  (BGG's Conjecture 10, still marked conjectural in A321941 when
  inspected), and r_k ≡ C(2k,k) + 16·[k ∈ {1,2}] (mod 32) for every
  k ≥ 0 (the congruence half of BGG's Remark 11).
- **Theorem 1.2:** the integers B with B^k d_k ∈ ℤ for all k are exactly
  the multiples of 64; den(d_k) divides 2^{6k−1}; den(d_k) = 2^{6k−s_2(k)}
  whenever 1 ≤ s_2(k) ≤ 4, so the bound is attained at every power of
  two.
- Along the way: a quadratic Wronskian product identity (Lemma 2.1), a
  formal master equation identified with the analytic coefficients
  (Lemma 3.1, Proposition 3.2), an integral even polynomial family
  P_k(t) with P_k(1) = r_k (Theorem 5.1), the closed form
  P_k(0) = −C(2k,k)(2k−3)!!(2k+1)!! (Theorem 5.2), a coefficientwise
  congruence mod 32 for P_k (Theorem 6.1), and an all-orders inverse of
  the product expansion whose normalized coefficients have no
  denominator prime other than 3 (Theorem 8.1).

**Part II** (AI-assisted, unrefereed) proves, with
S_k = C(2k,k)(2k−3)!!(2k+1)!! = −P_k(0):

- **Theorem 13.1:** **r_k < 0 for every k ≥ 3** — the other half of BGG's
  Remark 11 and question 1 of Part I's Section 11. The proof identifies
  −nρ_n exactly with the diagonal Green function G_n(2,2) of the radial
  operator −d²/dr² + r²/16 + 3/(4r²) (14.3), sums its heat kernel in
  closed form (15.1), and derives the coefficient relation
  d_k = (½)_k h_k (15.5); coefficient majorants (Lemmas 16.1–16.2) give
  |h_k/γ_k + 1| < 9/10 for every k ≥ 32 (17.5), and an exact rational
  certificate covers 3 ≤ k ≤ 31, with minimum margin −h_k/γ_k = 61/105
  (17.6).
- **Theorem 13.2:** r_k = −S_k(Σ_{j≤N} c_j k^{−j} + O_N(k^{−N−1})) for
  every fixed N, with c_0..c_4 = 1, −1/3, −11/18, −1279/1620, −5089/9720
  (and c_5..c_8 recorded in Section 18.1); hence
  r_k ~ −16^k (k!)² / (π^{3/2} k^{3/2}), r_{k+1}/r_k ~ 16k², exact Gevrey
  order two, and P_k(1)/P_k(0) → 1 — the constant edge of Part I's
  Theorem 5.2 is the leading scale.
- **Theorem 19.1:** Σ_k d_k s^k/(2k)! has radius exactly 16, and
  B_2(16x) = (1/π) log(1−x) + C_B + O((1−x)|log(1−x)|) as x ↑ 1.
- Proposition 18.1 (an all-orders finite formula), and Table 5 (rounded
  diagnostics of r_k/(−S_k) for k up to 128).

## What is not claimed

Part I's non-claims are kept in its text (abstract, Section 1.1, Section
8.1, Appendix A):

- Part I does **not** prove the negativity r_k < 0 for k ≥ 3 (it checks
  3 ≤ k ≤ 256 as an observation; question 1 of Section 11). That
  assertion is now proved in Part II (Theorem 13.1), by an independent
  analytic method that does not use Part I's integrality.
- The analytic all-orders expansion is BGG's theorem, used as input.
- No effective remainder constants, convergence or optimal truncation.
  The expansions are Poincaré expansions; the inverse gives only the
  algebraic sector, and exponentially small corrections are not
  determined (Section 8.1, "The boundary between an expansion and a
  transseries").
- Exact denominators only when s_2(k) ≤ 4; the general exact 2-adic
  valuations are open (question 2).
- No literature priority: the search was targeted.
- No Lean or Rocq proof, and no formal build was run.

Part II's non-claims are kept in its text:

- (15.4) is a **formal** identity; it asserts no convergence of the
  Bessel expansion or of H.
- Theorem 19.1 is a radial boundary statement inside the disk of
  convergence: **no analytic continuation or Borel summability** is
  claimed; the full singularity set, lateral continuations and Stokes
  constants are open (Research question 21.2). Question 4 of Part I's
  Section 11 is therefore answered only in part.
- The finite programs certify the range 3 ≤ k ≤ 31 and check identities;
  the infinite sign assertion, the asymptotic tails and the error terms
  are proved in the text, not inferred from finite tests. Table 5's
  decimals are diagnostics.
- Part I's integrality, congruence and denominator results are credited
  as prior results, not new claims (Research question 21.3).
- No exhaustive worldwide priority claim, no external peer review, no
  proof-assistant formalization; the internal reviews recorded in the
  source audit are reviews within the manuscript's own pipeline.
- The special-function inputs (BGG's Lemmas 1–2, DLMF 13.2.34, 13.2.40,
  18.18.27 (Hille–Hardy), 10.40.1, Watson's lemma) are cited, not
  re-proved.

The statements about BGG's paper (the range 3 ≤ k ≤ 1000 of Remark 11,
the journal theorem numbers) and about the OEIS entry are as the
manuscripts inspected them on 1 and 4 October 2026; the intake did not
re-check them against the live pages.

## Relation to neighbouring material

- **A088714.** Part II's manuscript also proves the finer Bell
  normalization of A088714 (Conjecture 8.1 of
  [`a088714-bell-scale-growth`](../../generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth/));
  that part is printed there as Part V. The two subjects share no
  mathematics beyond the manuscript's method of exact positive
  representations; they share the driver and source audit named under
  "Files".
- **Elsewhere**, A321941 is named only by the collection catalogue,
  by a "shares no theorem" remark in
  [`factorial-ratio-polynomial-divisibility`](../factorial-ratio-polynomial-divisibility/),
  and by the source audit shipped with Part V of the A088714 report.
  A000262 occurs nowhere else in the repository.
- **Formal neighbour.** Placement in this collection confers no formal
  status. The Lean module
  [`QuadraticCoreCatalan.lean`](../../../../../../Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean)
  of the FabiusFunction library formalizes `Fabius.quadHalf_rat` (the
  Catalan closed form of binom(1/2, n+1) over ℚ) and
  `Fabius.quadHalf_antidiagonal` (the Catalan convolution). These are an
  ingredient of Part I's Catalan fixed-point formulation (Section 4.3,
  equation (4.8)), which the manuscript cites accurately, including the
  module's own statement that the power-series square-root identity is
  not formalized. No statement of this report, in either Part, is
  formalized; Part II's Research question 21.4 proposes a staged route.
- The `Transseries_And_Inversion` README, inspected at Part I's pin,
  gives only the general framing of formal inversion; there is no
  overlap. Part II's order-two Borel transform is radial information,
  not a transseries.
- **Neighbouring reports** in this category, both arithmetic studies of
  other sequences with no overlap:
  [`secant-number-periodicity`](../secant-number-periodicity/) (A000364
  modulo m) and
  [`compositional-tree-series-congruences`](../iterated-series/compositional-tree-series-congruences/)
  (integrality and congruences of a formal fixed point, A396805).

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No figures or other inputs are needed. pdfLaTeX (MiKTeX 26.2) produced
the shipped `article.pdf`: 36 pages, with no errors, no warnings, no
undefined references or citations, no multiply defined labels, no
duplicate destinations and no overfull or underfull boxes. Copy back
only `article.pdf`. `data/BUILD_NOTES.txt` describes Part I's delivered
18-page PDF (TeX Live 2025, pdfTeX 1.40.26), which is not shipped.

## Rerunning the scripts

Run everything on copies. Several programs write into their own
directory, and Part II's programs find each other by their delivered
names. On Windows, use `uv run --no-project python` (or `py`) where
`python` is written; Windows writes CRLF, so compare with
`diff --strip-trailing-cr`.

**Part I.** `code/verify.py` writes `coefficients.csv`,
`polynomials.txt`, `numerical_checks.csv` and
`verification_metadata.json` to the directory given by `--out`, by
default its own directory (`code/`), and prints the console log. Pass an
explicit output directory; never point it at `data/`.

```sh
R=SetTheory/Cardinals/docs/reports/congruences-and-valuations/a321941-asymptotic-coefficient-integrality
W=$(mktemp -d)
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python "$R/code/verify.py" \
    --order 256 --independent-order 128 --out "$W" > "$W/verification_output.txt"
```

Do not run it with `python -O` (the checks are assertions). Without SymPy
and mpmath the optional checks are reported as skipped; `--no-optional`
runs the standard-library part only. The intake ran this command on a copy
(exit code 0, about 54 s): `coefficients.csv` and `numerical_checks.csv`
are byte-identical to the shipped files, `polynomials.txt` is equal up to
line endings (Windows writes CRLF; the delivered file is LF), and the
metadata and console log differ only in the elapsed time.

**Part II, the five programs.** `verify_sign.py`, `independent_check.py`,
`large_order.py` and `asymptotic_check.py` each write their output
beside themselves (`sign_verification.json`, `independent_check.json`,
`large_order_coefficients.json`, `asymptotic_check.txt`);
`finite_certificate.py` only prints. `large_order.py` imports
`verify_sign` and `asymptotic_check.py` loads `independent_check.py` by
their delivered names, so the shipped `02-sign-` names do not run in
place. Restore the delivered names in a scratch directory (from the
repository root):

```sh
R=SetTheory/Cardinals/docs/reports/congruences-and-valuations/a321941-asymptotic-coefficient-integrality
W=$(mktemp -d)
for f in finite_certificate verify_sign independent_check large_order asymptotic_check; do
    cp "$R/code/02-sign-$f.py" "$W/$f.py"
done
cp "$R/data/02-sign-requirements-symbolic.txt" "$W/requirements-symbolic.txt"
(cd "$W" && python finite_certificate.py && python verify_sign.py &&
    python independent_check.py && python large_order.py &&
    uv run --no-project --with-requirements requirements-symbolic.txt python asymptotic_check.py 8)
for f in sign_verification.json independent_check.json large_order_coefficients.json asymptotic_check.txt; do
    diff --strip-trailing-cr "$W/$f" "$R/data/02-sign-$f" && echo "$f matches"
done
```

The first four need only the standard library (about 4 s here);
`asymptotic_check.py` needs SymPy 1.14.0 (about 36 s here, including the
environment). The intake ran exactly this on Windows: every program
exited 0 and all four outputs equal the shipped files up to line
endings.

**Part II, the manuscript's driver.** `run_checks.py` (shipped as
`code/05-bell-norm-run_checks.py` of the A088714 report) copies
`code/*.py` to a temporary directory, runs all eight programs of the
manuscript, compares their outputs with `data/<delivered name>`, and then
**overwrites** `data/verification_run.txt` and
`data/verification_summary.json`. Rebuild the delivered layout from both
reports in a scratch directory:

```sh
A=SetTheory/Cardinals/docs/reports/congruences-and-valuations/a321941-asymptotic-coefficient-integrality
B=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth
W=$(mktemp -d); mkdir -p "$W/code" "$W/data"
for f in "$A"/code/02-sign-*.py;   do cp "$f" "$W/code/${f##*/02-sign-}"; done
for f in "$B"/code/05-bell-norm-*.py; do cp "$f" "$W/code/${f##*/05-bell-norm-}"; done
for f in "$A"/data/02-sign-*;      do cp "$f" "$W/data/${f##*/02-sign-}"; done
for f in "$B"/data/05-bell-norm-*; do cp "$f" "$W/data/${f##*/05-bell-norm-}"; done
(cd "$W" && uv run --no-project --with-requirements data/requirements-symbolic.txt \
    python code/run_checks.py --symbolic)
```

The intake ran this on Windows (exit code 0, every check passed, about
22 s with SymPy already cached). The rewritten run records in the copy
differ from the shipped ones only in the Python version, the per-check
seconds and the temporary paths. Alternatively, re-extract the archive
from `git show ae9baa422:docs/incoming/oeis_research_bundle.zip` and run
its `code/run_checks.py --symbolic` there, outside the repository.

**Independent checks by the intake.** For Part I: the symmetric-square
recurrence of ρ_n, derived from the second-order recurrence of a_n
(checked exactly on a_n² for n ≤ 29) and solved order by order for
r_0, …, r_10 (identical to `data/coefficients.csv`), the residues mod 32
for k ≤ 10 and den(d_k) = 2^{6k−s_2(k)} for k = 1, …, 8. For Part II,
against Part I's `data/coefficients.csv` (computed by Part I's program
from the quadratic master equation, not by Part II's code):
d_k = (½)_k h_k holds exactly for 0 ≤ k ≤ 128 with the h_k of
`data/02-sign-sign_verification.json`; r_k < 0 for 3 ≤ k ≤ 256; the
minimum of r_k/(−S_k) over 3 ≤ k ≤ 31 is 61/105, at k = 3; the middle
and last columns of Table 5 are reproduced to every printed digit;
64^k (½)_k γ_k = S_k for 1 ≤ k < 60; and 16^k d_k/(2k)! · πk is −1.0064,
−1.0032, −1.0016 at k = 64, 128, 256. The rational constants of Lemmas
16.1–16.2 and Section 17.1 were checked by hand. The special-function
inputs of Sections 14–15 were not re-derived.

## Disclosures and discrepancies

- **Not shipped:** Part I's delivered `README.md` and `article.pdf`;
  Part II's `oeis_research.tex`, `oeis_research.pdf`, `README.txt` and
  `MANIFEST.sha256`. They survive in `c79d64038` and `ae9baa422`.
- **Renamed paths, Part I:** the archive had all files at its root.
  `verify.py` → `code/verify.py`; `coefficients.csv`, `polynomials.txt`,
  `numerical_checks.csv`, `verification_output.txt`,
  `verification_metadata.json` and `BUILD_NOTES.txt` → `data/`. Part I's
  Section 9 and Appendix B (delivered text, followed by write notes) and
  `data/BUILD_NOTES.txt` use the delivered names, and Appendix B's "the
  compiled PDF" and `BUILD_NOTES.txt` describe the delivered PDF.
- **Renamed paths, Part II:** `oeis_research/code/<name>.py` →
  `code/02-sign-<name>.py` for `finite_certificate`, `verify_sign`,
  `independent_check`, `large_order`, `asymptotic_check`;
  `oeis_research/data/<name>` → `data/02-sign-<name>` for
  `sign_verification.json`, `independent_check.json`,
  `large_order_coefficients.json`, `asymptotic_check.txt`;
  `oeis_research/requirements-symbolic.txt` →
  `data/02-sign-requirements-symbolic.txt`. The manuscript's other files
  went to the A088714 report with the prefix `05-bell-norm-`. The
  delivered-name dependencies of `large_order.py` and
  `asymptotic_check.py` are described under "Rerunning the scripts".
- **Delivered text naming unshipped or renamed files:** the docstring of
  `code/02-sign-verify_sign.py` names `oeis_research.tex`; Part II's
  Section 20.3 (delivered text, followed by a write note) names
  `oeis_research.tex`, its PDF and `README.txt`.
- **Shared run records** (in the A088714 report):
  `data/05-bell-norm-verification_run.txt` records the authoring
  machine's temporary paths (`/tmp/oeis_verification_…`,
  `/workspace/scratch/…`) and Python 3.12.14; nothing sensitive.
- **Requirements file:** `data/02-sign-requirements-symbolic.txt`
  (`sympy==1.14.0`) has the same bytes as many requirements files
  already in the repository; it is shipped because the rerun needs it.
- **Recorded elapsed time.** Part I's `data/verification_metadata.json`
  and the last line of `data/verification_output.txt` record 6.493 s
  for the delivered run; a rerun records its own time.
- **OEIS data.** `code/02-sign-verify_sign.py` embeds the 13 initial
  terms of A321941 displayed in the OEIS entry, and Part I's
  `code/verify.py` checks the same terms. OEIS content is licensed
  CC BY-SA 4.0; the entry is cited in the bibliography. No OEIS update
  was drafted or submitted.
