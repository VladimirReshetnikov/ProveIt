# Proving Two Arithmetic Conjectures for OEIS A321941

**A nonlinear product identity, integral polynomial deformations, sharp denominator bounds, and asymptotic inversion**

This research report is dated 1 October 2026. It was built from one
manuscript, manuscript 45 of batch 73 (cluster O1) of ProveIt's
incoming-reports intake. Its author line is "ChatGPT / Research draft
prepared for the ProveIt research program" (PDF author: "ChatGPT").

| Source | Batch-73O1 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| single source | 45 | `A321941_Arithmetic_Conjectures.zip` (*Proving Two Arithmetic Conjectures for OEIS A321941*, main file `article.tex`, 18-page PDF as delivered, files at the archive root) | `0a6d798c5` | `c79d64038` | `9df4ba51a` | the whole report, Sections 1–12 and Appendices A–B |

The pin `0a6d798c5f39775b2fb4d85fef643fef996c87cf` is the ProveIt commit the
manuscript inspected: the root README, the `Transseries_And_Inversion`
README and `QuadraticCoreCatalan.lean`. No other manuscript of batch 73
treats A321941, so nothing was merged. The delivered README and PDF are not
shipped and survive in `c79d64038`; the archive had no checksum ledger.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran the
verifier on a copy and checked the coefficients independently (see
"Rerunning the script"). It did not re-derive every proof.

## Files

```
README.md                         this guide
article.tex                       the report (LaTeX, internal bibliography)
article.pdf                       the compiled report, 20 pages (unnumbered title page, then pages 1-19)
SOURCES.md                        the manuscript's source audit (BGG 2019, OEIS, ProveIt pin), as delivered
code/verify.py                    exact integer and rational checks; optional SymPy and mpmath checks
data/coefficients.csv             k, r_k, d_k (numerator, denominator), v_2(r_k), s_2(k) for k = 0..256
data/polynomials.txt              P_0(t), ..., P_8(t)
data/numerical_checks.csv         normalized product and inverse errors at n = 25, 100, 400
data/verification_output.txt      console output of the recorded run
data/verification_metadata.json   versions, ranges and status of the recorded run
data/BUILD_NOTES.txt              the delivered PDF's build and inspection receipt
```

Every file except `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery. `data/coefficients.csv` and
`data/numerical_checks.csv` are CRLF as delivered (kept by `-text` lines in
`SetTheory/Cardinals/.gitattributes`).

## Labels and edits

Every label carries the prefix `bgg:`. The manuscript's 81 labels are kept,
unchanged after the prefix; the write added two, `bgg:sec:collection`
(Section 1.2) and `bgg:app:audit` (Appendix B, previously unlabelled), so
the report has 83. No theorem, section, equation or table number of the
manuscript changed.

The text is printed as delivered, apart from the label prefix and four
notes marked `[Write note, batch 73O1]`: a line on the title page, Section
1.2 "Place in the ProveIt collection" (provenance, status, shipped layout,
the formal neighbour, neighbouring reports), a paragraph at the start of
Section 9 and one at the end of Appendix B on the shipped paths. The title
page is now wrapped in `\hypersetup{pageanchor=false}` … `pageanchor=true`;
the delivered source produced a duplicate `page.1` destination. No symbol
was renamed.

## What is claimed

Brent, Glasser and Guttmann (J. Integer Seq. 22 (2019), Article 19.4.7,
Corollary 9) proved ρ_n = a_n b_n ~ −(1/(2n^{3/2})) Σ_k d_k n^{−k}, where
a_n = [z^n] exp(z/(1−z)) (so n! a_n is A000262) and
b_n = [z^n] e^{1/(1−z)} E_1(1/(1−z)). That analytic expansion is **cited
input**, not claimed. With r_k = 64^k d_k (A321941) the report proves:

- **Theorem 1.1:** r_0 = 1 and r_k is an even integer for every k ≥ 1 (BGG's
  Conjecture 10, still marked conjectural in A321941 when inspected), and
  r_k ≡ C(2k,k) + 16·[k ∈ {1,2}] (mod 32) for every k ≥ 0 (the congruence
  half of BGG's Remark 11).
- **Theorem 1.2:** the integers B with B^k d_k ∈ ℤ for all k are exactly the
  multiples of 64; den(d_k) divides 2^{6k−1}; den(d_k) = 2^{6k−s_2(k)}
  whenever 1 ≤ s_2(k) ≤ 4, so the bound is attained at every power of two.
- Along the way: a quadratic Wronskian product identity (Lemma 2.1), a
  formal master equation identified with the analytic coefficients
  (Lemma 3.1, Proposition 3.2), an integral even polynomial family P_k(t)
  with P_k(1) = r_k (Theorem 5.1), the closed form
  P_k(0) = −C(2k,k)(2k−3)!!(2k+1)!! (Theorem 5.2), a coefficientwise
  congruence mod 32 for P_k (Theorem 6.1), and an all-orders inverse of the
  product expansion whose normalized coefficients have no denominator prime
  other than 3 (Theorem 8.1).

## What is not claimed

The manuscript's non-claims are all kept in the text (abstract, Section
1.1, Section 8.1, Appendix A):

- The negativity r_k < 0 for k ≥ 3 (the other half of BGG's Remark 11) is
  **not proved**; it is checked for 3 ≤ k ≤ 256 and logged as an
  observation only (question 1 of Section 11).
- The analytic all-orders expansion is BGG's theorem, used as input.
- No effective remainder constants, convergence or optimal truncation. The
  expansions are Poincaré expansions; the inverse gives only the algebraic
  sector, and exponentially small corrections are not determined
  (Section 8.1, "The boundary between an expansion and a transseries").
- Exact denominators only when s_2(k) ≤ 4; the general exact 2-adic
  valuations are open (question 2).
- No literature priority: the search was targeted.
- No Lean or Rocq proof, and no formal build was run.

The statements about BGG's paper (the range 3 ≤ k ≤ 1000 of Remark 11, the
journal theorem numbers) and about the OEIS entry (older preprint numbering,
integrality still described as conjectural) are as the manuscript inspected
them on 1 October 2026; the intake did not re-check them against the live
pages.

## Relation to neighbouring material

- **No repository host.** A321941 and A000262 occur nowhere else in the
  repository; "Guttmann" has no other hit.
- **Formal neighbour.** Placement in this collection confers no formal
  status. The Lean module
  [`QuadraticCoreCatalan.lean`](../../../../../../Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean)
  of the FabiusFunction library (unchanged since the pin) formalizes
  `Fabius.quadHalf_rat` (the Catalan closed form of binom(1/2, n+1) over ℚ)
  and `Fabius.quadHalf_antidiagonal` (the Catalan convolution). These are an
  ingredient of the report's Catalan fixed-point formulation (Section 4.3,
  equation (4.8)), which the manuscript cites accurately, including the
  module's own statement that the power-series square-root identity is not
  formalized. No statement of this report is formalized.
- The `Transseries_And_Inversion` README, also inspected at the pin, gives
  only the general framing of formal inversion; there is no overlap.
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

No figures or other inputs are needed. pdfLaTeX (MiKTeX 26.2) produced the
shipped `article.pdf`: 20 pages, with no errors, no warnings, no undefined
references or citations, no multiply defined labels, no duplicate
destinations and no overfull or underfull boxes. Copy back only
`article.pdf`. `data/BUILD_NOTES.txt` describes the delivered 18-page PDF
(TeX Live 2025, pdfTeX 1.40.26), which is not shipped.

## Rerunning the script

`code/verify.py` writes `coefficients.csv`, `polynomials.txt`,
`numerical_checks.csv` and `verification_metadata.json` to the directory
given by `--out`, by default its own directory (`code/`), and prints the
console log. Pass an explicit output directory; never point it at `data/`.

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

Independently of the delivered code, the intake derived the
symmetric-square recurrence of ρ_n from the second-order recurrence of a_n
(checked exactly on a_n² for n ≤ 29), solved it order by order for
r_0, …, r_10 (identical to `data/coefficients.csv`), and confirmed the
residues mod 32 for k ≤ 10 and den(d_k) = 2^{6k−s_2(k)} for k = 1, …, 8.

## Disclosures and discrepancies

- **Not shipped:** the delivered `README.md` (replaced by this guide) and
  `article.pdf` (replaced by a build of this text).
- **Renamed paths:** the archive had all files at its root. `verify.py` →
  `code/verify.py`; `coefficients.csv`, `polynomials.txt`,
  `numerical_checks.csv`, `verification_output.txt`,
  `verification_metadata.json` and `BUILD_NOTES.txt` → `data/`. The
  article's Section 9 and Appendix B (delivered text, followed by write
  notes) and `data/BUILD_NOTES.txt` use the delivered names, and Appendix
  B's "the compiled PDF" and `BUILD_NOTES.txt` describe the delivered PDF.
- **Recorded elapsed time.** `data/verification_metadata.json` and the last
  line of `data/verification_output.txt` record 6.493 s for the delivered
  run; a rerun records its own time.
