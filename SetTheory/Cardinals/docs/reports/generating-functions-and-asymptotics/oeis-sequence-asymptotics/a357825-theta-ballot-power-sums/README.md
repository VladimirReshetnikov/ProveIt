# Theta Asymptotics for High-Power Ballot Sums

**OEIS A357825, A357871 and the growing-power array A357824: exact oscillation envelopes, all-orders theta expansions, exponential multiset sectors and inverse asymptotics**

This research report is dated 1 October 2026. It was built from one
manuscript, manuscript 59 of batch 73 (cluster O1) of ProveIt's
incoming-reports intake. Its author line is "Prepared with ChatGPT as a
proposed contribution to the ProveIt research corpus" (PDF author: "Research
article prepared with ChatGPT").

| Source | Batch-73O1 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| single source | 59 | `OEIS_Theta_Ballot_Sums.zip` (*Theta Asymptotics for High-Power Ballot Sums*, main file `article.tex`, 25-page PDF as delivered) | `50f93367b` | `aa43cc555` | `9df4ba51a` | the whole report, Sections 1–11 and Appendices A–B |

The pin `50f93367b2859b2727c34c68cf87684c101768cc` is the ProveIt commit the
manuscript inspected (its root README and `Combinatorics/README.md`). The
delivered `source_audit.md` calls it the "inspected tree commit"; it is a
commit. No other manuscript of batch 73 treats these sequences, so nothing
was merged. The delivered README, PDF and `SHA256SUMS` ledger (20/20
verified at placement) are not shipped and survive in `aa43cc555`.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran the
verifier on a copy and checked selected values and the expansion
independently (see "Rerunning the script"). It did not re-derive every
proof.

## Files

```
README.md                         this guide
article.tex                       the report (LaTeX, internal bibliography)
article.pdf                       the compiled report, 27 pages (unnumbered title page, then pages 1-26)
source_audit.md                   the manuscript's source and claim audit, as delivered
code/verify.py                    exact, symbolic and high-precision checks, tables and plots (SymPy, mpmath, Matplotlib)
code/build.sh                     the delivered build script (runs verify.py --all, then pdflatex three times; see below)
data/requirements.txt             mpmath==1.3.0, sympy==1.14.0, matplotlib==3.10.8
data/software_versions.json       Python 3.13.5 and the three package versions of the recorded run
data/verification_status.json     recorded run: exact-check counts and the numerical settings
data/coefficients.json            the polynomials A_1..A_5, D_1..D_6 and R_0..R_6
data/constants.json               liminf, limsup, mean, Turan liminf/limsup, first-sector constant (55 digits)
data/asymptotic_errors.csv        Table 1: relative errors of the truncations J = 0..6, n = 25..1200
data/exponential_sector.csv       the first exponential sector at n = 20, 30, 40, 60, 80, 100
data/square_transition.csv        the near-square logistic transition, s = 8, 16, 32, d = -2..2
data/inverse_errors.csv           the inverse-expansion errors of Section 9.3
data/plot_data.csv                the 601 points of Figures 1 and 2 (600 <= n <= 1200)
figures/phase_collapse.pdf        Figure 1, regenerated in the write (see below)
figures/oscillation.pdf           Figure 2, regenerated in the write
figures/phase_collapse.png        raster version, as delivered
figures/oscillation.png           raster version, as delivered
```

Every file except `article.tex`, `article.pdf`, `README.md` and the two
figure PDFs is byte-identical to the delivery. The five CSV files are CRLF
as delivered (kept by `-text` lines in `SetTheory/Cardinals/.gitattributes`);
`data/coefficients.json`, `data/constants.json` and
`data/verification_status.json` have no final newline, as delivered.

## Labels and edits

Every label carries the prefix `tbs:`. The manuscript's 104 labels are kept,
unchanged after the prefix; the write added one, `tbs:sec:collection`
(Section 1.4), so the report has 105. No theorem, section, equation or table
number of the manuscript changed.

The text is printed as delivered, apart from the label prefix and three
notes marked `[Write note, batch 73O1]`: one line on the title page,
Section 1.4 "Place in the ProveIt collection" (provenance, status, shipped
layout, neighbouring material), and a paragraph at the end of Section 9.4 on
the shipped paths of the requirements file and the build script. The title
page also gained a `\par` after its status box, so that the author line no
longer starts beside the box (a layout defect of the delivered PDF). No
symbol was renamed.

## What is claimed

With B(n,h) the ballot triangle A008315, a_n = Σ_h B(n,h)^n (A357825),
b_n = Σ_h C(B(n,h)+n−1, n) (A357871) and S_{n,k} = Σ_h B(n,h)^k (A357824),
m = n+1, α_n = (√m − (m mod 2))/2 and Θ(α) = Σ_j exp(−4(j−α)^2):

- **Theorem 2.2** (all-orders diagonal expansion):
  a_n/𝒜_n = e^{−5/6}{Σ_{j≤J} m^{−j/2} F_j(α_n) + O_J(m^{−(J+1)/2})}, uniformly
  in the phase, with F_0 = Θ and F_j Gaussian-weighted sums of explicit
  polynomials R_j (R_1, R_2 printed; R_3, R_4 in Appendix A; R_0..R_6 in
  `data/coefficients.json`). 𝒜_n = 2^{n²+3n/2}/(π^{n/2} e^{n/2} n^n) is
  Kotesovec's normalization.
- **Theorem 4.2**: the exact liminf and limsup of a_n/𝒜_n are
  e^{−5/6}Θ(1/2) ≈ 0.31986675953099572613 and
  e^{−5/6}Θ(0) ≈ 0.45051819401966197435; the cluster set is the whole
  interval between them. Proposition 4.3 and Corollary 4.4 give the limiting
  phase law.
- **Theorem 5.1**: oscillatory adjacent-ratio and Turán asymptotics; a_n is
  eventually strictly log-convex. Proposition 5.2: a_n is not P-recursive.
- **Section 6** (the array A357824): fixed powers and the broad Gaussian regime k → ∞,
  k = o(n) (Proposition 6.1), the critical theta regime k ≍ n (Theorem 6.2), a uniform
  two-endpoint theorem for **all** supercritical powers (Theorem 6.3), and a
  logistic transition near square-index ties at k ≍ n^{3/2} (Corollary 6.4).
- **Section 7** (multisets): an exact rising-factorial bridge gives every
  fixed exponential sector (Theorem 7.1); the first one is
  n! b_n/a_n = 1 + √(πe)/(4√2) n³ 2^{−n}(1 + O(1/n)) with an explicit
  phase-dependent 1/n term (Theorem 7.2).
- **Section 8**: parity-sensitive inverse expansions (Proposition 8.1,
  Theorem 8.2) and their relation to integer thresholds.

Kotesovec's OEIS observations of November 2022 (a_n^{1/n} ~ K_n, and no limit
of a_n/𝒜_n; the same for b_n) are the starting point and are credited as
such, not claimed.

## What is not claimed

The manuscript's non-claims are all kept in the text (title-page box, the
table of Section 1.2, Sections 9 and 10, Appendix B):

- Bala's conjecture a_{2p−1} ≡ 1 (mod p³) for primes p ≥ 5, recorded in
  A357825, is **not resolved** (question Q9).
- Log-convexity is proved only eventually, not at every index (Q2).
- The expansion is a Poincaré expansion: no convergence, optimal truncation
  or resurgence is claimed. It is an oscillatory expansion with periodic
  coefficients, "not an ordinary real logarithmic-exponential transseries"
  (remark after Theorem 2.2).
- No unrestricted exact inverse rounding theorem, no effective thresholds
  for the O-terms.
- The numerical tables are high-precision experiments, not interval
  certificates.
- No publication priority: the literature and OEIS search was limited.
- No Lean or other formal proof.

The OEIS data and attributions quoted in the article (terms n ≤ 14 embedded in
`code/verify.py`, the dates of Kotesovec's and Bala's comments) are as the
manuscript inspected them on 1 October 2026; the intake did not re-fetch
them.

## Relation to neighbouring material

- **No repository host.** A357824, A357825, A357871 and A008315 occur nowhere
  else in the repository.
- **Same mechanism, different objects** (cross-references only; no statement
  depends on them):
  [`Theta_Resolved_Optimal_Truncation_q_Multinomial`](../../../../../../../Analysis/Transseries/docs/series-and-transseries/Theta_Resolved_Optimal_Truncation_q_Multinomial/)
  (a continuous-to-lattice saddle with a theta law for q-multinomial
  remainders) and the chapter "Galois numbers and root-lattice theta
  sectors" of
  [`Combinatorial_Transseries_Inverses`](../../../../../../../Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/),
  both in the series-and-transseries collection.
- [`ballot-polynomial-hankel-determinants`](../../../hankel-determinants/catalan-and-ballot/ballot-polynomial-hankel-determinants/)
  studies Hankel determinants of ballot moments, not growing powers; there
  is no overlap.
- **Lean.** Placement in this collection confers no formal status. No Lean
  or Rocq declaration of the repository concerns these sums, and none of the
  statements of this report is formalized. Question Q10 sketches a staged
  formalization plan.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build needs `figures/phase_collapse.pdf` and `figures/oscillation.pdf`
beside `article.tex`. pdfLaTeX (MiKTeX 26.2) produced the shipped
`article.pdf`: 27 pages, with no errors, no warnings, no undefined
references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes, and one underfull line in the bibliography
(also present in a build of the delivered text). It contains no Type 3 font
(`pdffonts`: 14 Type 1, 6 CID TrueType). Copy back only `article.pdf`.

The shipped `code/build.sh` does not work from `code/`: it changes into its
own directory and then calls `code/verify.py`, and it expects `article.tex`
beside itself. In the delivered layout, with `build.sh` at the root, it ran
`code/verify.py --all` (which rewrites `data/` and `figures/`) and then
`pdflatex` three times, copying the result over `article.pdf`. Do not run it
in this directory.

## Rerunning the script

`code/verify.py` finds `data/` and `figures/` relative to its own parent
directory and **overwrites** them: run it on a copy, never in place.

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a357825-theta-ballot-power-sums
W=$(mktemp -d)
cp -r "$R/code" "$R/data" "$R/figures" "$W/"
cd "$W"
uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 --with matplotlib==3.10.8 python code/verify.py --all
```

Without flags the script runs only the exact and symbolic checks (and
rewrites `data/coefficients.json` and `data/verification_status.json`);
`--plots` adds the figures, `--all` also the numerical tables. The intake ran
`--all` on a copy (exit code 0, about two minutes): the eight data files it
writes equal the shipped ones, five CSV files byte for byte and the three
JSON files up to line endings (on Windows, `Path.write_text` writes CRLF; the
delivered JSON is LF). The figures it writes differ in bytes from the
shipped ones (Matplotlib metadata, and Type 3 fonts unless set as below).

Independently of the delivered code, the intake recomputed a_0..a_6 and
b_0..b_6 from the definitions, both envelope constants to 20 digits, and the
expansion through F_2 against exact sums at n = 100, 200, 400, 800 (relative
errors 1.2e−5, −6.4e−5, 7.9e−7, −1.4e−5 after F_2, consistent with
O(m^{−3/2})), and the first exponential sector at n = 100, 200, 400.

## Disclosures and discrepancies

- **Not shipped:** the delivered `README.md` (replaced by this guide), the
  delivered `article.pdf` (replaced by a build of this text) and the
  `SHA256SUMS` ledger.
- **Renamed paths:** `requirements.txt` → `data/requirements.txt`;
  `build.sh` → `code/build.sh`. Every other file keeps its delivered path.
  Section 9.4 of the article (a verbatim delivered passage, followed by a
  write note), `source_audit.md` and the delivered README name
  `requirements.txt` and `build.sh` at the root, and the article's
  "From the extracted archive" refers to the delivered layout.
- **Regenerated figures.** The delivered `phase_collapse.pdf` and
  `oscillation.pdf` embedded their DejaVu Sans and STIX fonts as Type 3. In
  the write both were regenerated from the shipped, unmodified
  `code/verify.py`, on a copy, by calling its `plots()` function only:
  - Matplotlib 3.10.8, the version that made the delivered files, with
    `rcParams['pdf.fonttype'] = 42` set before the script was loaded, mpmath
    1.3.0 and SymPy 1.14.0;
  - `SOURCE_DATE_EPOCH=1790886019`, the delivered files' creation date
    (1 October 2026, 20:20:19 UTC);
  - the run rewrote `data/plot_data.csv` byte-identical to the shipped file,
    so the plotted data are the delivered ones;
  - two runs gave byte-identical PDFs; page size (576 × 266.4 pt) and the
    rendered images match the delivered figures, apart from glyph
    anti-aliasing; the fonts are now CID TrueType;
  - the PNG previews are kept as delivered.

  To reproduce, on a copy as above, run
  `import runpy, matplotlib; matplotlib.rcParams['pdf.fonttype'] = 42; runpy.run_path('code/verify.py', run_name='m')['plots']()`
  with that environment variable, under the `uv run` line above.
- **"Inspected tree commit"** in `source_audit.md` is the commit
  `50f93367b`.
- **Delivered README wording.** Its "Verification actually performed" list
  ("First 15 terms of each target sequence against OEIS") rests on the
  values embedded in `code/verify.py`, which the intake did not compare with
  the live OEIS entries.
