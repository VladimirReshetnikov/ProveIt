# OEIS A290268 at Unbounded Logarithmic Deficit

**Regular saddle phases, the Airy fold, two-dimensional cosine laws, superseded lower bounds, and arithmetic families**

This research report is dated 1 October 2026. It was built from nine manuscripts of batch 72A of ProveIt's incoming-reports intake. Eight are printed and one is superseded. Every manuscript carries the author line "Research note prepared for Vladimir Reshetnikov with OpenAI".

A290268 counts the nonzero terms a(N) in the Nth derivative of x^(x^2). The source report [`power-tower-derivative-term-counts`](../power-tower-derivative-term-counts/) reduces each term to an integer H(d,k,q) in depth coordinates. This report studies those integers when the depth d, the logarithmic deficit, grows with N.

| Source | Batch-72A manuscript | Archive (`ProveIt_A290268_…zip`) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| base | 58 | `Explicit_Finite_Ratio` (*An Explicit Finite-Ratio Noncancellation Region for OEIS A290268*, 10-page PDF) | `ca81647a9` | `d292c6765` | Section 2 (the shared model) and Sections 3–8 (Part I) |
| member | 54 | `Airy_Fold` (*The Airy Transition at the A290268 Critical Ratio*, 10 pp.) | `ca81647a9` | `d292c6765` | Part II, Sections 13–19 |
| member | 64 | `Arithmetic_Phase` (*Arithmetic Nonvanishing and Central Phase Laws for OEIS A290268*, 10 pp.) | `ca81647a9` | `d292c6765` | Sections 9–10 (case κ = 0); Part IV, Sections 26–31 |
| member | 45 | `Sparse_Cancellations` (*Sparse Cancellations in the A290268 Tail*, 10 pp.) | `ca81647a9` | `d292c6765` | Sections 11 and 21 |
| member | 53 | `Pointwise_Three_Halves` (*A Pointwise Three-Halves Correction for OEIS A290268*, 9 pp.) | `ca81647a9` | `d292c6765` | Sections 12 and 24 |
| member | 49 | `Strict_Quadratic_Gain` (*A Strict Pointwise Quadratic Gain for OEIS A290268*, 10 pp.) | `ca81647a9` | `d292c6765` | Section 20 |
| member | 40 | `Direct_Contour` (*A Direct Contour Proof for the A290268 Regular Region*, 8 pp.) | `ca81647a9` | `d292c6765` | Section 22 |
| member | 37 | `Global_049_Bound` (*A Global 0.49 Lower Bound for OEIS A290268*, 12 pp.) | `ca81647a9` | `d292c6765` | Section 23 |
| superseded | 61 | `Growing_Logarithmic_Degrees` (*Growing Logarithmic Degrees in OEIS A290268*, 5 pp.) | `ca81647a9` | `d292c6765` (nothing staged) | not printed; contents in Section 33 |

The pin `ca81647a9f679e96d49ffdbc54b0c0ab13d10a36` is the commit the manuscripts inspected: the text of the source report at that time. The archives arrived in `1512ef835`; the placement commit `d292c6765` deleted them from `docs/incoming`, and they survive in `1512ef835`. The manuscripts were written in the order 64, 61, 58, 54, 53, 49, 45, 40, 37, the reverse of their batch numbers. Manuscript 34, printed in the sibling report, was written after all of them.

**Status: AI-assisted, unrefereed, not formalized.** Each manuscript says it "received independent mathematical review". That is the authors' statement, kept as delivered. The intake checked selected constants and identities and reran every shipped script on a copy. It did not re-derive every proof. Every threshold is existential unless a number is displayed.

## Files

```
README.md                                         this guide
article.tex                                       the report (LaTeX, internal bibliography)
spectral_sections.tex                             Sections 3-5, \input by article.tex (manuscript 58's input file, edited; see below)
article.pdf                                       the compiled report, 77 pages
code/58-finite-ratio-verify_rational_band.py      exact-fraction certificate kappa_c > 1/36 (standard library)
code/58-finite-ratio-check_spectral_limits.py     numerical orientation for Part I (NumPy, SciPy); not a proof
code/64-arith-phase-verify_prime_blocks.py        prime-length identities, prime-unit family and valuations, jet blocks (SymPy)
code/64-arith-phase-verify_k0.py                  the 258 finite cases of the central strips and 1791 prime-block cases
code/64-arith-phase-verify_geometry.py            the root-geometry example (SymPy; prints only)
code/64-arith-phase-test_stronger_parameter.py    optional 813120-cell scan of the unproved evaluation lemma
code/40-direct-contour-verify_reduction.py        112 exact checks of the series form against the recurrence model (standard library)
code/40-direct-contour-check_prefactors.py        numerical prefactor and action checks at d = 200, 400, 800 (mpmath)
code/37-global-049-verify_constants.py            exact Taylor, angular, height and area certificates (standard library)
code/37-global-049-plot_regions.py                source of the region figure (Matplotlib)
data/58-finite-ratio-rational_band_certificate.json   recorded certificate (shared by manuscripts 49, 53, 58)
data/58-finite-ratio-requirements.txt             numpy>=1.24, scipy>=1.10 (for the orientation script only)
data/58-finite-ratio-spectral_numeric.json        recorded orientation run, 27 rows
data/64-arith-phase-prime_block_verification.json recorded prime-block run
data/64-arith-phase-prime_block_run.txt           its standard output
data/64-arith-phase-central_strip_certificate.json recorded central-strip certificate
data/64-arith-phase-central_strip_run.txt         its standard output (three PASS lines)
data/64-arith-phase-geometry_verification.txt     standard output of verify_geometry
data/64-arith-phase-stronger_parameter_scan.json  recorded diagnostic scan: 813120 checks, no unexpected zero
data/64-arith-phase-requirements.txt              sympy>=1.12
data/40-direct-contour-reduction_checks.json      recorded exact checks: 112 cases, PASS
data/40-direct-contour-prefactor_checks.json      recorded numerical checks
data/37-global-049-exact_constants.json           recorded exact certificates, PASS
figures/37-global-049-regions.pdf                 region figure (Figure 1), regenerated in the write (see below)
figures/37-global-049-regions.png                 raster version, as delivered
```

Every file in `code/` and `data/`, and the PNG in `figures/`, is byte-identical to the delivery. The figure PDF was regenerated in the write; see "Disclosures and discrepancies". Manuscripts 54 and 45 shipped no code. Manuscripts 49 and 53 shipped only the rational-band certificate, which is byte-identical to 58's and is shipped once. Manuscript 61 shipped none.

## Structure, labels and numbering

- **Front matter**: Sections 1–1.4 cover the organization, what was printed once, status, and the notation table with every renamed symbol. Section 2 is the shared model.
- **Part I** (Sections 3–12): the regular saddle branch and fixed-offset phases. Manuscript 58 is the base. Manuscript 64's fixed-degree phase laws are printed as corollaries, the case κ = 0 of 58's theorem, with 64's proofs as second proofs. Manuscript 45's O(1/d) rate and bounded strips follow, then manuscript 53's phase law for |b| ≤ √d.
- **Part II** (Sections 13–19): manuscript 54, the Airy law at the fold κ_c ≈ 0.0281461.
- **Part III** (Sections 20–25): two-dimensional cosine laws and lower bounds, from manuscripts 49, 45 (part 2), 40, 37 and the count of 53. Section 25 is the table of superseded headline bounds.
- **Part IV** (Sections 26–31): manuscript 64's congruences, valuations, central strips and root-geometry example.
- Section 32 holds the questions and Section 33 the provenance.

Every label carries the prefix `aud:`. A manuscript's own labels keep its prefix as a sub-prefix: `aud:fr:` (58), `aud:af:` (54), `aud:sc:` (45), `aud:qg:` (49), `aud:go:` (53), `aud:gh:` (37), `aud:dc:` (40; not the source's `xxb:dc:`) and `aud:ap:` (64). The staged base had 41 labels (`article.tex` 19, `spectral_sections.tex` 22). All 41 are kept, with the prefix added. The report now has **283** labels: 244 from the manuscripts and 39 added by the merge. By manuscript, the 244 are 41 from 58, 32 from 54, 17 from 64, 32 from 45, 44 from 49, 25 from 53, 19 from 40 and 34 from 37. The manuscripts had 300 distinct labels in all. The other 56 named duplicate copies of the model, the branch geometry, the lattice lemma, the contour and 49's cosine law, which are printed once. Every reference to them now points to the printed copy.

Text added in the merge is marked `[Merge note, batch 72A.]` or `[Added 1 October 2026, batch 72A: …]`. Otherwise the manuscripts' text is kept. It differs only in the label prefixes, the symbol renames listed in Section 1.4, the cross-references that replace the members' citations of one another, and the removal of the duplicate passages listed in Section 1.2.

## What is claimed

- **Part I.** There is a regular saddle branch κ = sin t/t − 2cos t − 2, for t_0 ≤ t < t_c, with fold κ_c = K(t_c) > 1/36, proved by an exact certificate. A uniform fixed-offset phase law holds on it, with phase (π − t)/2. Consequences:
  - eventual nonvanishing of H(d, k, 2d+b) whenever k/d tends to an algebraic κ < κ_c, apart from the reflection holes;
  - uniform nonvanishing for |b| ≤ 8 and 0 ≤ k ≤ d/36;
  - possible phase zeros only at the explicit transcendental ratios K((1 − p/s)π), the first being κ_9 = K(8π/9).

  Manuscript 45 adds the O(1/d) rate and bounded strips around those ratios. Manuscript 53 adds a phase law uniform for |b| ≤ √d. Manuscript 64 proves the case κ = 0, at k = 0 and at every fixed k, with phase arctan a_0, where a_0 arctan(1/a_0) = 1/4.
- **Part II.** An additive Airy law holds in the window |k − κ_c d| = O(d^(1/3)) at fixed b. It gives eventual nonvanishing whenever k − κ_c d = o(d^(1/3)), in particular at the nearest integer to κ_c d.
- **Part III.** The part proves:
  - uniform additive cosine laws: two conjugate saddles (49), a direct contour through δ = 0 and κ = 0 (40), and horizontal selection in the cone 10q > 3d (37);
  - explicit negative phase curvatures, including 2T²cos T/F(T) on the whole branch (40);
  - density one with O(N^(5/3)) exceptions on fixed tail patches (45, 40), and o(N²) zeros in the wide cone (37);
  - uniform eventual positivity of every coefficient on the triangle 40k + 420q ≤ 91d (37).

  It also prints the headline bounds liminf a(N)/N² ≥ 28176/57247 (37), a(N) ≥ (3/8 + c)N² (49), a(N) ≥ β(N) + C_patch(N−1)² − O(N^(5/3)) (45), a(N) ≥ (3/8 + C_0)N² − O(N^(5/3)) (40) and a(N) ≥ β(N) + CN^(3/2) (53).
- **Part IV.** For an odd prime p, the coefficient is congruent mod p to at most two terms of a residual polynomial of degree at most 2p − 2. The part proves:
  - a two-parameter prime-unit family at unbounded depth, with exact p-adic valuations of the derivative coefficients;
  - a logarithm-free prime-block family;
  - nonvanishing at k = 0 on the all-depth strips |q − 2d| ≤ 5 (d odd) and 1 ≤ |q − 2d| ≤ 9 (d even);
  - an exact example showing that the root geometry of the factorization cannot by itself prove the support conjecture.

## What is not claimed

- The full support conjecture of the source (`xxb:conj:support`) is not proved.
- No exact zero is inferred from a vanishing leading phase, a cosine zero, an Airy zero or a zero residue modulo p.
- No numerical depth threshold, offset width or gain is asserted anywhere.
- Every manuscript's non-claims are kept in the text. These include the fold excluded by 58, the dominance boundaries of 40, the "no uniform global power-saving remainder" of 37, the "only selected coefficients" of 53 and 49, the non-classification of strip candidates in 45, and the unproved evaluation lemma and diagnostic scan of 64.
- **The headline count bounds are superseded.** All five are ineffective. All are implied by a(N) = N²/2 + o(N²), manuscript 34's theorem, written after them on the same day and printed in the sibling report [`power-tower-exponent-supports`](../power-tower-exponent-supports/). That theorem is also ineffective. Each manuscript's "1/2 remains open" or "3/8 remains" sentence is kept with a dated note. The cosine laws, phase separation, positivity, strips and curvature formulas behind the bounds are statements about individual coefficients and are not implied by a count asymptotic. Section 25 states the relation exactly.
- The best *effective* lower bounds are not here. They are the source's Corollary `xxb:dc:cor:lower` and its batch-72A count-bounds addition (manuscript 68): a(N) ≥ 3N²/8 + (N/2)log N − (N/2)log log N − 5N/4 for N ≥ e^10.

## Relation to neighbouring material

- **Source report** [`power-tower-derivative-term-counts`](../power-tower-derivative-term-counts/), Part 3:
  - The model, the factorization (`xxb:dc:prop:factor`), the reflection holes (`xxb:dc:thm:holes`) and the bulk count β(N) come from there.
  - This report continues its conjecture `xxb:conj:support` and bears on its Questions 4 and 5 (Section 3.24).
  - Its Question 6, a(N) ~ N²/2, is answered in the sibling report, not here.
  - Batch 72A also added to it manuscript 70 (depths five and six), which 64 calls "an earlier companion", and manuscript 68 (count bounds), to which 53 alludes. Neither was cited by its sibling.
  - Batch 73 classifies depths seven and eight there (`13ef7d939`), so the open fixed-depth region is now m ≥ 9; this report's own results are unaffected.
- **Sibling report** [`power-tower-exponent-supports`](../power-tower-exponent-supports/) (batch 72A): it proves a(N) = N²/2 + o(N²) (manuscript 34, the case a = 2 of manuscript 28). It is cited, not reprinted.
- **Research notes** `Oeis/A290268/README.md`: the ProveIt investigation of A290268.
- **Lean.** Placement beside a formal development confers no formal status. The A290268 Lean development (`Combinatorics/DerivativeExpansions/A290268/Lean`) formalizes:
  - the coefficient recurrence `LeanProofs.A290268.coeff`;
  - the count of the conjectured support, `LeanProofs.A290268.card_S`;
  - the values `LeanProofs.A290268.a_values_le_53` (n ≤ 53);
  - the conditional reduction `LeanProofs.A290268.a_eq_closedForm_of_support`.

  None of the statements of this report is formalized.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build needs `spectral_sections.tex` and `figures/37-global-049-regions.pdf` beside `article.tex`. pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 77 pages, with no errors, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

## Rerunning the scripts

Every script writes its output beside itself, under its **delivered** name. Running one in `code/` would not overwrite the shipped `data/` files, but it would leave unprefixed files in `code/`, so run them on a copy. Use `py` or `uv run --no-project --with …`. The intake ran them with SymPy 1.14.0, mpmath and NumPy/SciPy, on copies under its scratch directory, and every run passed.

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a290268-unbounded-deficits
W=$(mktemp -d)
for f in "$R"/code/*.py; do b=$(basename "$f"); cp "$f" "$W/${b#*-*-*-}"; done   # restore delivered names
cd "$W"
py verify_rational_band.py                    # -> rational_band_certificate.json
uv run --no-project --with sympy==1.14.0 python verify_prime_blocks.py   # -> prime_block_verification.json (+ stdout)
uv run --no-project --with sympy==1.14.0 python verify_k0.py             # -> central_strip_certificate.json (+ stdout)
uv run --no-project --with sympy==1.14.0 python verify_geometry.py       # stdout only
py verify_reduction.py                        # -> reduction_checks.json
py verify_constants.py                        # -> exact_constants.json
# optional: check_spectral_limits.py (NumPy, SciPy; about 76 s), check_prefactors.py (mpmath),
#           test_stronger_parameter.py (about 56 s), plot_regions.py (Matplotlib; writes regions.pdf/png)
```

Compare each output with the shipped record `data/<prefix>-<delivered name>`. On Windows, `Path.write_text` writes CRLF, while the delivered files are LF, so compare ignoring line endings. The rerun of `check_spectral_limits.py` differs from `data/58-finite-ratio-spectral_numeric.json` in the last floating-point place (about 1.2e-15); that output is orientation only. `plot_regions.py` regenerates the figure. Run as-is, it gives Type 3 fonts and the current date; "Disclosures and discrepancies" gives the settings that reproduce the shipped PDF byte for byte. Its PNG output differs in bytes from the delivered PNG, which is the one shipped.

## Disclosures and discrepancies

- **Not shipped**:
  - the nine delivered manuscripts' READMEs and PDFs;
  - the manuscripts and `\input` files of the eight non-base manuscripts;
  - 45's `inputs/` directory, which held copies of 58's and 49's PDFs;
  - the copies of the certificate in 49 and 53;
  - every `build_local.sh`, a Linux-only wrapper identical across the batch and already in history;
  - all of 61.

  This README replaces 58's delivered README, which named `article.pdf`, `verify_rational_band.py`, `check_spectral_limits.py`, `rational_band_certificate.json`, `spectral_numeric.json` and `build_local.sh` under their delivered names.
- **Edited base files.** `article.tex` and `spectral_sections.tex` are manuscript 58's files, rewritten in the merge. `spectral_sections.tex` keeps its delivered name. Its labels gained the prefix, its limiting mean M(κ,y) is written 𝓜(κ,y), and three merge notes were added. It is no longer byte-identical to the delivery.
- **Delivery names in shipped text.**
  - The scripts write `rational_band_certificate.json`, `spectral_numeric.json`, `prime_block_verification.json`, `central_strip_certificate.json`, `stronger_parameter_scan.json`, `reduction_checks.json`, `prefactor_checks.json`, `exact_constants.json` and `regions.pdf`/`regions.png`, shipped as the prefixed `data/` and `figures/` files above.
  - The article's phrases "the accompanying exact-rational script", "the supplied exact-fraction certificate" and "the included script" (58, 49, 53) mean `code/58-finite-ratio-verify_rational_band.py`.
  - "The supplied script" in Section 29 means `code/64-arith-phase-verify_k0.py`.
  - "The accompanying standard-library verifier" and "a separate numerical diagnostic" (40) mean `code/40-direct-contour-verify_reduction.py` and `code/40-direct-contour-check_prefactors.py`.
  - "The accompanying rational verifier" (37) means `code/37-global-049-verify_constants.py`.
- **Requirements.**
  - 58's requirements file covers only its optional orientation script.
  - 64's pins `sympy>=1.12`.
  - 40's `check_prefactors.py` needs mpmath and 37's `plot_regions.py` needs Matplotlib; neither manuscript ships a requirements file.
- **Missing final newline.** `data/64-arith-phase-prime_block_verification.json` and `data/64-arith-phase-stronger_parameter_scan.json` have none, as delivered.
- **Regenerated figure.** The delivered `regions.pdf` embedded its two DejaVu Sans fonts as Type 3. In the write, `figures/37-global-049-regions.pdf` was regenerated from the shipped, unmodified `code/37-global-049-plot_regions.py`, run on a copy under its delivered name.
  - The run used Matplotlib 3.10.8, the version that made the delivered file, with `rcParams['pdf.fonttype'] = 42` set by a wrapper before the script ran, and with `SOURCE_DATE_EPOCH=1790840576`, the delivered file's creation date.
  - The script takes no data input; its geometry is hard-coded.
  - Two runs gave byte-identical PDFs. The page size (363.803 × 346.8 pt) and the rendered image match the delivered figure.
  - The fonts are now embedded as CID TrueType, and `article.pdf` contains no Type 3 font (`pdffonts`: 27 Type 1, 2 CID TrueType).
  - The PNG is kept as delivered.
  - To reproduce, run `import runpy, matplotlib; matplotlib.rcParams['pdf.fonttype'] = 42; runpy.run_path('plot_regions.py')` on a copy with the environment variable set, under `uv run --no-project --with matplotlib==3.10.8 python`.
- **Uncited dependencies** among the manuscripts are marked by merge notes:
  - 54 on 58;
  - 58 on 64's constant;
  - 64 on manuscript 70 and 53 on manuscript 68, both now additions to the source report;
  - 61 on 64.
- **Abstracts.** The eight abstracts were replaced by one. Their non-claims are all also in the manuscripts' bodies, which are kept.
- **Bibliography.** It was merged. The members' citations of each other became cross-references. 64's commented-out bibliography entry inside its fixed-offset section was dropped; the same item is in the bibliography.
