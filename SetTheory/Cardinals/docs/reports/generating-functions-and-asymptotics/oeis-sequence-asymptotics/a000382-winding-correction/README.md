# Winding Sectors and the Four-Displacement Restricted-Permutation Problem

**A direct Tribonacci–Lucas enumeration, an inverse transseries, and corrections to OEIS A000382, A000496 and A008305**

This research report is dated 1 October 2026. It is one manuscript, number 55 of batch 73O2 of ProveIt's incoming-reports intake. Author line: "Research report for the ProveIt project".

| Source | Batch-73O2 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| single source | 55 | `ProveIt_A000382_winding_correction.zip` (19-page PDF) | none (cites no repository revision) | `58dbe2cd3` | `6e193dd4f` | the whole article |

The placement commit `6e193dd4f` deleted the archive from `docs/incoming`; it survives in `58dbe2cd3`.

For n ≥ 4 let Φₙ be the number of permutations σ of ℤ/nℤ with every clockwise displacement σ(i) − i mod n in {0,1,2,3}, that is Φₙ = per(I+P+P²+P³) for the cyclic shift P: the fourth column T(n,4) of OEIS A008305 and the tail of A004306.

**The formula Φₙ = 2(A001644(n)+1) is not new: it is already printed in OEIS A004306**, whose cross-reference line reads "Equals 2 * (A001644(n) + 1), n>3", and whose formula lines give the recurrence a(n) = 2a(n−1) − a(n−4) and a tribonacci formula credited to Natalia L. Skirrow (16 February 2026). The novelty of this report is the **proof** (a winding-number decomposition into sectors of sizes (1, Lₙ, Lₙ, 1), with the winding-one sector in bijection with cyclic tilings) and the **diagnosis of A000382**: its 31 displayed terms are the values of Mendelsohn's displayed 1961 formula, not the restricted-permutation count, so its comment "The fourth column of A008305, divided by 4" is false from n = 8 on (65 against 264/4 = 66), and A000496 equals 4·A000382 from offset 4. The manuscript did not say that A004306 already records the formula; the write added that, in the abstract and in dated notes (Sections 1.1, 1.4 and 9).

**Status: AI-assisted, unrefereed, not formalized.** At intake the sector vectors were recomputed by brute force over all n! permutations for n = 4..10 and by an independent bitmask DP to n = 16, the OEIS quotations were checked against snapshots of A000382, A000496, A004306 and A008305 taken on 1 October 2026, the nearest-integer formula was checked for n = 4..39, the two inverse coefficients were re-derived, and the verifier was rerun on a copy. The proofs were not otherwise re-derived. Mendelsohn's 1961 paper was not available to the intake.

## Files

```
README.md                        this guide
article.tex                      the report (LaTeX, internal bibliography)
article.pdf                      the compiled report, 20 pages (title page 1, contents page 2, text pages 3-20)
code/verify.py                   independent subset-DP permanent computation and checks (standard library only)
code/Makefile                    delivered convenience targets (see "Disclosures": its pdf target does not run here)
data/verification_output.txt     captured standard output of verify.py
data/oeis_corrections.txt        proposed OEIS notes, not submitted (predates the A004306 notes; see below)
```

Every file except `article.tex`, `article.pdf` and this README is byte-identical to the delivery. Not shipped: the delivered PDF, the delivered README (replaced by this guide) and `SHA256SUMS` (verified 7/7 at placement and retired).

## Labels

Every label carries the prefix `wdc:`. The delivered article had **84** labels; all are kept with the prefix, and three were added (`wdc:sec:intro`, `wdc:sec:new`, `wdc:sec:provenance`): **87** in all. The text is as delivered except for:

- the label prefix;
- the symbol for log α in Section 7, renamed from L to **Λ** because L collided with the Tribonacci–Lucas numbers Lₙ of Theorem 1.1 (announced in a note there; no normalization change);
- dated write notes: that A004306 already prints the formula (abstract, Sections 1.1 and 1.4, and the A008305 and A004306 proposals in Section 9); that Mendelsohn's equation-(4) and printed-table values are as read from a scan not in the repository (Sections 1.2 and 5.3); the interpolation dependence of the continuous inverse and its repository provenance (Section 7); the shipped layout (Appendix B);
- a citation of the repository, which the delivered bibliography listed but never cited (Question 10.11);
- a note re-scoping Question 10.10 (inverse transseries for general rational recurrences), whose mechanism the canonical transseries volume's Chapter p9 already treats;
- the shipped paths of the verifier and its outputs (Sections 8 and 9), Appendix C (provenance), and one bibliography entry (the transseries volume).

## What is claimed

- **Theorem 1.1.** Φₙ = 2(Lₙ+1) for n ≥ 4, Lₙ = A001644 (L₀ = 3, L₁ = 1, L₂ = 3), with winding sectors (1, Lₙ, Lₙ, 1). The formula was already recorded in A004306; the theorem is its proof.
- **Sections 2–3, for every width r.** The winding number q(σ) = (1/n)Σdᵢ is an integer (Lemma 2.1); every cut is crossed exactly q times (Lemma 2.2); the sector polynomial is palindromic (Lemma 2.3); the outer sectors are singletons (Lemma 2.4); winding one is in bijection with cyclic tilings by tiles of lengths 1..r−1 (Theorem 3.1), counted by a power sum of r−1-bonacci roots (Proposition 3.2).
- **Section 4.** Φₙ = Φₙ₋₁+Φₙ₋₂+Φₙ₋₃−4 (n ≥ 7), Φₙ = 2Φₙ₋₁−Φₙ₋₄ (n ≥ 8), 4 | Φₙ, and the generating function.
- **Theorem 5.1.** Mendelsohn's formula sequence Mₙ = F_{n−1}+F_{n−3}+F_{n−4}+1 (M₄ = 6) satisfies Mₙ = Mₙ₋₁+Mₙ₋₂+Mₙ₋₃−2 for n ≥ 8: the recurrence marked "(conjectured)" in A000382 is a theorem for the formula-defined sequence, not for the restricted-permutation count.
- **Theorem 5.2.** Σ_{n≥4}(Φₙ/4 − Mₙ)z^(n−4) = z⁴/(1−2z+z⁴); the corrections are cumulative sums of tribonacci numbers, 1, 2, 4, 8, 15, 28, … from n = 8.
- **Theorem 6.1, Corollary 6.2.** Φₙ = 2(1+αⁿ+βⁿ+γⁿ) and Φₙ/4 = nint((αⁿ+1)/2), α = 1.83928675521…; a convergent all-orders expansion of log Φₙ; the limiting relative undercount of Mₙ is 0.0206945979568…
- **Section 7.** Monotonicity of the interpolation Φ̃(x) = 2+2αˣ+4α^(−x/2)cos(θx) (Lemma 7.1), a log-periodic inverse with two explicit terms and all orders (Theorem 7.2), and N(y) = ⌈x(y)⌉ (Corollary 7.3).
- **Section 9.** Proposed corrections to A000382, A000496, A008305 and A004306; **not submitted**.

## What is not claimed

- Not the formula Φₙ = 2(A001644(n)+1) itself (A004306), nor the recurrence and generating function of the true count (A004306), nor the classical transfer-matrix theory of permanents of cyclic (0,1)-matrices (Metropolis–Stein–Stein, Beker–Mitchell).
- No claim that no equivalent bijection has appeared in the wider literature: the search was targeted, not exhaustive. The OEIS statements quoted are snapshots of 1 October 2026 and may change.
- **No novelty for the inverse mechanism.** The continuous inverse is the inverse of one chosen interpolation; between the values Φₙ its log-periodic coefficients depend on that choice, and only N(y) is intrinsic (the dichotomy of Proposition `p9:prop:intrinsic`). The mechanism, a dominant exponential with a complex-conjugate subdominant pair giving log-periodic inverse coefficients, is Chapter p9 of the canonical volume (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`, Theorem `p9:thm:product`, Remark `p9:rem:shape`), which the manuscript does not cite.
- Mendelsohn's equation-(4) and printed-table values (260, 476, 872 and 256, 472, 872 at n = 8, 9, 10) are as read from a scan of the 1961 paper by the manuscript's author; the intake did not see the scan.
- The manuscript's README asks for independent review of the proof and the historical attribution before any OEIS or journal submission. The inner sectors for r ≥ 5 and the other questions of Section 10 are open; Question 10.10 is open only in its general, automated form (see the write note there).

## Relation to neighbouring material

- **No host.** Nothing else in the repository concerns A000382, A000496, A004306, A008305 or A001644.
- **Transseries volume** (above): Section 7 is a sequence case of its Chapter p9, which treats a real-argument Fibonacci function. The precedents for single-sequence OEIS correctness reports in this subcategory are [`a352969-correctness-and-growth`](../a352969-correctness-and-growth/) and [`a260306-formula-proof`](../a260306-formula-proof/).
- **Lean.** Placement in this collection confers no formal status. No statement of this report is formalized; Question 10.11 sketches a Lean route.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

(or `pdflatex` twice, as Appendix B says). pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 20 pages, no errors, no undefined references or citations, no multiply defined labels, no duplicate destinations, no overfull or underfull boxes. The delivered source built the same way gives 19 pages. Copy back only `article.pdf`.

## Rerunning the verifier

`code/verify.py` uses only the Python standard library and writes only to standard output (about 1 s):

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000382-winding-correction
py "$R/code/verify.py" > "$(mktemp -d)/verification_output.txt"
```

Compare the output with `data/verification_output.txt` ignoring line endings (redirected output on Windows is CRLF; the delivered file is LF). At intake they were equal. Do not redirect into `data/`.

## Disclosures and discrepancies

- **`code/Makefile`** (byte-identical) has `PDF_SCRIPT ?= /home/oai/skills/pdfs/scripts/latex_to_pdf.py`, a script in the delivery environment: its `pdf` (and hence `all`) target does not run here. Its `verify` target runs `python3 verify.py | tee verification_output.txt` in the current directory, so from `code/` it would write `code/verification_output.txt`, not the shipped `data/` file. GNU `make` is not installed on the intake machine; use the commands above. The delivered README's build line used the same sandbox script and is not reproduced.
- **`data/oeis_corrections.txt`** (byte-identical) was written before the A004306 notes. Its A008305 section proposes stating T(n,4) = 2·(A001644(n)+1) as a direct formula, and its A004306 section calls the current values, recurrence and tribonacci formula correct and suggests "additional comments" without mentioning that the A004306 cross-reference line already reads "Equals 2 * (A001644(n) + 1), n>3". Any submission should instead cross-reference the existing A004306 identity and add the proof, the sector sizes, the Binet and nearest-integer forms, and the A000382/A000496 corrections.
- **Delivery names in shipped text.** The article's Appendix B lists the delivered archive (`verify.py`, `verification_output.txt`, `oeis_corrections.txt`, `README.md`, `Makefile` at the archive root) and refers to "the PDF build command documented in the README", which this README replaces; a write note there gives the shipped layout.
- **Author line.** The delivered author line is "Research report for the ProveIt project", kept as delivered.
