# Two Fourier Peaks and a Moving Lattice Maximum

**A proof of the OEIS A039831 asymptotic conjecture, four correction orders, a smoothing hierarchy, and inverse growth**

This research report is dated 1 October 2026. It was built from one manuscript, manuscript 62 of batch 73 of ProveIt's incoming-reports intake. The manuscript's author line is "Research report prepared for Vladimir Reshetnikov".

| Source | Batch-73 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole | 62 (cluster O2) | `A039831_Two_Fourier_Peaks.zip` (main file `article.tex`, 18-page PDF) | `a5ad4ac2e` | `aa43cc555` | `6e193dd4f` | the whole article |

The pin `a5ad4ac2e2d4e642a6c015836a70492d40fcbc71` is the repository commit the manuscript's GitHub reads identified (`SOURCE_MANIFEST.md`, article Appendix B). It is an ancestor of the placement commit, and the two files the manuscript read, the root `README.md` and `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md`, are unchanged between the pin and the placement. The archive arrived in `aa43cc555`; the placement commit `6e193dd4f` deleted it from `docs/incoming`, and it survives in `aa43cc555`.

**Status: AI-assisted, unrefereed, not formalized.** The proofs are ordinary mathematical proofs, not Lean- or Rocq-checked and not referee-reviewed. The intake reran the three programs on a copy and made its own exact check (see below). It did not re-derive every proof.

## Files

```
README.md                        this guide
SOURCE_MANIFEST.md               the manuscript's source and audit-scope record, as delivered (URLs, pin; no file hashes)
article.tex                      the report (LaTeX, internal bibliography)
article.pdf                      the compiled report, 19 pages
code/verify.py                   exact sliding convolution through n = 400, small-row and cumulant unit tests, numerics, inverse checks
code/derive_coefficients.py      SymPy derivation of the four correction coefficients and the logarithmic coefficients
code/all_orders.py               evaluator of the finite arbitrary-order formula of Theorem 4.1 (exact cumulants, then mpmath)
data/numerical_results.csv       maxima, modes, means, normalized maxima and errors for every n <= 400 (CRLF, as delivered)
data/inverse_results.csv         inverse errors at n = 50, 100, 200, 400 (CRLF, as delivered)
data/verification_output.txt     standard output of the recorded verify.py run
data/symbolic_output.txt         output of derive_coefficients.py
data/all_orders_output.txt       standard output of all_orders.py --n 100 --k 4954 --order 8 --digits 70 --check
data/requirements.txt            mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to the delivery. `article.pdf` is a build of this `article.tex`, not the delivered PDF.

## Labels

Every label carries the prefix `tfp:`. The manuscript's 74 labels are kept, unchanged after the prefix. The write added one, `tfp:app:provenance` (75 in all).

## What is claimed

Let M_n be the largest coefficient of P_n(q) = ∏_{j=1}^n (1 + q + q³ + … + q^{2j−1}).

- **Kotesovec's conjecture on A039831** (OEIS, 5 January 2023), with two corrections (Theorem 1.1, `tfp:thm:main`):
  M_n = 3(n/e)^n (1 − 431/(300n) + 23085971/(1764000n²) + O(log n/n³)).
- A four-order local expansion of c_{n,k}/(3(n/e)^n), uniform for |k − μ_n| ≤ D, with exact harmonic numbers, a log-periodic lattice term at order n^-3 (Corollary 7.1) and a parity term −18(−1)^{n+k}/n⁴ from the second Fourier neighbourhood at q = −1.
- An arbitrary-algebraic-order finite formula with remainder (Theorem 4.1, `tfp:thm:allorders`).
- Eventually every maximizing exponent lies in {⌊μ_n⌋, ⌈μ_n⌉} (Proposition 6.2); the smaller Fourier contribution changes the maximizer infinitely often, and the number of failures of principal-peak rounding through N lies between positive multiples of log N (Theorem 6.3).
- A zero-multiplicity law for suppression of the second neighbourhood under fixed Bernoulli smoothing (Theorem 8.1).
- A Lambert-W inverse on the sequence values (Theorem 9.1) and a qualified integer-threshold bracket (Section 9.2).

## What is not claimed

- **A039824 is not resolved.** Its conjecture that the number of *distinct* coefficient values is n² − 3 for n > 6 (Ralf Stephan, 2004; related conjectures by Colin Barker, 2017) is a different question from the largest coefficient, and nothing here settles it (article Section 1.1 and research question 3).
- The remainders are asymptotic bounds with no explicit thresholds; no effective constants (research question 1).
- The numerical errors in the tables and CSVs are floating-point measurements, not interval bounds.
- The first-order parity threshold is asymptotic; its prediction (the `mode_prediction` CSV column) is wrong at n = 56, as the article and the recorded output say.
- No exact counting constant for the rounding failures (only logarithmic upper and lower bounds), no exponentially improved or resurgent description, nothing uniform in a growing smoothing order.
- The Fourier/Edgeworth method is classical; the Dolgopyat–Hafouta theorem is cited for context and not invoked outside its bounded-summand hypotheses.
- No global priority claim: the A039831 record still labels the leading estimate a conjecture, and a targeted search found no earlier proof, which is not proof of absence.
- **The inversion method is not new.** Section 9 re-derives the canonical transseries volume's apparatus: the Lambert core `p0:thm:lambert-core`, the perturbed inversion `p0:thm:perturbed-inversion`, and for integer thresholds the staircase theorem `p0:thm:staircase` and the certified discrete inversion `p0:prop:certified-rounding` (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`). The manuscript itself points to that organization (Section 12); notes added in the write name the theorems. No novelty is claimed there.

## Relation to neighbouring material

- **Transseries volume**, Part "Inversion: the apparatus for a rapidly growing function": the theorems above. The manuscript read only the volume's README.
- **Collection neighbours**, related in method only: [`a277280-hermite-maximum`](../a277280-hermite-maximum/) (the largest coefficient of another polynomial family), [`q-integer-product-unimodality`](../../../log-concavity-and-unimodality/q-integer-product-unimodality/) (products of q-integers and a smoothing threshold, another family and question), and the Edgeworth expansions of [`hardinian-array-diagonal-asymptotics`](../../../enumerative-combinatorics/hardinian-array-diagonal-asymptotics/) and [`preorder-root-polytopes`](../../../enumerative-combinatorics/preorder-root-polytopes/). No shared theorem.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report; none of its statements is formalized. The Lean declarations the notes in Section 9 name, `Fabius.staircase_separation` and `Fabius.staircase_separation_fails` (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`), formalize the separation step of the staircase theorem in general; they verify nothing specific to this report.

## Building

From a scratch copy of `article.tex`, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 19 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

## Rerunning the programs

The delivered commands assumed all three scripts beside a `data/` directory. In the shipped layout:

- `code/verify.py` writes its two CSVs to `--out`, whose default is `data/` **beside the script**, that is `code/data/`, not the shipped `data/`.
- `code/derive_coefficients.py` writes `symbolic_output.txt` **beside itself**, that is `code/symbolic_output.txt`, not the shipped `data/symbolic_output.txt`.
- `verify.py` and `all_orders.py` print their reports to standard output; the shipped `data/verification_output.txt` and `data/all_orders_output.txt` are captures of it.

Run them on a copy and compare with the shipped files:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a039831-two-fourier-peaks
W=$(mktemp -d); cp -r "$R/code" "$W/"; cd "$W"
U="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$U code/verify.py --max-n 400 --digits 70 --out out > verification_output.txt     # about 1-2 min
$U code/derive_coefficients.py                                                  # about 30 s; writes code/symbolic_output.txt
$U code/all_orders.py --n 100 --k 4954 --order 8 --digits 70 --check > all_orders_output.txt   # about 7 s
```

The intake's run on a copy reproduced both CSVs byte for byte (Python's `csv` module writes CRLF on every platform, so the delivered CSVs are CRLF and are stored with a `-text` attribute). `all_orders_output.txt` came out byte-identical, `symbolic_output.txt` equal apart from line endings, and `verification_output.txt` equal apart from line endings and its elapsed-time line (the delivery recorded about 16 s; the intake's run took 72 s).

## Checks by the intake

- Rows recomputed exactly through n = 200 by an independent sliding-sum program: M_1, …, M_5 = 1, 2, 4, 13, 57; every row mass equals (n+1)!.
- Relative error of the two-correction formula: about 8.8 × 10^-4, 1.24 × 10^-4 and 1.70 × 10^-5 at n = 50, 100, 200, a ratio of about 7.3 per doubling, consistent with O(log n/n³).
- The three programs rerun on a copy, as above.

## Disclosures and discrepancies

- **Not shipped:** the delivered README (replaced by this one) and the delivered 18-page PDF (replaced by a build of the edited text). The delivery had no checksum ledger; `SOURCE_MANIFEST.md` is a provenance record with URLs and the pin, kept as delivered.
- **Moved files.** The delivered `verify.py`, `derive_coefficients.py` and `all_orders.py` (archive root) are shipped in `code/`; `verification_output.txt`, `symbolic_output.txt`, `all_orders_output.txt` and `requirements.txt` (archive root) are shipped in `data/`. The CSVs were already in `data/`.
- **Delivery wording in shipped text.** The article's "the supplied program", "the accompanying archive" and "the package" mean the files of this directory; a note in Appendix B says so. `SOURCE_MANIFEST.md` says the CSVs and symbolic output were generated by the supplied programs, which remains true of the shipped copies. The delivered README's commands assumed the delivered layout; use the commands above.
- **Edited text.** `article.tex` is the delivered manuscript with the label prefix, an editorial note after the abstract, notes marked "[Added October 1, 2026, batch 73O2]" in Section 9 (twice), research question 9, Section 12 and Appendix B, one bibliography entry (the transseries volume) and Appendix C (provenance). Nothing was removed.
