# Fixed-composition excursions

## D-finiteness, transcendence, and all-order asymptotics for OEIS A215561

Research report prepared for Vladimir Reshetnikov, October 1, 2026.

The article studies words with n copies of each letter 1,...,r whose kth prefix sum is at most k(r+1)/2. Write A_r(n) for their number. This includes A215562 (r=4), A215570 (r=5), A215571 (r=6), and A215593 (r=7).

## Main results in the manuscript

For every fixed r >= 2, the article proves

    A_r(n) ~ kappa_r (rn)! / (rn (n!)^r),

identifies kappa_r as a positive algebraic kernel-root product, and proves a full inverse-power expansion with algebraic normalized coefficients. It also proves that every fixed-row generating function is D-finite and that every row with r >= 3 has a transcendental generating function. For r=5 it derives

    A_5(n) = (3 sqrt(5)-5)/(8 pi^2) * 5^(5n)/n^3
             * (1 - 13(5-sqrt(5))/(50n) + O(n^-2)).

Further results include a limiting law for interior returns to zero, an extension to unequal positive rational centered compositions, and asymptotic inversion using an exact lower-branch Lambert-W core. Eight follow-on research directions are discussed.

This is a newly written mathematical manuscript, not a peer-reviewed or Lean-verified publication. The finite tests below do not verify the infinite asymptotic or D-finiteness theorems. Those are supported by the written mathematical arguments. The source audit is bounded; exhaustive bibliographic priority is not claimed.

### Important distinctions

The leading constants already posted for r=4 and r=5 are credited to Vaclav Kotesovec. The kernel method and bridge-logarithm identity are classical, and the diagonal theorem is due to Lipshitz. The article applies these tools to the fixed-composition problem and develops the additional deductions explicitly.

The article proves recurrence EXISTENCE for all fixed rows. It does **not** prove the specific order-three recurrence for A215570 in Kauers and Koutschan's Conjecture 15, print a recurrence for A215562, or establish minimal recurrence orders. It also does not claim a complete exponentially small transseries or estimates uniform in growing r.

## Contents

- `article.pdf`: compiled 25-page article.
- `article.tex`: complete editable LaTeX source, with bibliography included.
- `code/verify.py`: exact count-vector enumeration, exact bridge-logarithm checks, an independent weighted sextic check, and numerical asymptotic/inverse diagnostics.
- `code/derive_alpha5.py`: exact symbolic derivation of the first r=5 correction and the ambient algebraic sextic.
- `data/exact_rows.json`: independently enumerated terms, indexed from n=0.
- `data/kernel_constants.json`: numerical kernel constants and exact reduced kernel polynomials.
- `data/diagnostics.json`: asymptotic and inversion diagnostics, each recording the origin of its input term.
- `data/verification.txt`: saved output of the verification program.
- `data/symbolic_verification.txt`: saved output of the symbolic derivation.
- `requirements.txt`: versions of the two Python dependencies used here.
- `SOURCES.md`: source and claim provenance.
- `BUILD.md`: build and visual-QA receipt.

## Reproduce the checks

Python 3.10 or later is intended; the supplied programs were executed with Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py
python code/derive_alpha5.py > data/symbolic_verification.txt
```

After the dependencies are installed, neither program requires network access. The programs write their outputs only into this package's `data` directory. The largest independent enumeration uses 1,419,857 rectangular states. No guessed recurrence is used to generate any of the independently enumerated rows.

For the fifth row, values through n=16 were independently generated. The n=20 and n=50 terms used in the diagnostic table were read from the published OEIS b-file, not independently computed. This distinction is recorded in both the program and the article.

The root computations are high-precision numerical evaluations, not interval-certified root enclosures. Exact arithmetic is used for the finite combinatorial identities, polynomial elimination, and first-correction calculation.

## Build the PDF

A TeX installation with pdfLaTeX and the packages listed in the source is required. The bibliography is embedded, so BibTeX is not needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The final delivered build contains no undefined references or overfull-box warnings. All pages were rendered and inspected for layout; see `BUILD.md`.
