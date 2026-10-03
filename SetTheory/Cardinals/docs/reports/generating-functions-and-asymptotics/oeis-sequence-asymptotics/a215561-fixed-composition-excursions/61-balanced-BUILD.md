# Build and verification receipt

Date: October 1, 2026.

## Article

- Source: `article.tex`.
- Output: `article.pdf`, 25 A4 pages.
- Engine: pdfLaTeX.
- Final log: no undefined references, no overfull or underfull box warnings, and no LaTeX warnings detected.
- Visual inspection: all 25 pages rendered with Poppler/pdftoppm and inspected in page contact sheets. Dense symbolic formulas and numerical tables were additionally inspected at 150 dpi.
- Geometric check: no extracted text block came within 10 PDF points of an outside page edge.
- The PDF is searchable, contains embedded bibliography links, and is not encrypted.

## Programs

The following commands completed successfully:

```sh
python code/verify.py
python code/derive_alpha5.py
```

The execution environment used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. The supplied `requirements.txt` records the two library versions.

Independent count-vector enumerations covered:

| Alphabet size r | Values n | Rectangular states |
|---:|:---|---:|
| 2 | 0..24 | 625 |
| 3 | 0..24 | 15,625 |
| 4 | 0..18 | 130,321 |
| 5 | 0..16 | 1,419,857 |
| 6 | 0..6 | 117,649 |
| 7 | 0..4 | 78,125 |

All finite exact assertions passed. Separate exact bridge-logarithm checks covered 120 nonempty balanced count vectors. An independent height-based weighted enumeration checked the ambient five-step sextic through length 24. Exact symbolic arithmetic reproduced both the polynomial elimination and the first asymptotic correction.

The n=20 and n=50 fifth-row terms in the numerical tables were external OEIS b-file inputs, not outputs of the independent enumeration. The multiprecision numerical tests are not interval certificates or proofs of the infinite claims. No Lean code was compiled.

LaTeX auxiliary files and intermediate page images are intentionally excluded from the delivery archive.
