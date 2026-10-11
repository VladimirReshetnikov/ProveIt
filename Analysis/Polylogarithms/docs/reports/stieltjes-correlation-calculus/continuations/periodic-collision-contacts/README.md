# Periodic Stieltjes Collisions

**Exact Contact Terms, Finite-Part Fubini Laws, and Gamma–Polylogarithm Primitives**  
Research continuation for the ProveIt programme, 10 October 2026.

The 23-page article is `Periodic_Stieltjes_Collisions.pdf`; its standalone editable source is `Periodic_Stieltjes_Collisions.tex`.

## Main result and the question it answers

Section 11.1 of the preceding *Coincident-Point Stieltjes Calculus* report asks for the local, delta-supported terms in a periodic extension of its off-point collision formulas. This delivery proves that comparison for **fixed unit-coordinate Hadamard extensions** at both endpoints, at every Stieltjes index and every argument-derivative order.

Writing `T[m,p] = Fp gamma_m^(p)`, `r = p+q`, and `R` for periodic reflection, the theorem is

```text
(R T[m,p]) * T[n,q] = H[J[m,n,p,q]] + kappa[m,n,p,q] delta^(r).
```

There are no lower delta derivatives. The article gives a finite gamma–harmonic generating function for every coefficient. At Stieltjes index zero,

```text
kappa[0,0,p,q] = (-1)^p * (
    2*zeta(2) + (H[r]-H[p])*(H[r]-H[q]) - H[r]^(2)
).
```

In particular the digamma base case requires `(pi^2/3) delta`. This contact coefficient is not the same object as the finite scalar collision constant in the preceding report.

The article also proves exact finite-part Fourier identities, a polylogarithm order-derivative representation with its complete Abel limit, and explicit Bernoulli corrections for all mean-zero antiderivatives. A normalized primitive kernel produces ordinary log-Gamma covariance identities. Classical and previously established ingredients are attributed and distinguished from the extension comparison.

## Contents

- `Periodic_Stieltjes_Collisions.tex` and `.pdf`: complete article with proofs, normalization safeguards, further questions, and references.
- `code/exact_checks.py`: finite exact coefficient and Fourier-polynomial checks.
- `code/numerical_checks.py`: independently integrated finite-part modes and ordinary Gamma integrals.
- `data/contact_coefficients.json`: 420 explicit contact coefficients for `p+q <= 6`, `m+n <= 4`.
- `data/exact_checks.json`, `data/numerical_checks.json`: recorded results and configurations.
- `code/build.py`, `code/inspect_pdf.py`: clean temporary-directory LaTeX build and PDF rendering/structural checks.
- `integration/INTEGRATION.md`, `integration/manuscript_insert.tex`: proposed placement and a compact, unapplied manuscript insert.
- `data/source_provenance.json`, `data/research_status.json`: inspection and claim scope.
- `SHA256SUMS` and `code/verify_manifest.py`: integrity verification for the delivered files.

The formulas in the JSON coefficient table use `pi` for pi and `zeta_j` for the ordinary zeta value at the odd positive integer j. Even zeta values have been simplified to rational multiples of powers of pi. `delta_order` is part of each record. These are formal expression coordinates, not an assertion of arithmetic independence.

## Reproduction

Python 3.10 or later and a TeX installation with `pdflatex` are required. The recorded Python run used 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. Rendering used PyMuPDF 1.26.7 and Pillow 12.3.0.

```bash
python -m pip install -r requirements.txt
python code/verify_manifest.py
python code/exact_checks.py
python code/numerical_checks.py
python code/build.py
python code/inspect_pdf.py
```

Verify the manifest **before** regenerating files. A rebuild may change PDF metadata, engine-version information, or receipts and will therefore require a new manifest. The article's LaTeX preamble lists its TeX package dependencies. `build.py` does not leave `.aux`, `.log`, or `.toc` files in the delivery directory. `inspect_pdf.py` places rendered page images in a sibling review directory by default; those images are not bundled.

## Evidence and limits

The recorded exact run passes **760 assertions** and generates **420 contact formulas**. The numerical run passes **40 diagnostics at 60 decimal digits**, with maximum recorded absolute error below `1.1e-51` against the displayed formulas. It uses truncated convergent Taylor/exponential series and ordinary quadrature, **not rigorous interval arithmetic**. A deliberate missing-atom control is rejected, with discrepancy pi²/3.

The unlimited-index conclusions rest on the analytic proofs in the article. Finite checks do not establish the distribution theory, and PDF inspection establishes neither mathematical validity nor independent review. No proof-assistant formalization or external peer review has been performed. Global priority for all consequences has not been established.

The preceding coincident article's open periodic comparison is resolved in the specified normalization. Its off-point formulas and same-point finite constants are retained. No false theorem is attributed to it. The safeguards reject tempting but unjustified extensions, not statements falsely ascribed to the source.

The canonical S6 and revised S8 identities remain conjectural. Cubic products and arbitrary changes of subtraction coordinates remain outside this theorem. The six incoming ZIPs were listed but not all retrieved or audited; the complete coincident TeX was read through the user's Library. No claim of exhaustive non-overlap with the entire repository or those archives is made.

No repository files were modified. Integration remains a separate editorial action.
