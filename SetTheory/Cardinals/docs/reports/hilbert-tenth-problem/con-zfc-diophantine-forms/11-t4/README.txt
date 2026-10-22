Combined Diophantine constructions for Con(ZFC), 22 October 2026

Start with report.pdf (10 pages) and its editable report.tex.

Recommended small system: comparison/hybrid_system61.json
  15 strictly positive unknowns; six equations; maximum degree 28;
  61 binary arithmetic operations including fixed-numeral arithmetic.

Single positive-domain equations:
  comparison/hybrid_product69.json: degree 99, 69 operations.
  comparison/hybrid_sos78.json: degree 56, 78 operations.
  comparison/product67_T4.json: degree 155, 67 operations (existing
  normalized arithmetic with the new coefficient tuple).

Low-degree alternative:
  quartic/quartic33_normalized.json: 33 strictly positive unknowns,
  24 explicit quadratic equations. Their sum of squares has exact degree 4.
  quartic/quartic33_ordinary.json gives a second such lift.
  The normalized lift requires fewer additional number-theoretic dependencies.

Unrestricted integer domain, with no positivity side conditions:
  reduction/signed31_product.json: 31 integers, degree 188, 127 operations.
  reduction/signed31_sos.json: 31 integers, degree 100, 136 operations.
  reduction/signed31_system.json: 31 integers, six equations of maximum
  degree 50, 119 operations.
  Intermediate signed33 files are retained as proof stepping stones.

FIXED COEFFICIENT BINDING
All main files in INSTANCE.json use the complete tuple in
bridge/T4_CONSTANTS.json: T4-37075-tightband-5pow18.
The tuple is defined by finite formulas and all 37,075 literal tiles in
bridge/t4_windows.json. Its base is B=2^(5^18). Coefficient numerals are
not expanded: beta alone would take about 477 GB in binary.
The high-mask port is MF_native+B-1, NOT MF_native.
Historical files under sources/ retain their original bindings and serve
as provenance or separately proved fallback instances. Do not mix their
coefficients with one another or with the new tuple.

WHAT IS PROVED
The mathematical arguments show that existence of a solution is equivalent
to blank K215 halting and hence to a finite ZFC refutation. Consequently,
formalizably in ZFC, lack of solutions is equivalent to Con(ZFC).
The complete new arithmetic, sign, odd-port, lift and T4 adapter arguments
are in the accompanying proof documents. Existing universal compiler and
logical endpoint theorems remain substantive pinned dependencies.
This is not a proof of Con(ZFC), a global minimality result, or a newly
kernel-checked composite Lean/Rocq theorem. No accepting K215 run is claimed.

REPRODUCE
Python 3.10+ and SymPy are needed (tested with SymPy 1.14.0).
Run without -O, so assertion-based audits are enabled:

  python verify_all.py

This first checks the hash manifest, then replays the owned finite and
symbolic audits in a temporary copy. It never imports or executes downloaded
repository programs, materializes giant final coefficients, or searches for
a ZFC refutation. All test outputs and exact scopes are in VALIDATION.json
and the component receipts. A sign-mutation negative control is included.
The full tile enumeration may take a little time.

A standard TeX Live installation builds the report with:
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

COMPARISON AND PROVENANCE
comparison/COMPARISON.md compares all eight packets; its source checker
independently recounts 24 representative circuits. Source files are scoped
copies, not standalone copies of every historical package. Their old links
may refer to material not copied here. No upstream repository was modified.
The new proofs and programs are offered for incorporation under the
repository's MIT-0 license; original sources retain their provenance.
