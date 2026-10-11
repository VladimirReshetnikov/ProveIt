BARNES RESOLVENT AND NORMALIZATION CHECKS

Requirements: Python 3, mpmath 1.3.0, SymPy 1.14.0.

  python3 verify_normalization.py
  python3 verify_barnes.py

Both scripts work from any current directory and write JSON beside
themselves. Existing records are replaced; run a copy to preserve hashes.

There are 18 exact finite checks: the multiple-Gamma multiplicity
polynomials and normalization through rank six, plus the corrected
pointwise reflection algebra. The all-rank proof is in the article.

The seven 65-digit numerical comparisons evaluate:
  - the depth-two derivative D and the T_n Fourier generator separately,
    at two values of q;
  - the complete log-Barnes-G resolvent against direct quadrature at
    three z values, including both half-planes;
  - the real component at b=3*pi and the removable q=0 value at b=pi.

The double sums use outer N=150, inner M=360, and 100 explicit zeta-tail
terms. The largest D/T discrepancy is 9.74e-47; the largest full-transform
discrepancy is 4.39e-49. These are floating-point diagnostics, not certified
enclosures. The recorded runtime of the numerical script is about ten
seconds in the development environment.

A separately recorded nonzero residual at x=1/4 documents the pointwise
error in Mezo equation (7). Its proof is elementary algebra and endpoint
asymptotics; the residual itself is not a proof or a pass/fail identity test.
