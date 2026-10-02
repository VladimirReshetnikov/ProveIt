# Verification scope and results

Date: 2 October 2026. Status: PASS.

The reference outputs cover the following finite checks:

- 355 exact first-failure, finite-difference, uniform-integral and small-state identities
- Coefficients through order 5 for k=2,3,4, with a 60-to-90-digit replay for k=2
- 518 exact imaginary-phase tests and a k=500 first-correction precision test
- Exact recurrence comparisons through n=25 for k=2,3,4,5
- Exhaustive restricted-growth checks at (k,n)=(2,2),(2,3),(3,2),(3,3)
- Exact right-endpoint polynomial tests at k=2,3,4 and r=1,...,7
- Exact integer counts through n=500 and a separate cumulant-based c3 derivation
- Comparisons of c0 through c3 and tau1/tau2 between separate derivations
- Lambert/Newton model inversion at exact count values for k=2,3,4 and n=50,100,200

Every successive truncation from order 0 through 5 reduced the exact absolute error in the tested cases k=2,3,4 and n=100,200,400. The largest absolute difference in the c0-c3 cross-comparison was about 4.02e-60. The low/high precision order-five relative difference was below 1e-59. These are finite checks, not interval or uniform error certificates.

The package was replayed from a clean ZIP extraction. All assertions passed. Manifest checks before and after replay passed. The PDF was rebuilt without a copied format, font map or cache; the build script created them locally. The rebuilt PDF matched the supplied PDF byte for byte in the tested environment. All 16 rendered pages were visually inspected; the final compilation had no overfull boxes or unresolved references.

Tested dependencies: Python 3.12.14, mpmath 1.3.0, SymPy 1.14.0 and pdfTeX 1.40.26 from TeX Live 2025/dev/Debian. Different TeX/font versions may produce different PDF bytes.

- TeX SHA256: 92fd7c5068b5319f1fc97c21561239698754177983e4cbb7d63d67b7c5cc0e4a
- PDF SHA256: 97a66d2c7fa597300a554ae228aa661e47d9827b7f9b7ea25869305aae693561
- Coefficient-generator SHA256: d54cc31ba5b5318eaa07e4524a16f25c9ccacab5ed01adee4fe11fc7ad8d6a48

The proof establishes each fixed order for each fixed alphabet. The checks do not establish convergence of the full series, growing-alphabet uniformity, every requested digit for arbitrary order, certified numerical inverse thresholds, or publication priority.
