# Release quality checks

Date: 2026-10-01

- Producer exact coefficient/remainder/moment checks through n=800: PASS
- Exact rational symbolic coefficient exports through order four; no Float atoms: PASS
- Nine numerical finite-contour tests against the proved explicit tail bound: PASS
- Forty inverse cases through correction order six: PASS
- 1,621 modular congruences in 23 prime-power cases: PASS
- All seven producer output files byte-identical in a fresh clean replay: PASS
- Independent mathematics audit: see audit/independent_audit.md
- Eight-page PDF producer visual inspection: PASS
- Independent second inspection of all eight PDF pages: PASS
- Final TeX log contains no overfull/underfull boxes or warnings: PASS

Visual review applies to PDF SHA-256:
b6ab979ad5e9069ecc677933366a52abb4a6bf5091142142428953160b573131

Integrated TeX SHA-256:
e4b9eac3fe4d1c57db6e45078fb0e00f3d19709fedf891d0a9bfa1e6c5098e2c

Finite numerical quadrature checks are high-precision diagnostics, not interval-arithmetic certificates. The tail bound is proved analytically. The all-orders and inverse remainder constants remain asymptotic existence constants.
