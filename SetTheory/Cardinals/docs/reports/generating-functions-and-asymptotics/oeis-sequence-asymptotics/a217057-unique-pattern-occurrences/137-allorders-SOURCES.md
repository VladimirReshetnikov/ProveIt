# Sources and provenance

`Report137.tex` is the reader-facing proof document; `Report137.pdf` is its
rendering. The underlying all-orders proof source was frozen and independently
reviewed at SHA256
`0070de0a487f589f51c46ad5b6cc92d23565659fd183775291731eace5849493`.
The resulting Report137 article expands the exposition and uses U_j for the
tail arrays, v_n for the convolution sequence, and Phi_m for the finite
single-log pairings. Its theorem is conditional on the explicitly inherited
exact gluing, character-integral, global-bound, and positivity inputs proved in
the preceding reports. Source review is separate from the finite replay.

The complete final Report135 companion is included unchanged at
`companion135/`, with its own complete unchanged Report134 companion. Their
original manifest hashes are hard-coded in the new verifier and listed in the
README. They supply the exact counting identities, global estimates,
finite lower certificate, and first two correction orders. Neither their
sources nor their original verifiers have been edited. The historical scope
limitations in their READMEs remain part of their original records.

The new code is a compact standard-library implementation of the displayed
finite algebra. `checks/fixtures.json` contains exact outputs reconstructed by
the replay, including rational Gaussian moments, singular coefficients,
contractions, fixed-shift weights, explicit scalar synthetic regularization
checks, and formal inverse cancellations. No external sequence download or
third-party numeric data is required. The regularization fixtures are expressly
synthetic; they do not claim to approximate the actual infinite A217057
constants. The optional explicit symbolic f_3 supplement is omitted.

Primary mathematical references used by Report137 include:

- L. Isserlis, On a formula for the product-moment coefficient of any order of a
  normal frequency distribution in any number of variables, Biometrika 12
  (1918), 134–139. DOI: https://doi.org/10.1093/biomet/12.1-2.134
- NIST DLMF, equation 5.4.14, harmonic numbers and the digamma function:
  https://dlmf.nist.gov/5.4.E14
- NIST DLMF, equation 5.11.2, fixed-order digamma asymptotics:
  https://dlmf.nist.gov/5.11.E2
- NIST DLMF, equations 2.10.1 and 2.10.8, Euler–Maclaurin and harmonic
  asymptotics with remainder:
  https://dlmf.nist.gov/2.10.E1 and https://dlmf.nist.gov/2.10.E8

The article states and verifies the hypotheses needed for its applications.
No third-party paper PDF, private working note, or raw review report is
redistributed. This companion can be replayed offline.
