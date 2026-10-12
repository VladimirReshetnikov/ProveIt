# Joint Polygamma Moments, Gap-Eight Reconstruction, and Multiscale Stieltjes Resonances

Research continuation dated **12 October 2026** for the ProveIt project.

## Read the article

- `Polygamma_Moments_and_Stieltjes_Resonances.pdf` is the complete article.
- `Polygamma_Moments_and_Stieltjes_Resonances.tex` is a standalone source: it compiles without the modular source files.
- `article.tex`, `sections/`, and `references.tex` are the modular sources for editing and integration. `build.py` regenerates the standalone source and PDF from these.
- `verification/` contains all verification programs, exact certificates, numerical output, and internal analytical audit notes.

## Main results

1. **Complete joint cumulants through total weight `2n+2`.** An unpaired Gamma deformation gives the means, covariances, and higher cumulants of all real polygamma statistics in this weighted range. Positive-order statistics obey an exact finite Wick rule. The digamma sector has a separate explicit higher-cumulant correction. A nonzero small-shift third moment proves that the single-trigamma Gaussian degree cannot be extended universally.
2. **Effective reconstruction at every fixed even gap, and complete gap eight.** An explicit threshold `B(m)` reduces each fixed-gap question to a specified finite interval. At gap eight the analytic threshold is sharpened to `8192`; an exact certificate proves all `8187` remaining determinants nonzero. An all-order family of ordinary convergent polygamma-product sums follows. The `(14,22)` example supplies every rational coefficient in machine-readable form.
3. **All-index Stieltjes collision constants at two positive monomial scales.** Two mixed resonance laws and one singular resonance law classify all corrections to the coincident finite part. A finite polynomial compiler evaluates their coefficients. Integer trigamma tails arise as first-Stieltjes collision contacts, with an explicit polylogarithmic generator and anchored primitive.
4. **Barnes companion evaluations.** Centered digamma moments and pure trigamma correlations are explicitly evaluated by differentiating the classical first Barnes lemma.

The full article states exact hypotheses, proves the analytic steps, isolates the exact computational proof, and discusses further research. Novelty is claimed relative to the inspected repository baseline, not as an exhaustive historical-priority conclusion.

## Source baseline and integration decisions

Pinned repository revision:

`03112a7d3b91efdd3c00b6e595cf0ffa4694d2dc`

The principal dependencies are the incoming reports:

- `ProveIt_Ordered_Boundary_Identities_2026-10-11.zip`
- `ProveIt_Gap_Six_Harmonic_Determinants_2026-10-12.zip`
- `ProveIt_Gamma_Normalizations_and_Colored_Moments_2026-10-12.zip`
- `ProveIt_Lattice_Contacts_and_Mixed_Zeta_Identities_2026-10-11.zip`

All sources refer to that pinned revision, even where a report's filename is dated the following day. The bibliography identifies the exact input passages and the primary classical references.

Suggested status changes are given in the article's source-audit section. Gap-eight completion is solved with an exact computational component. Joint moment separation is solved in the stated weighted range. Different positive monomial scales are solved through the constant, with all preceding divergent terms specified by finite truncation. The broader all-pairs reconstruction conjecture, the beyond-range cumulants, nonmonomial and three-factor collisions, and the short `S6` and revised `S8` candidates remain open. The old rejected `S8` formula remains rejected.

No new false inherited theorem was found in the targeted dependencies. The article proposes status reconciliation and removal of an already reported duplicated README paragraph. Previous evaluations of the Gamma normalizer and `K_m`, complete gap six, and fixed-rate collisions retain their predecessor attribution.

This package does not modify the repository. No proof-assistant formalization or external peer review is claimed.

## Build the article

Requires Python 3, `latexmk`, and pdfLaTeX with ordinary AMS, Latin Modern, geometry, hyperref, microtype, and table packages.

```bash
python3 build.py
```

The standalone source can also be compiled directly:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error Polygamma_Moments_and_Stieltjes_Resonances.tex
```

The PDF was rendered and visually inspected after compilation. `verification/document_qa.json` records the final build and layout checks.

## Reproduce the mathematics

Install the exact Python dependency versions used in the supplied runs:

```bash
python3 -m pip install -r requirements.txt
```

Run the following commands from the `verification` directory. Python reports are written beside their verifier, or to the explicit `--output` path. The certificate command writes the full indexed list of residues.

### Exact finite proof for gap eight

```bash
g++ -O3 -std=c++17 -Wall -Wextra -pedantic verify_gap_eight.cpp -o verify_gap_eight
./verify_gap_eight 4 8192 > gap_eight_certificate.json
python3 verify_gap_eight_bridge.py
python3 create_gap_eight_example.py
```

The C++ program verifies primality, invertibility of every needed denominator, all `8194` cotangent coefficients by an independent sine/cosine multiplication, and all `8187` determinant residues. It uses no floating-point arithmetic. A second compilation and replay reproduced the complete supplied certificate exactly; see `gap_eight_replay.json`.

The SymPy bridge check reconstructs the original Bernoulli matrices, confirms the determinant bridge and modular residues for `b=5,...,16`, and verifies the rational constants in the analytic threshold. The example generator checks its inverse row and every subtraction coefficient exactly. Real positivity at `17 <= b <= 8191` is not inferred from nonzero residues.

### Joint Gamma-polygamma identities

```bash
python3 verify_gamma_cumulants.py --dps 36 --nodes 56 --output gamma_cumulant_checks.json
python3 verify_gamma_cumulants.py --dps 46 --nodes 72 --output gamma_cumulant_checks_46dps.json
```

Each run includes `122` exact algebra assertions and `17` independent determinant-quadrature cumulant checks. The higher-precision run's largest scaled residual is approximately `2.1e-43`. The expectation side uses inserted one-dimensional integrals and determinant jets, not the same closed Gamma quotient being tested. The excluded third moment is evaluated separately as a diagnostic of the proved small-shift limit.

### Stieltjes collisions and Barnes integrals

```bash
python3 stieltjes_contacts.py
python3 verify_stieltjes_contacts.py
python3 identity_audit.py
```

`stieltjes_contacts.py` exposes:

```python
collision_correction(m, n, r, t, alpha, beta, lam=1, mu=1)
singular_contact(m, n, r, t, j, lam=1, mu=1)
```

The first returns the change from the article's fixed-coordinate finite part `F[m,n,r,t]`. Supply nonnegative integer indices, exact positive rational exponents, and explicitly positive amplitudes. The analytic theorem also covers arbitrary positive real exponents; the implementation uses rationals for exact resonance decisions. It automatically exchanges the factors when the exponent ordering is reversed and agrees with the inherited formula at equal exponents.

The Stieltjes verifier performs `72` exact assertions plus `8` numerical checks at 64 digits. The independent audit uses 90-digit ordinary quadrature after exact singular integration for six monomial examples and six Barnes identities. A nonresonant irrational example converges slowly because the next exponent is `5*sqrt(2)-7`; the audit records that effect and an acceleration by terms which themselves vanish. Its slow raw convergence is not concealed.

All numerical residuals are diagnostics, not interval certificates. Convergence, continuation, and the limit evaluations are established analytically in the article. The only computational step used as a proof of infinitely many cases is the finite, exact gap-eight completion combined with its proved analytic tail.

## Files for reuse

| File or directory | Purpose |
|---|---|
| Standalone `.tex` and `.pdf` | Complete deliverable |
| `article.tex`, `sections/`, `references.tex` | Modular integration sources |
| `build.py`, `requirements.txt` | Reproduction instructions in executable form |
| `verification/gap_eight_certificate.json` | All 8,187 exact nonzero residues |
| `verification/gap_eight_14_22_example.json` | All 22 coefficients of `P` and all 5 coefficients of `S` |
| `verification/stieltjes_contacts.py` | Exact finite contact compiler |
| `verification/*checks*.json`, `verification/identity_audit.json` | Recorded exact and numerical verification |
| `verification/*audit.md` | Internal independent analytical review notes |

No generated executable, TeX intermediate, or third-party paper is required in the archive.
