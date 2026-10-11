# Harmonic Gaps, Gamma Derivatives, and Mixed Tail Moments

**Joint Lerch generators and exact centered values**  
ProveIt research continuation — 11 October 2026

This package contains a comprehensive research article with ordinary mathematical proofs, executable verification programs, result records, and an integration ledger. Its immediate targets are R1, R7, and R8 of the incoming *Harmonic Parity and Resolvent Identities* report.

The source snapshot is `VladimirReshetnikov/ProveIt` at commit `7bd45777a8a127e5dc69aff8887ca36a79a3059d`. The manuscript sources and all eleven incoming archives were inventoried. The targeted mathematical review and its limits are described in Section 5 of the article.

## Results

| Target | Result proved in the article | Location |
|---|---|---|
| R7 | A joint multiple-Lerch completion for arbitrary independent harmonic orders; the full zero-block decoration series converges locally normally on the unit polydisc, independently of depth. | Section 2 |
| R8 | Every transverse derivative at every nonpositive center for one marked harmonic index, including explicit Gamma and Stieltjes gaps, normalized Mellin integrals, arbitrary unmarked nonpositive decorations, and finite endpoint formulas. | Section 3 |
| R1, two-factor sector | Every centered even moment of two even-order Hurwitz tails, with a finite Bernoulli formula, reduction to ordinary zeta products, a fixed finite spanning list, and an analytic polylogarithmic generating function. | Section 4 |
| Spectral derivative extension | Every derivative of a mixed-tail Dirichlet series at a centered even spectral value has a convergent logarithmic-sum representation with explicit finite Hurwitz correction terms. This does not claim an arithmetic reduction of the remaining logarithmic sum. | Section 4 |

For example, with `x_n=n+1/2` and `T_j(n)=ζ(j,n+1)`, the article proves

```text
sum T_2(n) T_4(n) = 15 ζ(5)/2 - 3 ζ(2) ζ(3),

sum [x_n^4 T_2(n) T_4(n) - 1/3]
  = -7 ζ(2)ζ(3)/80 - ζ(2)/30 - ζ(3)/4 + 7 ζ(5)/32 - 3/40.
```

Both displayed sums are ordinary convergent series. The subtraction in the second is part of the identity. Since `T_2=ψ′` and `T_4=ψ‴/6`, these also give exact unequal-order polygamma-product identities.

The article includes twelve further research questions. Products of four or more tails, several independently marked positions, arithmetic reduction of the remaining logarithmic moments, and the Gaussian S6 and revised S8 candidates remain open in the stated senses.

## Files

| File or directory | Contents |
|---|---|
| `Harmonic_Gaps_and_Mixed_Moments.pdf` | Complete article, with linked contents and references. |
| `Harmonic_Gaps_and_Mixed_Moments.tex` | Complete standalone LaTeX source; no project-local inputs are required. |
| `article.tex`, `preamble.tex`, `sections/`, `references.tex` | Modular source for editorial integration. Edit these files and regenerate the standalone source. |
| `build.py` | Regenerates the standalone source and builds the PDF. |
| `integration_ledger.md` | Precise question-to-result map, placement suggestions, attribution, normalization safeguards, and remaining boundaries. |
| `verification/` | Exact finite checks and independent numerical diagnostics. |
| `results/` | Recorded machine-readable verification results. |
| `provenance/` | Immutable source URLs, file sizes, Git blob identifiers, and SHA-256 hashes. |
| `requirements.txt` | Python versions used for the recorded calculations. |
| `SHA256SUMS.txt` | Checksums of the delivered files, excluding this checksum file itself. |

## Build the article

A TeX installation with `latexmk` and `pdflatex` is sufficient. The source uses standard TeX Live packages, including `lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `mathrsfs`, `booktabs`, `longtable`, `enumitem`, `microtype`, `xurl`, `fancyhdr`, `hyperref`, and `bookmark`.

From this directory:

```bash
python3 build.py
```

Intermediate TeX files go into `build/`; the finished PDF is copied to the package root. To regenerate only the standalone source:

```bash
python3 build.py --source-only
```

The standalone source can also be compiled directly with `latexmk -pdf Harmonic_Gaps_and_Mixed_Moments.tex`. The modular entry point `article.tex` is independently compilable if its inputs are retained.

## Reproduce verification

The recorded environment was Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0. Install the two Python dependencies if needed:

```bash
python3 -m pip install -r requirements.txt
python3 verification/run_all.py
```

Do not run Python with optimization (`-O`), because the programs deliberately use assertions. The scripts overwrite their corresponding JSON records in `results/` and stop on a failed identity or an exceeded diagnostic tolerance.

| Program | Exact checks | Numerical cases |
|---|---:|---:|
| `verify_zero_block_kernel.py` | 590 | 0 |
| `identity_moments_verify.py` | 460 | 30 |
| `verify_r8_audit.py` | 0 | 15 |
| `verify_mellin_derivatives.py` | 0 | 24 |
| `identity_generator_verify.py` | 0 | 3 |
| **Total** | **1,050** | **72** |

The exact checks concern finite rational or symbolic identities. The numerical cases compare independent formulas at 65, 80, or 95 working digits. The three generator cases use 65 Taylor coefficients apiece; those coefficients are inputs to the comparisons, not 65 additional exact identity assertions. Numerical agreement is not an interval certificate or a replacement for the analytic proofs.

## Integration and attribution

The geometric harmonic kernel and the original entire interpolant are due to Ihara, Nakamura, and Yamamoto; their published 2025 reference is supplied. The relative normalization, fixed-index gap calculus, and preceding one-free-order generator retain their incoming-report attribution. Bernoulli, Hurwitz, Gamma/Barnes, and Euler double-zeta identities remain classical ingredients.

The proposed advancement is relative to the inspected repository corpus. Literature-wide priority, arithmetic independence of displayed coordinates, and proof-assistant formalization are not asserted. No newly false source theorem was established in the targeted audit. The article instead records concrete normalization safeguards, an exact continued-versus-literal boundary example, and bibliographic and question-ledger updates.

For integration, preserve the initial convergence domains, the strict Bernoulli endpoints, the centered cutoff coordinate, the distinction between `ζ(0,1/2)=0` and `ζ(0)=-1/2`, and all stated branch and additive normalizations. The detailed ledger identifies where each of these affects a formula.
