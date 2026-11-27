# Two inverse theorems for Dirichlet zeros

26 November 2026

## Papers

1. **Recovering prime weights from damaged residue data** — `layers/residue_recovery.pdf`. At fixed modulus, each sufficiently high dyadic block of distinct Dirichlet zero ordinates contains a basis of bounded multiplicity vectors, each recurring at a positive proportion of all candidate locations. This gives exact recovery of arbitrary complex weights on the relevant power residues despite a positive proportion of incorrectly reported or missing residues. Small errors on the other observations give bounded errors in the weights. The calibration, the factor of m in the noise scale, and the dependence on q are specified in the paper. Its input is Dirichlet GRH together with the joint short-interval Gaussian theorem of Bombieri and Perelli.
2. **Recovering omitted primes from normalized zero spacings** — `gaps/gaps.pdf`. The germ of the limiting nearest-neighbor gap distribution of the positive imaginary-axis zeros of an imprimitive Dirichlet L-function identifies all omitted primes when there are at least three. The proof combines a classical spacing formula with the six exponentials theorem. This result is independent of RH. Exact identification is discontinuous for weak convergence of the laws.

The earlier note *Reading arithmetic weights from poles of a prime series* already established the power-image classification and local recovery from intact data. The first paper adds positive density at distinct locations, frequent bounded multiplicity patterns, and recovery under corruption. Both papers contain analytic proofs and references. The published Lean result is used as an input in the first paper. The new theorems have not been formalized in Lean and no upstream Lean rebuild was performed for this archive. The papers describe the scope of the prior-art comparisons.

## Reproduce the PDFs

Use a standard TeX Live installation with the AMS, geometry, Latin Modern, microtype, fancyhdr, xcolor, booktabs and hyperref packages. Each main TeX file is self-contained. From the root of this archive:

~~~sh
(cd layers && pdflatex -halt-on-error residue_recovery.tex && pdflatex -halt-on-error residue_recovery.tex)
(cd gaps && pdflatex -halt-on-error gaps.tex && pdflatex -halt-on-error gaps.tex)
~~~

## Reproduce the calculations

Use Python 3.9 or later. The numerical Dirichlet-zero example uses mpmath 1.3.0. The other three programs use the Python standard library. From the root:

~~~sh
python3 layers/check_layers.py
python3 layers/check_decoder.py
python3 layers/observed_example.py
python3 gaps/verify_gaps.py
~~~

| Program | Recorded output | What is checked |
| --- | --- | --- |
| `layers/check_layers.py` | `layers/check_layers.txt` | Exact cyclotomic Fourier identities, rational ranks and formal prime-power coefficients, including derivative signs, modulo 13, 15 and 16 |
| `layers/check_decoder.py` | `layers/check_decoder.txt` | Exact median decoding for all 27,417 placements of two gross errors and one erasure on the first synthetic design, plus 3,990 placements on the second design, both with and without bounded noise |
| `layers/observed_example.py` | `layers/observed_example.txt` | Floating-point residue estimates at ten sampled zeta and beta zero ordinates, with corruption and recovery of two complex arithmetic weights; completeness and simplicity of the samples are not certified |
| `gaps/verify_gaps.py` | `gaps/example_output.txt` | Predicted and measured spacing tails and endpoint masses for two different characters omitting the same primes, up to height one million |

`SHA256SUMS` lists the digest of every other member. To verify the files, run `sha256sum -c SHA256SUMS` from the extracted directory.
