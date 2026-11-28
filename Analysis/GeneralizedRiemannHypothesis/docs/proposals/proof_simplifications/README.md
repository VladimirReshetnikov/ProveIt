# Three shorter steps in the theta-lift proof of Dirichlet GRH

Read **proof_simplifications.pdf**. The 11-page paper gives three substitutions in the readable proof by Levent Alpöge and Claude. Each one preserves the mathematical conclusion required downstream.

| Pages | Result |
| --- | --- |
| 1–2 | Summary and the arithmetic estimate that detects the prime remainder |
| 3–4 | Good auxiliary prime from two ordinary Dirichlet polynomials and Heath-Brown's quadratic large sieve |
| 5 | Why the selected prime rules out a hypothesized zero and yields RH |
| 6 | Direct smoothed Perron inversion at the far cutoff |
| 7–8 | Stronger spanning theorem on the ramified source, with an example testing the logarithmic translate budget |
| 9 | Source interfaces, verification scope and references |
| 10–11 | Proof of good-prime selection by elementary character sums and Fourier completion |

For a fixed height and fixed modulus, let g be the distance of the left edge of the zero-detection rectangle from the critical line. The two-polynomial proof bounds the number of exceptional auxiliary primes between X and 2X by O(X^(1−g/2+ε)). The elementary variant gives O(X^(1−g/4+ε)). A second argument proves a stretched-exponential bound for the prime remainder at the far cutoff. A third improves the missing target dimension from 4d/b² to 20d/b⁴ at the original translate budget. The theta-lift and covolume estimates in the readable proof still give the near-cutoff bound. The large-sieve alternative is already suggested in the source.

## Rebuild the PDF

Keep the four LaTeX files together. A standard TeX Live installation with latexmk and Latin Modern supports

    latexmk -pdf -interaction=nonstopmode -halt-on-error proof_simplifications.tex

## Exact finite checks

Run from the extracted directory, using Python 3.10 or newer with its standard library.

    python3 checks/check_convolution.py
    python3 checks/check_completion.py
    python3 checks/check_spanning.py

The first script verifies 24 instances of the truncated Möbius product, including an imprimitive nonreal character and unequal cutoffs. The second verifies all 204 Fourier frequencies for eight primitive characters, including four genuinely complex twists, by exact cyclotomic arithmetic. The third checks the restricted rank recurrence on 1,024 coordinate subspaces, the uncovered-coordinate formula for the incidence example, and the codimension constants.

## Source provenance

The readable grh/ tree is 2e133df63d7f4da6b3059c4195324f8e9187ba73. The attached guide's [ProveIt revision](https://github.com/VladimirReshetnikov/ProveIt/tree/d8415e76ad850651f8c0083afe689dd9f4a45a10/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh), the [inspected main snapshot](https://github.com/VladimirReshetnikov/ProveIt/tree/8dd060b05dd9aacda4ee48d5c7f9525adf329bcd/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh), and the [checked upstream revision](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh) give the same directory tree. The TSV identifies 46 anchors in 17 source files. To verify their bytes and line text against a local checkout, run

    python3 checks/check_source_anchors.py /path/to/grh

All four scripts were run for this report. The replacements are mathematical proofs on paper. Independent Lean verification results for the original development are available in [Sutherland's verification record](https://math.mit.edu/~drew/shortgrh/).
