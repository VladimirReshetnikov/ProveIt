# All fixed order asymptotics for distinct parabolic double cosets

This package accompanies the research article on A260700, the number of **distinct subsets** of the symmetric group that are double cosets of standard parabolic subgroups. Equal subsets are counted once, even when their presentations differ.

## Main result

With rho = log(2) and K = exp(-rho²/2)/(4rho²), for every fixed nonnegative integer M,

p_n = K n! rho^(-2n) [sum_(j=0)^M B_j(rho)/n^j + O_M(n^(-M-1))].

The leading equivalent is Thomas Browning's established 2021 result. The first correction proved here is

B_1(r) = r²/2 - r³ - 11r⁴/12 + r⁵/4,

which proves his higher-order conjecture with

c = -K B_1(rho) = 0.108197052893921571585327453732… > 0.

The article provides full analytic proofs, exact B_1 and B_2, an appendix with B_3 and B_4, a finite coefficient algorithm for any fixed order, and properly qualified inverse models and integer-threshold brackets. A bounded primary-source search through 2 October 2026 found no later solution to the precise correction conjecture; this is not a claim of exhaustive novelty or external peer review.

## Files

- `article.pdf`: the research article
- `article.tex`: editable LaTeX source
- `code/coefficients.py`: original exact rational coefficient generator
- `code/validate.py`: Browning's finite formula implemented with integer recurrences, actual group-subset enumeration, and cycle checks
- `code/inverse.py`: Lambert-W, Newton and rounding diagnostics
- `code/replay.py`: a complete offline computational replay
- `code/verify_manifest.py`: SHA-256 and byte-count verification
- `data/coefficients-order4.json`: exact D, U and B polynomials through order four
- `data/exact-values.json`: locally computed p_n and q_n for n = 0,…,400
- `data/b260700.txt`: separately attributed OEIS numerical reference data
- `results/validation.json`: recorded exact and residual checks
- `results/inverse-validation.json`: numerical inverse diagnostics and a rounding counterexample
- `SOURCES.md`: primary-source attribution and scope
- `MANIFEST.json`: checksums of all other declared deliverable files

## Replay

Python 3.10 or later is required. The tested environment used Python 3.12.14, SymPy 1.14.0 and mpmath 1.3.0. Dependencies are pinned; no network is used by the programs after installation.

```sh
python -m pip install -r requirements.txt
python code/verify_manifest.py
python code/replay.py --quick
python code/replay.py --full
```

The quick replay recomputes exact values through n=40. The full replay uses n=400. Both regenerate the correction polynomials through order four, enumerate all distinct group-coset subsets for n≤5, verify 259 cycle identities, compare with stored exact data, and run the inverse diagnostics. Outputs go into `replay-output/`, leaving the supplied data unchanged. Use `--output-dir PATH` for another output directory.

To generate a different fixed coefficient order:

```sh
python code/coefficients.py 5 --output-dir replay-order5
```

This uses exact rational expressions, not numerical interpolation or fitting. Runtime and expression size grow with the requested order. The computation of exact p_n and q_n also grows substantially with the limit.

To rebuild the PDF with a standard TeX installation:

```sh
bash build_pdf.sh
```

The build uses common LaTeX packages: lmodern, amsmath, amssymb, amsthm, mathtools, booktabs, microtype, geometry, enumitem, fancyhdr, xcolor, hyperref and listings. If the system TeX format or font-map cache is missing, the script builds a writable cache under `.build/` from the installed TeX resources. It does not download software or depend on another workspace. Computational reproduction does not require TeX. PDF byte identity is not expected across TeX versions because metadata and rendering can differ.

## Interpretation and limits

The article proves an expansion for every **fixed** order M. It does not prove convergence of the infinite series, optimal truncation, or an exponentially improved transseries. The leading constant and exact enumerative formula belong to Browning; the general methods of singularity analysis and Stirling transforms are not claimed new here.

Numerical agreement is a diagnostic, not the proof. No effective global remainder constants or finite starting indices have been extracted. The smooth inverse model is not a canonical interpolation of the discrete sequence. In particular, its ceiling need not equal the exact threshold when the inverse lies extremely close to an integer. The checked example y=p_25+1 has exact threshold 26 but ceil(F_1^(-1)(y))=25.

No full third-party paper, private review notes, credentials, environment-specific build caches, or downloaded software is included. Nothing has been submitted to OEIS, a journal, or an external repository as part of this package.
