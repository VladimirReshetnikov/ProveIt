# Quadratic central derivatives and positive filters for Dirichlet zeros

## The results

**The turning points of quadratic Dirichlet central derivatives** is the main paper. Using the quadratic case of the repository's Dirichlet GRH input, it proves Sheth and Voo's Conjecture 1.5 and gives the complete list of the 31 signed fundamental discriminants with a strict change of direction. The largest conductor on the list is 97. The classification for every conductor below 512, including the infinite increasing tail of all 31 exceptional sequences, is proved independently of GRH. For an arbitrary fixed character the ratio of successive even derivatives tends to infinity unconditionally.

**The critical moment of a positive filter for Dirichlet zeros** answers the sharpness question in the repository's global-filters section. It halves the universal upper bound to πd/Q*, proves polynomial rigidity at equality and gives exact examples of nonattainment, unique attainment and infinitely many attaining measures. The full complex zero-divisor theorem is unconditional. The critical-line hypothesis identifies this divisor with real Fourier frequencies. The optimal positive-filter coefficient for every family with a sign-changing canonical kernel remains open.

## Files

| File | Contents |
|---|---|
| quadratic_turning_points.pdf and quadratic_turning_points.tex | Six-page main paper and its source |
| critical_filters.pdf and critical_filters.tex | Five-page companion paper and its source |
| verification/verify_small.py and verification/small-certificate.csv | Unconditional interval verification for 312 quadratic characters and every derivative order |
| verification/SMALL-VERIFICATION.md | Details of the integration and truncation bounds |
| verification/verify_derivatives.py and verification/signs.csv | Independent Taylor-series verification of 555 derivative comparisons and the conductor-384 cutoff |

## Reproduction

Compile either TeX file twice with pdfLaTeX, or run the following from this directory with a standard TeX Live installation.

```sh
latexmk -pdf quadratic_turning_points.tex
latexmk -pdf critical_filters.tex
```

To replay the unconditional check with Python 3.9 or later, run the following inside the verification directory. It uses only the standard library.

```sh
python3 verify_small.py > small-replay.csv
cmp small-replay.csv small-certificate.csv
```

The alternative check uses Python with python-flint 0.9.0. It computes rigorous enclosures for central Taylor coefficients and the explicit logarithmic-derivative lower bound in the main paper.

```sh
python3 verify_derivatives.py > flint-replay.csv
cmp flint-replay.csv signs.csv
```

The checked repository revision is cfab41369737c66ae520d179419509eb719367cd. The papers use the source theorem as an input. The presented proofs are mathematical arguments with the stated finite certificates. No additional Lean formalization or kernel replay of the upstream GRH theorem is included.
