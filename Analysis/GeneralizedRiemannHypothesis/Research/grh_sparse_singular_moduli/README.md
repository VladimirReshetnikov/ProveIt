# Five-term equations for singular moduli

Research report, 25 November 2026. Open **report.pdf** to read the paper. **report.tex** is the LaTeX entry point. All proofs, source inputs for the article, finite certificates, and arithmetic replay programs are included.

## Results

For an imaginary quadratic order of discriminant Δ, write h for its class number and s for the least number of nonzero coefficients of a nonzero rational polynomial vanishing at one of its singular moduli. Polynomial degrees and coefficient sizes may be arbitrarily large.

* The report proves **s ≤ 5 if and only if h ≤ 4**, independently of RH and GRH. For h ≤ 5 the minimum equals h+1, apart from j=0 where it is 1. One companion report had already established the four-term threshold and treated 28 of the 29 quintic orders. A second independently reduced the global five-term question to the five orders of discriminants −87, −131, −348, −432 and −675 and excluded them through exponent width 65,536. We eliminate all five for unbounded width. The six-prime test completes the quintic census at Δ=−131. The global argument covers every higher degree.
* Using the Dirichlet GRH theorem in the cited Lean repository, the report proves **s ≫ h/(log |Δ|)²**. In particular log s / log |Δ| tends to 1/2. An unconditional comparison uses Pollack’s theorem on prime nonresidues and the class number bound of Siegel. The second companion report independently obtains both growth exponents.
* An explicit infinite family has s=h+1. A separate density calculation gives a lower relative density above 61.33% for this equality among the orders of prime conductor in Q(i).
* The final research section gives an optimal one-sided Frobenius statistic and a prime-counting criterion for RH for the splitting field of X⁴−2. The analytic inequality in that criterion remains open.

## Replay

From this directory on Linux, use Python 3.10 or later, a C++17 compiler with GNU integer extensions, and a POSIX shell. The arithmetic uses the Python standard library. A typical complete run takes a few minutes. Run with ordinary Python assertions enabled.

```sh
sha256sum -c SHA256SUMS
python3 reproduce.py
```

The transcript recorded during assembly is **checks/reproduction.txt**. Compilation and enumerations use temporary directories. No internet connection or Lean installation is needed for the arithmetic replay.

| To inspect or reproduce | Entry point or data |
|---|---|
| Decision tree reducing every discriminant to 71 small cases | `checks/global_five.py`, `checks/global_five.txt` |
| The 49 complex determinant and 18 single-disk certificates, plus class polynomials for the last four sextics | `checks/verify_five_small.py`, `checks/five_small_witnesses.json` |
| All-exponent elimination at −87, −348, −432, −675 | `checks/verify_five_sieves.py`, `checks/five_sieves.cpp` |
| Independent implementation for −87 and −348 | `checks/fast_sieve/verify.py` |
| The last quintic, Δ=−131, by two implementations | `checks/verify_last_quintic.py`, `checks/independent_quintic.py` |
| Certified ring class polynomials, disk parameters and low-degree censuses | `cm/` |
| Infinite family, density truncations and the finite-group examples | `checks/check_exact_family.py`, `checks/check_prime_conductor_density.py`, `checks/check_frobenius_weights.py` |
| The preceding ProveIt paper's four-term reduction, including its finite sieves | Appendix A, `previous/`, `checks/prior_audit.md` |
| Lean declarations, one-sided criterion, commit and individual Git blob hashes | `checks/source_audit.md`, `checks/upstream_blobs.json` |

The infinite-family and character-theoretic results have general proofs in the paper. Their small checks illustrate the formulas. The arithmetic certificates for the classification exhaust the finite cases that the mathematical reductions leave.

## Source and typesetting

The analysis uses the readable edition of lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`. Our source-identity check matched thirteen files of that checkout. With an existing checkout, run:

```sh
python3 checks/check_source.py /path/to/grh-lean
```

The upstream Lean theorem covers the Riemann zeta function and Dirichlet L-functions. Andrew Sutherland's independent verification logs are cited in the report. The mathematical extensions here are paper proofs and finite arithmetic certificates. An independent Lean formalization of the new results would constitute further work.

To rebuild the PDF with a standard TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The main manuscript includes all section files and the appendix. The source audit and the bibliography link directly to the pinned Lean declarations, earlier ProveIt reports and the mathematical literature.
