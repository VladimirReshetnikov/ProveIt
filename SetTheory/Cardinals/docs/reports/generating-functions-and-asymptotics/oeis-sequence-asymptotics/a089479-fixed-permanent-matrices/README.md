# Report184: binary matrices of fixed positive permanent

This package accompanies Report184, *Fixed positive permanent binary matrices*. It contains the manuscript, original reproduction programs, exact reference data, and independent optional C++ enumerators. No downloaded research papers or third-party executable source are included.

For fixed integer permanent k >= 1, write d = Omega(k). With

    E(z) = sum_{m >= 0} (-z)^m / (m! 2^(m(m-1)/2)),

and its unique zero rho in |z| <= 2, the result has the normalization

    C[n,k] = (n!)^2 2^(n(n-1)/2) / k
             * (rho^(-n) P_k(n) + O_k(2^(-n))),

where P_k has exact degree d. The k=1 DAG case and the SCC transform are classical and credited in the manuscript. The analysis does not cover a growing-k regime or claim worldwide historical priority.

## Quick start

Mandatory Python checks use **only the standard library**, with both ordinary and optimized (`-O`) execution. No network, pip installation, or symbolic-algebra package is needed.

```sh
python3 -B reproduce.py
python3 -B test_build.py
python3 -O -B test_build.py
```

`reproduce.py` regenerates five reference JSON outputs in temporary storage, compares every byte with its supplied reference, and checks exact identities, certificate guards, the explicit remainder constants, and supplied independent exhaustive data. Decimal diagnostics are regenerated too; **they are not rigorous certificates**.

To compile the manuscript and create a new release directory, install a working pdfLaTeX/TeX Live stack, then run:

```sh
python3 -B build.py --output /absolute/path/to/new-release
```

The parent of the output directory must exist. The output must not exist and must be outside the package. The builder refuses to replace existing files or directories and rejects unexpected source files, caches, symlinks, compiler warnings, unresolved references, and overfull/underfull boxes. It creates:

- `Report184.pdf`
- `Report184.tex`
- `Report184_code.zip`
- `ARTIFACTS.json`, with sizes and SHA-256 hashes of those three artifacts

The ZIP includes its own complete `SHA256SUMS.json` inventory. Extract it into a fresh directory and run `python3 -B verify_manifest.py` before reproducing or rebuilding. The manuscript source is standalone and needs no external bibliography or graphics files.

## Exact certificates versus diagnostics

- `certificates/exact_checks.json`: exact SCC-kernel formulas for k=3,4, source count comparisons for n<=6 and k<=4, exact matrix counts through n=20, and exhaustive diagonal-one comparisons through n=4
- `code/constant_certificate.json`: outward rational-interval decimal enclosures for rho, a, H2(rho), H3(rho), H4(rho), and every low-k Laurent coefficient; stored beside its unchanged original guard script intentionally
- `certificates/effective_error_checks.json`: exact rational inequalities proving the stated boundary constants M2=1000, M3=3900, M4=170000 within the manuscript's analytic proof, and the explicit envelope start x=50
- `certificates/decimal_diagnostics.json`: original standard-library Decimal approximations, dominant-term/exact ratios, and the permanent-two cycle-size probabilities; not interval-certified
- `certificates/precomputed_audit_checks.json`: mandatory exact consistency checks against the supplied independent C++ TSV data; this does not itself rerun C++

The all-n remainder bound requires the manuscript's analytic proof in addition to the checked rational inequalities. Finite numerical comparisons alone do not prove an all-n assertion. No certified numerical inverse solver is included.

## Optional independent exhaustive checks

The unchanged original C++ programs and their byte-preserved TSV outputs are in `optional/`. They were rerun for preparation of this package and agreed exactly with the supplied output. The ordinary builder does **not** repeat this exhaustive enumeration. To do so explicitly:

```sh
python3 -B reproduce.py --optional-cpp
```

This requires `g++` with C++17 support and compiles with assertions enabled. The full-matrix audit enumerates all binary matrices through n=5, including 33,554,432 matrices at n=5; the block audit checks all 16,774 matching normalizations for diagonal-one graphs through n=4 and block counts for k<=4 through n=5. These checks are supplemental, not assumptions of the proof.

See [README_REPRODUCIBILITY.md](README_REPRODUCIBILITY.md) for the full inventory, arithmetic, guard coverage, isolation rules, and reproducibility limits.
