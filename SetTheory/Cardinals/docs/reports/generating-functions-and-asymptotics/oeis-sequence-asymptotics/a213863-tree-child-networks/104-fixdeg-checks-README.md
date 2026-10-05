# Exact algebra and reproducibility checks

This directory is the sole executable check package for the accompanying fixed-d tree-child amplitude report. It uses exact integers, fractions and symbolic algebra. It contains no numerical estimates of the limiting amplitudes and no downloaded research papers.

## Run

Requirements: Python 3.10 or later and SymPy 1.14.0. The recorded run uses Python 3.12.14.

    python -m pip install -r requirements.txt
    python run_checks.py

The suite runs the verifier normally and with Python's `-O` option, and then runs every deliberate-corruption test in both modes. It exits nonzero on a failed baseline, an accepted corrupted input, an unexpected exception, a wrong rejection reason, an incomplete check set, or a changed input during the run. Its machine-readable result is `results/suite.json`.

Individual checks can be replayed with:

    python verify_exact.py --section all --output results/manual.json
    python -O verify_exact.py --section all --output results/manual_optimized.json

The available sections are `finite`, `formal`, `endpoint`, `ternary`, and `all`. Each invocation validates the complete input schema and SHA-256 manifest before running the selected mathematics. There are no assertion-based correctness gates that disappear under optimization.

## Mathematical coverage

1. **Original recurrence and exact startup.** Recompute the integer prefix-sum recurrence for every integer d from 2 through 12. Compare c(0),...,c(6) with the declared reference values. Verify the exact shifted normalization, including y(0,0)=y(2,0)=1, the one-step recurrence through N=18, and the two-step recurrence through n=9. These include 594 two-step coordinates and both boundaries.
2. **Jacobi algebra and gauge.** Check the telescoping identity, full terminal diagonal, positive bidiagonal Gram-factor identities, symmetrizer factorization and finite inter-time contraction ratios. At d=6 and d=10, n=1000, exhibit the original factorial gauge's R(1)>1 obstruction exactly and verify that the repaired gauge has R(1)<1. Four generic symbolic denominator-deficit and derivative identities support the report's global factorwise monotonicity proof.
3. **Universal formal coefficients.** Validate four polynomial-Airy profiles and six scalar coefficients by substitution into the complete formal recurrence through degree five in t. This is a direct residual check, not a repeat of the triangular system used to generate the coefficients. Independently expand the exact finite-product weights for d=2,3,4,6,10 and compare them with the generic weight expansion. Boundary values and derivative gauges are checked explicitly.
4. **Universal first and second corrections.** Check the scalar carrier difference equation, the canonical endpoint conversion, both explicit coefficients, the word and network polynomial exponents, and the second binary-correction specialization. Here q=((d-1)/(d+1))^(1/3), `al` is the largest Airy zero, and `k` is the scaled Airy parameter kappa.
5. **Additional ternary coefficients.** Independently verify five finite-d profiles and seven scalars through degree six. Reconstruct the local Airy solution from its differential equation, substitute it into the finite profiles, check the carrier through degree six, and include the exact gamma-product normalizer. This yields the logarithmic word corrections

       L1 = al^2/(36*2^(1/3))
       L2 = 11*al/(108*2^(2/3))
       L3 = al^3/243 - 3/16

   in powers n^(-1/3), n^(-2/3), n^(-1). The exact normalizer contributes -7/(32n). Omitting it changes the third coefficient and is detected by a deliberate-corruption test.

## Input format and fail-closed behavior

`input_manifest.json` fixes the exact input file set and SHA-256 digests. Each JSON object has an exact permitted key set, version, array length and variable set. Unknown fields, missing fields, duplicate keys, nonfinite JSON constants, booleans in integer schema fields, shortened profiles, malformed expressions and unexpected files are rejected. Expressions use a small AST-parsed arithmetic language of integer literals, declared symbols, arithmetic and bounded integer powers. The parser does not evaluate arbitrary strings or accept function calls.

The suite tests 25 distinct deliberate corruptions, each in normal and optimized Python: integrity damage, schema changes, unsafe syntax, truncated coverage, a wrong reference count, altered Gram and symmetrizer identities, a false gauge-obstruction assertion, boundary/gauge/interior profile changes, scalar and carrier changes, both universal endpoint corrections, and the ternary degree-six scalar, carrier, gamma normalizer and cubic logarithmic correction. Algebraic corruption tests refresh the digest in their temporary copy so that the mathematical check, rather than just the hash check, must detect the error. The original files are never modified.

## What these checks do not prove

Finite exact checks do not establish the asymptotic statement for every n or every fixed d. The report supplies the global positive-product, spectral-gap, localization, smoothing, amplitude-positivity and all-orders transfer arguments. These scripts verify algebraic inputs and finite regression cases used by that proof. They do not certify a numerical amplitude, prove uniformity as d tends to infinity, or establish an all-orders expansion for total network counts. The source-derived ternary total/maximal rate is a combinatorial proof consequence, not a numeric test in this package.

## Files

- `verify_exact.py`: direct exact verifier, independent of the coefficient-generation program
- `run_checks.py`: normal/-O replay and deliberate-corruption runner
- `inputs/formal_coefficients.json`: universal profiles, scalars, carriers and first two endpoint coefficients
- `inputs/ternary_degree6.json`: additional exact ternary certificate
- `inputs/reference_sequences.json`: finite integer regression values
- `input_manifest.json`: exact integrity inventory
- `provenance.json`: source and input descriptions
- `results/`: machine-readable results and replay logs

The mathematical certificates, verification source, requirements, documentation and result records make up the complete check package.
