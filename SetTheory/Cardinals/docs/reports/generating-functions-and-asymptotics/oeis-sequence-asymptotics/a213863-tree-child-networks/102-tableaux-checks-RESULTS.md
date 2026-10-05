# Recorded verification results

Recorded suite status: **PASS**

- Software: Python 3.12.14, SymPy 1.14.0
- Ordinary interpreter: all four sections passed; 4,999 explicit gates
- Optimized interpreter (`python -O`): all four sections passed; 4,999 explicit gates
- Deliberate corruption: all 22 cases rejected in both modes, for 44 verified rejections
- Suite elapsed time: 135.86 seconds

## Checked extent

- 560 adjacent-entry identities for the defining integer recurrence
- 288 rotated one-step entries
- 1,632 two-step matrix entries over startup n = 1 through 16
- Exact symmetrizer, Jacobi squares, square-bidiagonal factor, boundary conventions, and inter-time ratios
- General rational identities and Airy coefficient expansions through epsilon cubed
- 20 polynomial-pair recurrence coefficients, with boundary/gauge and grading checks
- All six logarithmic and six nonconstant multiplicative corrections through n^(-2)
- Endpoint ratio through n^(-3), by two independent conversion routes

## Integrity and reproducibility

Verifier SHA-256: `1e43eb5720222224a797b219980fc271b5879e03f08fe3d2835f93968a0da2fc`

Harness SHA-256: `04b023f483e9d4524c8dff59d2128103c5ef6ae34d6897799a4aa374f4967ba5`

Input-manifest SHA-256: `9141b2f15155ee981984fd34c11c5082b568391ae09c29e94be07b2518868c99`

The manifest lists the exact five local input snapshots. The suite JSON records every corruption, its selected section, expected and observed rejection reasons, return code, and interpreter mode. Semantic-data corruption tests refresh only their temporary copies' input hashes, ensuring that the algebra checks themselves are exercised. Code-formula corruptions separately test the finite matrix checks. JSON/schema, grading, coverage, and provenance failures are also exercised.

These results are finite algebra certificates. The analytic theorem and all-depth error control require the accompanying mathematical proof; neither a rigorous amplitude enclosure nor convergence of the infinite formal series is certified here.
