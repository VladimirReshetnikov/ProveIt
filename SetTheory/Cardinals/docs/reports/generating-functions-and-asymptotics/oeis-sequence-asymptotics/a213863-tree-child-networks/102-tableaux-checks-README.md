# Exact verification of the A213863 / tree-child formulas

This directory is a self-contained, reproducible **finite algebra verification package** for the accompanying mathematical report. It uses exact integers, rational numbers, and symbolic polynomial identities. It neither estimates the amplitude numerically nor replaces the analytic proof of its existence or the all-orders remainder bounds.

## Run

Requirements: Python 3.10 or newer and SymPy 1.14.0 (the recorded runs use Python 3.12.14). The Python standard library supplies everything else. No network access, external file paths, numerical eigenvalue solver, or large dynamic program is used.

From this directory:

```sh
python run_checks.py > results/suite.log 2>&1
```

That command performs the complete verification in ordinary Python and again with `python -O`, then makes temporary local copies and deliberately corrupts their inputs or formulas. Every corruption must be rejected in both interpreter modes for the suite to succeed. Temporary copies are removed automatically.

For an individual full verification:

```sh
python verify_exact.py --output results/manual.json
python -O verify_exact.py --output results/manual_optimized.json
```

Exit status zero means every selected check passed. A nonzero status means a failure. Do not infer success from a partial log. `--section finite`, `symbolic`, `formal`, or `endpoint` selects a smaller diagnostic subset; only the default `all` checks the complete package.

## What is checked

1. **Defining recurrence and startup.** Direct integer prefix sums build the triangular array
   \(b(n,m)=(2n+m-2)\sum_{j\le m}b(n-1,j)\), with \(b(1,1)=1\). The checks cover 560 adjacent-entry identities, 288 rotated one-step identities, and 1,632 entries of the exact two-step operators for \(1\le n\le16\). Every coordinate of the propagated vector is compared to the direct array. Original rows through 33 suffice. The initial state, forbidden predecessors, exceptional first row, moving upper endpoint, and the exact factor \(3n+1\) are included.
2. **Jacobi and positive factor.** Exact rational comparisons check the rising-factorial symmetrizer, its edge ratios, the Jacobi off-diagonal squares, and the diagonal and off-diagonal identities for \(J_n=C_nC_n^T\). Positivity removes any ambiguity about square-root signs. The full terminal diagonal is checked explicitly: its extra term multiplies the zero-extended new coordinate. The inter-time symmetrizer ratios and corrected entrywise domination are checked over startup.
3. **General symbolic identities.** Rational identities independently eliminate the one-step recurrence; verify the Jacobi square factor, edge monotonicity derivatives, the contraction argument's polynomial numerator, and the potential identity; and replay the Airy-scale coefficient expansions through order \(\varepsilon^3\). The leading triangular operator is checked on monomials of degrees 0 through 18. These are symbolic algebra statements, not proofs of analytic asymptotic bounds.
4. **Formal polynomial–Airy pairs.** Every saved profile's exact boundary value, derivative gauge, and modulo-three grading is checked. An implementation independent of the supplied derivation scripts composes the profile polynomials at the shifted coordinate and Taylor-expands only the Airy basis. Both pair components of the formal recurrence vanish coefficient by coefficient through \(t^9\), giving 20 exact coefficient identities. Profiles 0 through 7 and scalar coefficients 0 through 9 are covered.
5. **Endpoint and scalar conversion.** The canonical endpoint Taylor series is reconstructed from derivative pairs. The scalar-carrier logarithmic difference is checked through \(t^9\); all six supplied logarithmic corrections and all six nonconstant multiplicative corrections are checked through \(n^{-2}\). The ratio \(a_n/(12n a_{n-1})\) is reconstructed through \(n^{-3}\) in two ways: directly from the exact two-step endpoint formula and from the canonical logarithmic expansion. The exact factor \((3n-2)/(3n+1)\) is retained.

## Interpretation and limits

- The checker does not import `derive_tree.py`, `endpoint_tree.py`, or `verify_tree_formal.py`; these are coefficient-generation reference snapshots only
- Exact arithmetic does not turn finite tests into an all-depth induction or a proof of uniform analytic estimates
- No floating-point fit, numerical amplitude enclosure, transseries claim, or assertion about convergence of the formal infinite series is made
- The coefficient tables concern A213863 and the exactly related maximal-reticulation count; they do not supply an all-orders expansion for the total tree-child count
- All verification gates use explicit exceptions; no `assert` statement can disappear under optimization
- The input manifest detects changed input bytes. It is an integrity inventory, not a cryptographic signature or protection against someone deliberately rewriting both code and manifest

## Files and provenance

- `verify_exact.py`: independent exact verifier
- `run_checks.py`: ordinary/optimized replay and deliberate-corruption harness
- `inputs/formal_9.json`: polynomial profiles and scalar series through the saved order
- `inputs/endpoint_9.json`: endpoint, carrier, logarithmic, multiplicative, and ratio coefficient tables
- Other `inputs/*.py`: reference derivation/replay snapshots; not executed by the verification suite
- `input_manifest.json`: SHA-256 values of every required local input
- `provenance.json`: primary-source link and the coefficient, script, and validation inventories
- `results/normal.json`, `results/optimized.json`: complete baseline results, software versions, exact check coverage, input hashes, and verifier hash
- `results/suite.json`: baseline and corruption outcomes, including expected and observed rejection reasons and code hashes
- `results/*.log`: readable transcripts from the final suite

The defining recurrence and the initial values \(1,1,7,106,2575,87595,3864040,210455470\) agree with the primary [OEIS A213863 entry](https://oeis.org/A213863), accessed 2026-10-02. Mathematical conventions and analytic conclusions should be read in the accompanying report. The checked software versions and actual run times are recorded in the result JSON, rather than inferred from document dates.
