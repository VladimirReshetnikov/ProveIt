# Concrete nine-variable compiler

This directory provides an ordinary polynomial in exactly nine natural
unknowns. It explicitly specializes the Jones construction to the supplied
32-variable normalized quartic. No recursively enumerable index remains
uninstantiated: every constant has a bounded coefficient recipe.

The primary variant uses unconditional Pell square-root majorants and has
exact degree `161844*5^33+484` and 20,531 binary arithmetic operations.
The comparison variant retains the literal weights from the Lean source.
The parent native/Pell compiler and the K215 calibration remain mathematical
dependencies; the checks here are not a new proof-assistant endpoint.

Reproduce from the package root, with Python 3.10 or later and its standard library:

```
python3 nine/nine_compressor.py base/quartic32.upstream.json nine/generated
python3 nine/check_nine.py base/quartic32.upstream.json nine/generated
```

The generator emits `constants.json`, `index_bound_s.json`, the shifted
quartic, and two fully expanded binary arithmetic DAGs. The check program
emits `nine_checks.json`. It rejects check failures using explicit
exceptions, so validation is not disabled by Python's optimization flag.

The constant recipe uses the selected complete tuple of the four compiler
ports `beta,K0,MC,MF`; these are fixed nonnegative integers and never
existential unknowns. This release binds the whole T4 tuple in
`../COEFFICIENT_BINDINGS.json`. The polynomial DAG only uses 9 unknown leaves.
All 348 named fixed leaves are defined by the coefficient/index recipes.

`evaluate_dag(body,fixed,variables,modulus)` evaluates residues without
materializing the enormous coefficients. Such evaluations are arithmetic
diagnostics, not a search for a consistency witness.

The TeX fragment gives every formula, the self-contained two-radical
finalizer proof, the unconditional majorant lemma, and the bridge to the
existing normalized-quartic and K215 theorems.

From the package root, verify the actual fixed coefficient instance with:

```
python3 nine/verify_fixed_instance.py --package-root . --generated nine/generated --output verification/nine_fixed_instance.json
```

Adjust `--generated` to the folder containing `constants.json` and the
two arithmetic DAGs. The verifier loads the supplied T4 coefficient module
and finite window data, compares the independently generated coefficient
polynomials and index bound, and evaluates actual instance residues.
Its three odd primes, four input tuples and two weight variants yield 24
output comparisons and 840 named intermediate-node comparisons. The
literal digit-polynomial sum has 66,045 terms; the geometric sum is evaluated
logarithmically without division. Receipt input labels are independent of
the absolute package location.
