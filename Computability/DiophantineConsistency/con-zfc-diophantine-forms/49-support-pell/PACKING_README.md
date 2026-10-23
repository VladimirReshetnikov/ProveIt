# Support-separated quadratic consistency encodings

Reviewed ProveIt commit: `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

This module supplies a support-sensitive replacement for the full Sidon
position code in current wave-6 constructions. It preserves the complete
package-31 native coefficient tuple and the inherited arithmetic finalizers.

| Domain | Unknowns | Exact total degree | Live binary operations |
|---|---:|---:|---:|
| Strictly positive integers | 9 | **32,568,568** | **652** |
| Nonnegative integers | 9 | **32,568,568** | **655** |
| Unrestricted integers | 10 | **59,564,744** | **653** |

The current wave-6 comparison points are package45's 9-positive
129,875,980/788 and package40's 10-integer 237,520,456/782. The improvement
is approximately fourfold in degree on each matching domain. This does
not lower the number of variables or establish a global minimum.

## Mathematical contribution

Only 71 of the 528 padded quadratic monomials occur in the source rows.
Each of those 71 must have a sum represented uniquely among **all** 528
pairs. The other pairs can collide. The explicit labels have maximum 200,
where the full Sidon labels had maximum 799. There are 285 distinct pair
sums and 130 collided sum positions; all 71 active sums remain isolated.

The reversed coefficient kernels still recover every quadratic residual
exactly. Coefficients away from the target cells obey the same bound,
because the square polynomial has nonnegative coefficients whose sum is
unchanged. All this is proved in `SPARSE_PACKING_PROOF.md`, which also
gives the complete nine-variable source, ratio bridge and finalizer.

The ordinary consistency equivalence uses the inherited native-compiler,
machine calibration and arithmetic contracts stated in that proof.
The ten-integer companion additionally uses Sun's external reduction.
There is no new end-to-end Lean/Rocq certificate or proof of consistency.

## Canonical artifacts

- `nine/generated/multitarget_nine_positive.json`: primary nine-positive polynomial.
- `nine/generated/multitarget_nine_natural.json`: corresponding nine-natural polynomial.
- `data/polynomial.json`: primary ten-integer polynomial.
- `data/weights.json`, `quartic/QUADRATIC_TARGETS.json`, `data/coefficient_recipes.json`: exact source definitions.
- `fixed/FIXED_LEAVES.json` and payloads: actual fixed integer leaves, with signed encodings and hashes.
- `coefficients/`: coherent whole native tuple, generator, proofs and inherited notices.
- `certificates/sparse_extraction.json`: exact finite audit receipt.
- `upstream/`: clearly marked, unchanged historical proofs and parent data.

The larger `*_degree_certificate.json` nine-variable circuits are equal-
polynomial certificates, not the primary operation-count claims.

## Reproduce

Only Python3's standard library is needed:

```sh
python3 verify.py
python3 -O verify.py
python3 code/audit_full_circuit.py
```

Rebuild generated data with:

```sh
python3 code/build.py
python3 nine/build_multitarget_nine.py
python3 materialize.py
python3 verify.py
```

The verifier compares exact symbolic coefficients for all 44 target
identities while keeping the four native ports independent. It also
checks both parent circuits, hashes of the actual fixed ports, complete
DAG liveness, operation counts, coefficient bounds, exact norm identities,
and exact degree certificates. Modular replay checks supplement the
proofs; they are not used as a substitute for a polynomial identity proof.

New material is AI-assisted work prepared for Vladimir Reshetnikov's
ProveIt project. No external human review, literature-priority theorem,
global minimality theorem, or decision of consistency is asserted.
Inherited attribution and licenses remain in `upstream/` and `coefficients/`.
