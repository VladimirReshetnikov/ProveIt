# Nine-variable equations with normalized radix positions

This component contributes three explicit polynomials in nine **strictly positive** integers. No intermediate circuit register is an extra unknown.

| Equation | Exact degree | Live binary operations | Coherent coefficient tuple |
|---|---:|---:|---|
| `equations/boundary_simple.json` | 1,472,168 | 420 | original31 |
| `equations/boundary_complete.json` | 997,810 | 1,057 | original31 |
| `equations/compact_simple.json` | 1,626,248 | 428 | compact54-sharp |

All additions, subtractions and multiplications on variable-dependent values are charged, including squares and multiplication by numerals. Fixed integer leaves and reuse are free in this convention. The whole coefficient tuples and every live fixed leaf are materialized. Literal finite reconstruction recipes are included. These are mathematical description/circuit measures, not runtime or bit-complexity claims.

## Mathematical contribution

Translate every source weight down by one and every extraction target down by two. Replace each degree-d kernel exponent e by e+d-2. These exponents remain nonnegative, all coefficient-extraction identities are preserved, and the convolution height drops by two. The first coordinate may now occupy radix position zero. Its validity is proved by the mask argument and checked against the precise positive Jones ratio interface: neither `ratio_sound` nor `ratio_complete` assumes b divides g or R+1.

For original31 this gives W=115, H=1866, L=2b B^1983, N=2^16012032 B^1053, and cap=b B^115. For compact54 use H=2080, L=b B^2197, N=2^6480184 B^1160. Recalibrating the population count is essential.

The source normalization is an existence equivalence, not a same-witness identity with the predecessor polynomial. After normalization, a common addition chain evaluates all required powers of B; both digit masks use sums of shared powers and the kernels use Horner form. This second step is a polynomial identity.

`report_section.tex` contains the complete new argument, explicit registers for the equations, ordinary semantic dependencies, exact degree proofs, storage comparisons and further questions. The inherited saturation and majorant proofs are retained under `inherited/`. The fixed comparison snapshot and archive hashes are in `SOURCE_PINS.json`.

## Reproduction

Python's standard library suffices. From this directory:

```sh
python3 build.py
python3 verify.py
python3 exact_audit.py
python3 verify_coefficients.py
python3 normalization_check.py
```

- `build.py` regenerates the three DAGs and all fixed leaves from the supplied coefficient ports. It tries four mask evaluation choices and, for the complete radical, 24 Horner variable orders. Those finite choices do not claim globally shortest circuits.
- `verify.py` imports no builder and checks 54 or 55 exact polynomial identities per graph. It also checks fixed-leaf values, topology, liveness, the nine-variable set, and independent operation counts. This is an exact composition check, not just modular testing.
- `exact_audit.py` uses a separate sparse-polynomial implementation to verify all source coefficient identities including absent monomials, actual coefficient bounds, binary calibration exponents, the full 36,309-term positive radical certificate, and the cancellation-resolved degree 997,810.
- `verify_coefficients.py` reconstructs all eight native port integers from the retained original31 machine/tile recipe and the compact54 fixed seed, comparing complete byte strings. It does not infer compiler semantics from those finite comparisons.
- `normalization_check.py` checks both translated layouts against their unchanged predecessor tables and proves the exact finite exponent substitutions.

Normal and optimized Python runs retain explicit exceptions; checks do not depend on `assert`.

## Comparison and scope

The immediate inherited original31 simple and complete forms used 449 and 1,086 operations, at degrees 1,474,688 and 999,518. The compact predecessor used 434 operations at degree 1,628,768. The changes improve these respective entries in both measures. The original31 four native ports occupy 533,099 raw bytes; compact54 uses 215,492. The twelve original31 live fixed leaves occupy 4,001,391 raw bytes versus 1,565,018 for eleven compact leaves, so compact54 retains a coefficient-size advantage.

The ordinary mathematical conclusion composes with the retained source/compiler and machine/refutation calibration: ZFC proves that the stated positive-domain equation has no solution if and only if Con(ZFC). This packet supplies the new ordinary reduction and finite exact algebra certificates; it does not supply a newly exported internal-ZFC derivation or end-to-end Lean/Rocq proof. There is no claim of global minimality, fewer than nine unknowns, historical priority, or a proof that ZFC is consistent.
