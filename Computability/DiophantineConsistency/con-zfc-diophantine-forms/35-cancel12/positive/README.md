# Twelve-positive-variable equations and systems

These six circuits use exactly twelve **strictly positive integer** variables:

`J, F, alpha, z, h, i, T, s, w, eta, zeta, t`.

The other named values are polynomial abbreviations, not further unknowns.
The full definitions, correctness proof, and exact-degree arguments are in
`../sections/positive.tex` and the compiled report.

| Circuit | Equations | Exact degree / maximum residual degree | Binary operations |
|---|---:|---:|---:|
| `economical_product.json` | 1 | 1081 | 108 |
| `economical_system.json` | 3 | 1072 | 104 |
| `economical_shifted_system.json` | 3 | 1072 | 103 |
| `cancellation1065_product.json` | 1 | 1065 | 118 |
| `cancellation1065_system.json` | 3 | 1056 | 114 |
| `cancellation1065_shifted_system.json` | 3 | 1056 | 113 |

## Circuit encoding

Each JSON `source` is an ordered list of rows
`[output_name, operator, left_operand, right_operand]`, with operator `+`,
`-`, or `*`. An operand is either an integer literal, a supplied variable,
a fixed coefficient port, or a previously defined output name. Process rows
in order. The product circuit imposes `output = 0`; a system imposes equality
for every pair in `comparisons`. Shared intermediate values are computed once.

Every binary arithmetic row is charged, including multiplication by a fixed
numeral. System comparisons are free under the repository's counting convention.
No radical, division, variable exponent, or implicit quantified intermediate
is present in these circuits.

The shifted systems use `z_old = z + 1`; their existence is equivalent to
that of the unshifted systems over the positive integers. The report proves
positivity of this shift from the restored canonical compiler witness.
The product equations retain the unshifted transport coordinate.

## Complete fixed coefficient binding

Use the **entire tuple** in `../coefficients/COEFFICIENT_BINDING.json`.
The four circuit ports map to minimal unsigned little-endian payloads in
the same coefficients directory:

| Port | Payload | Meaning |
|---|---|---|
| `beta` | `beta.bin` | `B - 1` |
| `K0` | `K.bin` | Complete transport coefficient |
| `MC` | `MC.bin` | Native low mask |
| `MF` | `MF_source.bin` | Shifted high mask, `MF_native + B - 1` |

If only the gzip form is present, decompress it before decoding. For raw
payloads use `int.from_bytes(path.read_bytes(), 'little')`. The binding fixes
all four coefficients, their recipes, and hashes. They are not unknowns.
Do not combine ports from different compiler layouts. The theorem depends
on the whole-tuple compiler proof, not merely on congruence or byte checks.

At the same four port values, the economical circuit evaluates exactly
package 30's polynomial using fewer operations. Rebinding to this release's
new tuple produces a different fixed polynomial through the same proved
interface. The cancellation circuit additionally changes the carrier and
has the smaller exact degree proved in the report.

## Offline reproduction

From this directory, with Python 3 and its standard library:

```sh
python3 -B build_new.py
python3 -B check_new.py
```

The first command regenerates the six retained JSON circuits. The second
compares the norms with an independent multiquadratic conjugate-product
implementation on signed assignments, checks parity and transport shifts,
checks all gate dependencies and liveness, and computes complete univariate
polynomial coefficient lists over two primes to verify the predicted degrees
and leading forms. It writes `CHECK_RESULTS.json`.

Those checks establish finite arithmetic properties. The mathematical proof
supplies unbounded soundness and completeness and explicitly inherits the
native compiler and K215 syntactic-refutation calibration. The release does
not claim to decide Con(ZFC) or to provide a new end-to-end Lean/Rocq proof.
