# A 62-operation quadratic system and a 127-operation quartic

This component improves the low-degree presentation in ProveIt's frozen
`30-quartic31` package. It retains **31 positive integer unknowns and
22 quadratic equations**, reduces the shared arithmetic circuit from
65 to **62 binary operations**, and reduces the corresponding quartic
sum-of-squares circuit from 130 to **127 operations**. Three invertible
changes of positive coordinates produce the improvement.

Together with the inherited compiler and K215 calibration theorems, the
system has no positive integer solution if and only if `Con(ZFC)`, with
the equivalence provable in ZFC. The proof, including the positivity
dependency of the transport-coordinate shift, is in
`QUARTIC31_62_PROOF.md`. This is an ordinary mathematical proof with exact
finite algebra checks; it is not an end-to-end formal proof certificate.
No global optimality is claimed.

## Reproduce

From this directory run:

```sh
python3 build_quartic31_62.py
```

The script uses only the Python standard library. It resolves all paths
relative to itself, so it can also be called from another directory.
It reads the supplied frozen literal JSON and executes no upstream code.
It regenerates the following files and raises an error if an exact
algebra or circuit check fails:

| File | Contents |
| --- | --- |
| `quartic31_system62.json` | The 31 variables, four coefficient ports, 22 residuals, and 62-gate comparison circuit |
| `quartic31_sos127.json` | The quartic sum of squares, its exact sparse expansion, and 127-gate circuit |
| `QUARTIC31_62_AUDIT.json` | Degree, operation, liveness, normalization, and predecessor-identity checks |

The 62 operations comprise 33 multiplications and 29 additions or
subtractions. Multiplication by fixed numerals is charged; comparisons
and reuse of already-computed values are free. The quartic has 297
monomials when the four coefficient ports are kept as separate formal
symbols. This convention measures the arithmetic presentation; it does
not charge for writing out the fixed integer coefficients.

## Coefficient binding

The circuit ports are `beta,K0,MC,MF`. They must be bound together to a
single authenticated blank-input compiler tuple. For the new tuple in
this archive, the binding to the files in `../coefficients/` is:

| Circuit port | Integer file |
| --- | --- |
| `beta` | `beta.bin` |
| `K0` | `K.bin` |
| `MC` | `MC.bin` |
| `MF` | `MF_source.bin` |

The files encode unsigned integers in little-endian byte order, as
documented by the coefficient generator. In particular, `MF` uses the
shifted source mask `MF_source = MF_native + B - 1`. The full compiler
proof for this new tuple belongs to the coefficient component. The
quartic transformation also applies to the complete predecessor tuple.

## Source provenance and scope of checks

`SOURCE_PINS.json` records the frozen repository commit, upstream paths,
SHA-256 digests, and Git blob identifiers. The `upstream/` directory
contains the literal predecessor polynomial and the two inherited proof
documents needed to review the three coordinate shifts. The generator
checks all 22 residual identities against both the predecessor's
expressions and its literal sparse polynomial data. It also checks all
circuit outputs exactly, proves the quartic degree by its `tau^4`
coefficient, and verifies the all-one normalization used when shifting
the witnesses to nonnegative integers.

These finite checks establish the new algebraic transformation. They do
not replace the inherited Pell, compiler, Wang-table, or K215 calibration
theorems. The separate independent coefficient audit and mathematical
reviews are in `../reviews/`.
