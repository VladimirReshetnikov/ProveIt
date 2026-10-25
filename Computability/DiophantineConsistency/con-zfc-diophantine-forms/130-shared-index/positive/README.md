# Ten-positive quotient charts

The principal file is **`quotient_absorbed.json`**: one fixed integer
polynomial in ten strictly positive inputs, evaluated by 86 binary
arithmetic operations, with exact total degree 466. Its lack of positive
zeros is equivalent in ZFC to syntactic `Con(ZFC)`, by the ordinary proof
in `PROOF.md` composed with the explicitly pinned inherited calibration.

| Equation | Operations | Exact degree | Purpose |
|---|---:|---:|---|
| `quotient_absorbed.json` | 86 | 466 | Principal operation-count improvement |
| `quotient.json` | 87 | 466 | Positive-zero bijection control |
| `quotient_absorbed_sharp.json` | 89 | 450 | Sharp-center algebraic control |
| `quotient_sharp.json` | 90 | 450 | Sharp-center bijection control |

Each JSON file is a complete arithmetic schedule: its ten witnesses are
`J,F,alpha,i,T,w,s,n,eta,zeta`, and the output register `N` is set equal
to zero. Intermediate registers are polynomial abbreviations and are
not additional quantified variables. All four fixed coefficients belong
to the **whole original compact44 tuple** in `coefficients/`.

## What changed

The old theorem forces `q^3|Y` at every positive zero. Define `Y=q^3s`,
remove the resulting common denominator from the carrier, and divide the
full norm by its exact common factor `q^12`. This produces the
87-operation control with a positive-zero bijection. Absorbing the
integer `s` into the positive padding coordinate saves one more
operation. The 86-operation proof supplies its own sign argument and
canonical completeness; it does **not** claim that `n-s` is positive
at every new zero.

Relative to the inspected 89-operation, degree-288 parent, the principal
equation saves three operations and increases degree. The sharp charts
are retained as controls and are not new Pareto records.

## Verify without changing the packet

From this directory:

```text
python3 -B verify.py
python3 -B -O verify.py
```

To save a receipt at a path you choose:

```text
python3 -B verify.py --output /tmp/positive-verification.json
```

The verifier uses only the Python standard library. It imports the
builder and finite coefficient recipe without invoking their writing
entry points. It writes no file or bytecode cache unless `--output` is
explicitly supplied. The normal and optimized Python modes use the same
explicit checks; correctness does not rely on `assert` statements.

The checks cover all four circuits, exact carrier/finalizer identities,
192 full formula controls, eight degree rays, operation counts and
liveness, three planted mutations, and reconstruction of every byte of
the four fixed coefficients. The coefficient recipe reads a finite K215
transition table to reconstruct the inherited tuple; it does not run the
machine. These are syntax/arithmetic verification checks, not a proof of
consistency or a replacement for the unbounded proof.

## Rebuild the equation files

```text
python3 -B build.py
```

This command intentionally rewrites the four JSON graphs from their
pinned parents. The verifier also calls the pure in-memory builder and
requires exact object equality with every supplied graph.

## Coefficients and proof dependencies

`coefficients/BINDING.json` names each gzip file, its raw and compressed
SHA-256 hashes and its bit length. The compressed bytes store unsigned
little-endian integers. `MF` is already shifted and must not be shifted
again. `coefficients/recipe/build_coefficients.py` and its literal seed
provide the finite reconstruction; the verifier performs that
reconstruction in memory and compares every byte.

The parent polynomial and ordinary proof are under
`inherited/gap_fusion/`. Additional fusion, saturation, coefficient and
source61 explanations are under `inherited/`. The source snapshot is
ProveIt commit `f4d8db99e060339f3306a04d507c35bc1d0d68c5`, with further
provenance recorded in the enclosing packet's `SOURCE_SNAPSHOT.json`.

The result is an ordinary arithmetic equivalence formalizable in ZFC.
It does not add an end-to-end Lean, Rocq, or object-language ZFC proof
certificate, and it makes no claim of global minimality.
