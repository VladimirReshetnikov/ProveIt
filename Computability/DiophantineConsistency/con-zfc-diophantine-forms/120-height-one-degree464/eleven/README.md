# Eleven-variable Diophantine consistency equation at degree 464

`PROOF.md` gives the complete ordinary arithmetic reduction and its exact
inherited calibration boundary. `powered_coprime11_aux.json` is the selected
literal integer polynomial; all six fixed coefficient payloads and their
finite construction recipe are included.

| Equation | Domain | Unknowns | Exact degree | Live binary operations |
| --- | --- | ---: | ---: | ---: |
| `powered_coprime11_aux.json` | Unrestricted integers | 11 | 464 | 122 |
| `powered_coprime11_direct.json` | Unrestricted integers | 11 | 488 | 121 |

This improves the immediate incoming selective-coprime parents 11/688/126
and 11/728/122, with the same complete six-integer coefficient tuple. It
combines their coprime guard with the separately incoming powered carrier
and supported-modulus interpolation, and adds a smaller parity guard and
an evaluator sharing the auxiliary center. It does not claim the globally
simplest Diophantine equation.

The variable order is `j,C,z,h,r,v,w,T,c,n,s`. Uppercase `C` and lowercase
`c` are distinct. All other names are polynomial abbreviations. The six
coefficient ports are fixed numerals, not extra unknowns; `MF` is already
shifted and must not be replaced with an unshifted payload.

## Reproduce

Python 3.10 or later and its standard library suffice. From this directory:

    python3 build.py
    python3 check.py
    python3 -O check.py

`build.py` rewrites the two literal graphs and metric table. `check.py`
independently transcribes all mathematical register identities, checks every
live gate, multiplies all eight formal norm conjugates, proves the center
identity, authenticates and fully reconstructs all fixed coefficients,
verifies source hashes and exact degree coefficients, and compares the
regenerated artifact bytes. Normal and optimized receipts are included.

The selected graph has naive syntactic degree bound 488; its exact degree
is 464 because of the explicitly proved center cancellation. The proof
does not use finite samples as evidence of the unbounded semantic theorem.

## Files

- `PROOF.md`: complete new arithmetic proof, including soundness order,
  completeness order, exact degrees, costs, and further questions.
- `coefficients/`: complete fixed tuple, hashes, and finite recipe.
- `source/`: credited ordinary proof dependencies and formalization boundary.
- `SOURCE_PINS.json`: inspected commit, incoming archive hashes, and retained
  source-file hashes.
- `build.py`, `circuit.py`: literal arithmetic graph constructor.
- `check.py`, `exact_polynomial.py`: exact independent formula and size checks.
- `CHECK.json`, `CHECK_OPTIMIZED.json`: finite replay receipts.
- `licenses/`, `NOTICE.md`: retained source notices and attribution.

The consistency equivalence uses the named ordinary native/compiler and
finite-refutation calibration theorems. This component does not supply a
new Lean/Rocq kernel certificate or a sealed object-language ZFC derivation.
It proves neither consistency nor inconsistency.
