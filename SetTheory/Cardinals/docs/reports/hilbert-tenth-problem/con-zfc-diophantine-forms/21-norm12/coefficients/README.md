# Smaller fixed coefficients for the K215 consistency equations

This directory supplies a complete four-coefficient recipe for the existing
inputless Diophantine arithmetic backends. It reduces the local alphabet
from 37,075 to 5,280 tiles and changes the base from `2^(5^18)` to
`2^(5^15)`. The bit length of `beta=B-1` is exactly 125 times smaller.

## Reproduce

Run from this directory with Python 3 (standard library only):

```sh
python check_reduced.py
```

This verifies the exact bytes of the included literal K215 table and its
transition JSON, parses the table and compares every one of its 430 actions
with the JSON, exhaustively generates the stricter tile alphabet, checks all
1,319 convolution targets and the all-rotation support conditions, verifies
the mask populations, carry bounds and coefficient residue modulo five,
and checks 1,143 helical windows of two halting control machines.

The enumeration considers all 46,980 horizontal triples satisfying the
one-head rule, filters them by the symmetric row guard to 13,465, and tests
all 439 successors for those triples: 5,911,135 quadruples. It does not
enumerate all `439^4` quadruples; excluded triples fail a required guard.

The command regenerates:

- `reduced_t4_windows.json`: the complete ordered alphabet;
- `reduced_t4_receipt.json`: the finite verification receipt;
- `COEFFICIENTS.json`: the exact four bounded finite-sum recipes, scalar
  constants, source bindings and compiler invariants.

`REDUCED_T4_PROOF.md` gives the mathematical adapter proof. The alphabet
filter lives in `explore_t4.py`; `check_t4.py` is the inspected upstream
37,075-tile predicate and is included as a dependency. Its main entry point
is not invoked by the new checker.

## Scope

The finite checker does not establish the universal Pell/compiler theorems,
decide K215 halting, or constitute an end-to-end Lean/Rocq proof. Those
mathematical dependencies are explicitly retained in the adapter proof.
The internal equivalence to `Con(ZFC)` follows by composing this adapter
with the existing inputless compiler and ordinary K215 calibration.

Use the complete four-tuple `(beta,K,M_C,M_F_src)`. The final coefficient is
the shifted source mask `M_F_nat+B-1`. Mixing ports from different recipes
is not justified. The coefficient integers are fully specified and enormous;
the programs do not materialize their binary expansions.

## Provenance and licensing

Baseline: `VladimirReshetnikov/ProveIt`, commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`, package
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/11-t4`.
Its original transition export records an older source commit; the exact
machine table remains byte-identical and is checked independently here.

The literal table has SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The transition JSON has SHA-256
`880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755`.
The compact JSON encoding of its 430 transition rows has SHA-256
`c6075157c74077e27fbcea05b35ab8b3a6ef0a976c08f442653f809eb1fe2d61`.

The source data and baseline predicate are used under the included exact
ProveIt MIT No Attribution license, `licenses/LICENSE.ProveIt`.
