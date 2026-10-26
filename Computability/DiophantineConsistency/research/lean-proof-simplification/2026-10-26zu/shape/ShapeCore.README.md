# Standard-library validation of raw split shape

`ShapeCore.lean` was generated from source declarations at repository commit
`9d9d1123b39927d30363f1dcd53c23f0575c30ee` and the precise proposed source files
listed in `ShapeCore.manifest.json`. The generator asserts each complete input
file's SHA-256 before writing the checker. The copied original size module and
the maintained source module must match the same hash.

The extracted declaration bodies are unchanged. The only textual normalization
is `ℕ` to `Nat`, `ℤ` to `Int`, and `Type*` to `Type _`, allowing an import of only
`Lean.Elab.Tactic.Omega`. The old `splitSize` is placed in a `Legacy` namespace
so it can coexist with the proposed definition. Imports and unrelated source
declarations are deliberately not included.

## What was checked

The generated checker passes Lean 4.32.0, compiler commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, with exit code zero.

| Result | Printed axioms |
|---|---|
| Generic ordered operation-preserving shape-fold equality | `propext` |
| Equality of both trees after leaf erasure | `propext` |
| Equality of both raw node counts | `propext` |
| Equality of both raw depths | `propext` |
| Proposed scalar `halfSize`/diagonal `splitSize` correctness | `propext`, `Quot.sound` |
| Original `splitSize` always reaches the diagonal | `propext`, `Quot.sound` |
| Proposed `splitSize` equals original `splitSize` for every expression | `propext`, `Quot.sound` |
| Equality of the proposed record's two projections | none |

Two reduction checks establish that both raw trees of `x*x` have seven nodes.
A further inequality check compares the shapes `x*x` and `0`; it only
illustrates why the raw theorem does not by itself control separately
simplified expressions. The actual `NatExpr.simplify` implementation is not
extracted or certified by that example.

No new axioms or admitted proofs occur in the successful checker. The complete
stdout is in `ShapeCore.log`. The exact compiled file hash is recorded in
`ShapeCore.validation.json`.

## Replay

With Lean 4.32.0 on the executable path:

```sh
lean ShapeCore.lean
```

To regenerate using the pinned checkout and this directory's candidate files:

```sh
python3 generate_shape_core.py --repo /path/to/ProveIt
lean ShapeCore.lean
```

This is a kernel check of an exact extracted source slice. It is not a fresh
build of the full repository import graph and does not validate omitted graph
compiler, witness-count, or expression-renaming declarations. The universal
equality of old and new size data is proved, rather than inferred from a finite
sample; downstream full-project elaboration remains a separate integration
check.
