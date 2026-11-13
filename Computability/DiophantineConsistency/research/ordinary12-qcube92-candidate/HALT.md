# Fixed-port all-model halt equivalence

`QCube92Halt.lean` proves, in every model `V` of `IΣ₁`, that the 92-operation
expression instantiated with the fixed symbolic four-port tuple has a
strictly positive zero exactly when

```
∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0.
```

The witnesses, including `T`, can be nonstandard elements of `V`. Separate
theorems give the same equivalence after substituting `x+1` for each witness,
and after using the exact closed Lean byte recipes for all four ports. The
92-operation count applies to the unshifted positive-coordinate graph; it
does not include the separate coordinate shifts. `beta_pos` discharges the
positive-β premise using the previously checked fixed-beta bound.

The bounded author check in `observations/halt2-attempt01/` exited 0 in 10.3
seconds, with no warning or `sorryAx`. All four named axiom reports list only
`[propext, Classical.choice, Quot.sound]` as Lean metatheory axioms. Its
source and runner SHA-256 hashes are
`4761687cb642710db6e6b10b205611b0f3920c2b0916ce13265c773ae3fa7429` and
`0723a9bcb8bcf8a7b5d215d8f57a7442aa2cce0e98126c8c1a5cc99b64737ac3`.
The exact runner is also retained with the receipt. Three resource samples
saw at most one Lean process and at least 18,524,376 KiB MemAvailable;
between-sample dips or overlaps are not excluded.

The runner pins and rechecks the 1,288-file fixed-port model union and the
three selected 92-proof additions, for 1,291 selected files. It pins both
independent serialized-ancestor results, checks their inputs and selected
ancestors, and records the declared direct imports. The conflicting top-level
`FreeJRootBinding` and old top-level existence objects are absent from the
final union. The known differing `FreeJOrdinaryTailWitness` and extra
`FreeJSignedTransport` search-path objects are treated as irrelevant only
because the recorded serialized ancestor checks exclude them from the new
proof's selected-project closure. All union and input checks passed again
after compilation. The two earlier strict preflight failures, the later
preflight wrapper failure, and the duplicate-module Lean failure are retained
under `observations/`; see [HALT_PREFLIGHT.md](HALT_PREFLIGHT.md) and
[NAMESPACED_EXISTENCE.md](NAMESPACED_EXISTENCE.md).

This is a model-level Lean theorem, not an internal iPRA derivation. Selected
serialized-project ancestry is checked within the recorded scope; complete
historical source-to-object, package-transitive and dynamic ancestry remain
inherited. The numerical graph and its Lean expression have an external
source check; equivalence to external coefficient/gzip files or a PDF is not
a Lean filesystem or PDF theorem. The accepted run is a single-author build,
not an independent Lean replay.

To repeat, preserve the recorded temporary providers and choose a fresh
attempt:

```sh
ATTEMPT=attempt02 python3 run-halt2.py
```
