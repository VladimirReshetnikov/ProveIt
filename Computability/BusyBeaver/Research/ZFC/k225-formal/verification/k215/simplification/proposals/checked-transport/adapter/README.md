# Exact native K215 to maintained sparse-semantics adapter

`NativeSparseAdapter.v` connects the new transport development's exact old
native K215 machine to the actual repository predicate

```
K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0
```

The theorem `native_blank_halts_iff_sparse` has no generic calibration or
simulation premise. It checks the literal old native table against the
maintained `K215F.TM230.tmn`, using the state map

```
301 -> 102, 302 -> 120, 254 -> 230; all other labels unchanged.
```

A finite Boolean certificate establishes transition correspondence, state
bounds, and the unique active terminal; a second certificate establishes
closure of transition targets. The active-label condition is necessary:
the native model leaves missing rows fixed and designates state 254 as halt,
while BusyCoq regards any missing row as halted. The 15 disabled sparse
working labels cannot be reached from a related active native state.

The two stream types are related by an observational coinductive relation.
The adapter proves forward and backward one-step simulation, halting
reflection, both finite-run implications, and the exact blank configuration
relation. No stream extensionality, function extensionality, or custom
axiom is used.

`ContextSparse.v` composes the adapter with the checked context-return
transport. `ContextLiteralSparse.v` also uses `LiteralBindings.v`, attaching
the supplied literal 430-row table. Their final conclusions are equivalences
with the precise maintained K215 sparse halting predicate, not with an
abstract hypothetical source theorem.

## Complete ZFC client boundary

`ContextZFCClient.v` imports `K215F.Correct215` and composes its established
`tm215_sparse_halts_iff_ZFC_inconsistent` theorem with the literal adapter.
Its statement uses `StandardZFC ⊢TC ⊥` from the real repository interface.
This client has no postulated ZFC consistency theorem or custom axiom.

The minimal build does **not** freshly compile this client or rebuild the
237-source complete ZFC closure. Its correctness is an explicit composition
with the existing audited endpoint; describing this packet as a fresh
end-to-end rebuild would overstate what was run. Compile the client inside
the maintained full K215 lane to obtain that additional recorded check.

## Reproduction

The minimal build requires the completed transport folder containing
`NativeContext.v` and `LiteralBindings.v`. It uses a fresh output directory:

```
python3 build.py --native-dir /path/to/transport --out /fresh/check
```

The driver copies exact source files, compiles the listed dependency closure,
recursively runs `coqchk` on `ContextLiteralSparse`, and retains source/object
hashes, tool identity, timings and logs. The recorded toolchain for this work
is Coq 8.18.0. This is not a Rocq 9.1.0 replay.

All dependencies are included as source. BusyCoq's three files are exact Git
blobs from Jeff's pinned dependency commit
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`; the two K215F files are exact copies
from ProveIt commit `aa66d0a33f1f8237a348899eb8095b045a502832`.
`SOURCES.json` records paths and SHA-256 hashes. Their notices and BusyCoq's
MIT licenses are retained. The imported tactic library declares some global
axioms, but the selected adapter endpoint assumption reports are closed:
those declarations are not dependencies of the reported results.
