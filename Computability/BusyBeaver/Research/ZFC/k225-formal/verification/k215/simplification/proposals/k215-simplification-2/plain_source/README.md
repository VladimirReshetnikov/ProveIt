# Ordinary K215 source equivalence

This is a portable, isolated source-equivalence lane for ProveIt commit
`b6c7087477e51c017003bd729e712c8969733223`, checked with Lean 4.32.0.
All 70 project modules in `build_plan.json` compiled successfully during this
session. Unchanged objects were reused only within this session after source,
object, saved-log hashes and direct-dependency modification times matched.
`result.json` records the final selected source/object/dependency ledger.
Compiled objects, toolchains and caches are excluded from this packet.

## Exact checked interface

```lean
SetTheory.BusyBeaver.ZFC.KSource215PlainAudit.source_halts_iff_iter
    (R : RegisterPath.Registers) :
  RegisterPath.Halts KSource215.p215 ⟨[], R⟩ ↔
    RMDag.IterHalts DagPerm.dagPerm R
```

This establishes the same source bridge as the existing K215 proof for every
register file. It includes exact bindings of both literal trees to the actual
source programs, and the exact well-formedness proof connecting the path DAG
to its iterative semantics. It does not rebuild the dense binary machine
endpoint `KEndpoint215`. The final exact axiom output is in
`build_logs/KSource215PlainAudit.log` and repeated in `result.json`.

## Why this simplifies the proof

All 2,240 signed offsets in the old certificate are zero. The new
`RMPlainCodec` checker uses the ordinary equal-register segment relation and
reuses `RMBisim.Bisim.halts_iff`, including its symmetry. The integer-offset
module `RMOffsetBisim` is absent from this entire import closure.

The checker interface is parameterized over an arbitrary path decoder. The
chosen `totalDecode n := RMBisim.decodeAux n n []` has input-dependent fuel;
it does not silently truncate paths to the old ordinary decoder's 128-step
cap. 622 path occurrences exceed 128 bits and the maximum is 176. The semantic
soundness theorem is valid for every decoder, independently of any codec law.
The concrete checks run in the kernel and validate the complete certificate.

The exact original source trees are represented by 427 shared subtrees. The
ordinary monolithic data prototype is 220,643 bytes versus 456,548 upstream.
The data/facade modules actually shipped here total 224,084 bytes after
partitioning. The new generic checker is 113 lines/4,639 bytes, compared with
the omitted offset checker 293 lines/13,151 bytes. These measure source and
certificate representation, not proof-object sizes or total build speed.

## Rebuild from source

Supply the complete shipped core of Lean 4.32.0. No Lake, Mathlib or network is
needed. From this directory:

```sh
python3 build.py --lean /absolute/path/to/lean-4.32.0/bin/lean
```

This portable runner rebuilds every dependency serially into `fresh-build/`
and stops at the first failure. `--output /absolute/output/directory` selects
another output location. Logs and a fresh result ledger are written there.
Memory use depends on available system resources: the supplied partitioning
was chosen for an 8 GiB shared environment. This is not a minimum-memory claim.

## Execution and integration boundary

The original monolithic evaluation and one 140-entry certificate block exceeded
our available memory. Those attempts are recorded separately under
`historical/attempts`; they are not selected successes. Finite checks were
partitioned into 16 DAG well-formedness chunks and certificate chunks of 140 or 70
entries without changing their propositions. `allC_of_halves` composes checked
halves abstractly, so wrappers do not normalize complete concrete data again.

`historical/run_lean.py` and `historical/build_plain.py` are the original
session drivers, retaining their absolute paths for execution provenance.
The top-level `build.py` is the portable fresh-build driver. Historical
transformation records describe intermediate source states; `result.json`
and `manifest.json` describe the final shipped sources.

Before production adoption, update the maintained generators, integrate the
source facade, rebuild all affected production consumers and both typed
endpoint clients, and compare final axioms. No claim is made here that the
full binary endpoint closure has become smaller, faster or freshly rebuilt.
