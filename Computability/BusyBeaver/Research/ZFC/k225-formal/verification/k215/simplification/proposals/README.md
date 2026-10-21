# Proof-simplification proposals for the K215 endpoints (batch 205)

Six research packets, each placed whole and byte-identical (logs stay out by the ignore rules),
delivered in arrival commit `a6b3a30011`. Nothing was rerun at intake; compilation claims are the
packets' own. Each archive is recoverable with `git show a6b3a30011:docs/incoming/NAME.zip`.

| Directory | Archive | Main proposals |
|---|---|---|
| [k215-simplification](k215-simplification/README.md) | `K215_Proof_Simplification_2026-10-21` | source certificate quotiented by trailing zeros, 2,240 -> 1,426 checkpoints, with a Lean checker reusing the segment bisimulation (compiled against the pinned repository); compiled Lean transport CM215 <-> K215; positive stuttering in Coq 8.18 |
| [k215-transport](k215-transport/README.md) | `K215_Proof_Transport_2026-10-21` | positive-block forward simulation (no reverse certificate); compiled Lean CM215 <-> K215 on the repository's dense semantics; graph-congruence measurements |
| [structural](structural/README.md) | `Structural_Proof_Simplification_2026-10-21` | normalization-aware bisimulation (decoder trees normalize to identical 1,426-vertex graphs); a calibration patch replacing two syntactic round-trip inductions by the semantic one; startup compressed to 39,889 sweeps. Uncompiled |
| [zfc215-simplification](zfc215-simplification/README.md) | `ZFC215_Proof_Simplification_2026-10-21` | `source_proof/Source215Simple.v`: ordinary bisimulation, one certificate and symmetry, compact path codec (173,003 bytes vs 1,499,170), decoding proved equal to the original (Coq 8.18); Lean and Rocq all-tape proofs for M124 |
| [zfc-k215-transport](zfc-k215-transport/README.md) | `ZFC_K215_Proof_Transport_2026-10-21` | positive stuttering; standalone Lean K215 <-> CM215; Lean shared-tree and Rocq compact-path data pilots. `reference/` (repository copies) omitted |
| [k215-simplification-2](k215-simplification-2/README.md) | `K215_Proof_Simplification_2026-10-21 (2)` (batch 206, arrival `53269bcab1`) | a different, larger packet under the same name: `coq/` proves symmetry for the actual offset checker (forward certificate only) and the compact/original certificate equality (Coq 8.18, recursive `coqchk`), with a `Source215.v` patch; `plain_source/` checks the ordinary zero-offset source equivalence in Lean (70 modules); compiled Lean CM215 -> `KDense215.machine215` |
| [k215-simplification-3](k215-simplification-3/README.md) | `K215_Proof_Simplification_2026-10-21(1)` (batch 207, arrival `beaabc8e3b`) | a third packet under the name, finite replays and uncompiled drafts: the two source programs have equal 1,426-node increment-count CFGs, and their ordered CFGs differ by 256 adjacent increment swaps from two shared DAG templates; canonical checkpoint rows (814 aliases removed, minimization removes 3 more); packed Rocq certificate and Lean symmetry/canonical-row/local-swap drafts; a comparison of alternatives for proof simplicity (`candidates/COMPARISON.md`). `lean/snapshot/` (a mirror of this repository) and `new_intake/gc_zc215/received.zip` (batch 204's archive) omitted |
| [fm215-compression](fm215-compression/README.md) | `zfc-fm215-proof-compression-2026-10-21` | shared decoder contexts (234 roles cover 4,750 internal occurrences); FM215 with a compiled Lean transport; a compiled logical obstruction. `machine/inherited_notices/` and `machine/tables/` (repository copies) omitted |

**FM215 is not a new alternative.** It differs from M124 (`candidate-k215/alternatives/dr215/markers/
marker_family/m124`, batch 204) in one row only, 127/1 -> 109 instead of 59: the same merger of decoder
roles 124 and 127 behind a predecessor marker, with an equivalent provider. Its proof is kept as proof
material.

**Status against `main` at placement.** The Lean source layer already checks one certificate through
`RMOffsetBisim.OBisim.symm`. Open, in order of value for the K215 endpoints: the single-certificate
Rocq source proof with the compact codec (`zfc215-simplification`), the trailing-zero quotient of the
Lean certificate (`k215-simplification`), the calibration patch (`structural`), and shared decoder
contexts for `KSites215` (`fm215-compression`, `structural`). The CM215 and M124 transport proofs give
formal endpoints for those alternatives once their adapters are compiled.
