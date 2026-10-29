# Adaptive13 expression plan freeze

2026-10-29, circuit_reduction. Read-only planning checkpoint; no Lean command,
private overlay, new proof source, prerequisite refresh, or Git mutation occurred.

The frozen proposal separates generic split-natural semiring syntax from the
wide identity with `NativeAdaptiveGraph.polynomial`. It preserves the exact
88-gate schedule and `CurrentWindowCarry2011.ports`; it does not assume any
factor extraction, arithmetic-model zero-set equivalence, or HA result.

## Exact frozen inputs

- Proposal: `adaptive-expression2011-proposal.md`, SHA256
  `519e8d1be6160478fed9ca471ae521a5abb1501841c57d9ede8cdf63ccd98a36`.
- Executed auditor: `adaptive-expression2011-cache-audit.py`, SHA256
  `ec43f42c280895fc423a5626133857ed78881fb14c1c401d485d461a949fb659`.
- Plan: `adaptive-expression2011-cache-plan.json`, SHA256
  `f8ce7569b263e774e84c106cfa8b8e2797792c74c43e006d064f22f14d0c5202`.
- Current source snapshot: `8bb2c583d0f87154a0a2e50570011a015e566029`.

The complete reachable custom DAG has 52 modules and no Foundation modules.
Six changed sources force 24 existing prerequisites to be compiled freshly;
28 source-and-dependency-identical modules retain exact historical primary
object hashes. There are 35 explicit package/toolchain boundaries, 140
primary/private/server/IR artifacts, and 34 package trace files. No unchanged
cached module imports an affected node. The proposed subsequent work has
24 prerequisite commands and four new main/check commands, pending ROOT's
independent review and authorization.

The successful audit made 780 hash observations over 344 distinct paths.
Its separate frozen-pin/header verification rehashed all 344 paths and passed.
Both executions are Python-only and their commands, exit codes, timings and
complete stdout/stderr are retained here.

## Preserved attempts and provenance limits

`attempt-01` stopped before plan creation on a historical object hash mismatch
for SignedPellResidue, which was already excluded from reuse due to changed
source. The revised auditor observes excluded historical objects separately
and still requires exact historical hashes for every selected reusable object.
It records three excluded mismatches: SignedPellResidue, NativePellStepDown,
and NativePellBootstrap. Their current bytes are not promoted to providers.

`attempt-02` stopped before plan creation because an expected list of two
package boundary names omitted three additional names absent from the two
selected historical inventories. `attempt-03` passed with the exact five-name
list retained in the proposal and plan. These were read-only metadata failures,
not Lean source or compiler failures. Every attempted proposal/auditor snapshot,
command, log and result is preserved.

The five explicitly new-to-these-inventories boundaries are current v4.32.0
Mathlib package objects with pinned source, primary/companions and trace bytes.
This is an explicit external package boundary, not a claimed fresh build or
complete transitive Mathlib source authentication. Historical Graph and narrow
ROOT evidence is retained by exact referenced hashes; its affected objects
are not used to claim a current-source wide graph.

All new Lean source remains unwritten at this checkpoint. Before any later
compiler command, the final implementation and each freshly rebuilt dependency
must be read fully, current pins rechecked, and fresh outputs isolated. The
512 MiB reserve and `-M6000 -j1 -DElab.async=false` remain mandatory.
