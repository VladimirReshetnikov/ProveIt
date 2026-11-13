# Source-declared closure plan for the 76Y endpoint

The checked 76Y client uses 42 flat research modules, not just the eleven
modules covered by its [direct receipt audit](../../reviews/p64-qcube76y-chain-receipt-independent/README.md).
On 2026-11-04 [`survey.py`](survey.py) expanded their source-declared imports
through the project sources and wrote [`result.json`](result.json); a second
read-only run reproduced it byte-for-byte. The result pins every source
path, SHA-256 and explicit import edge, along with topological project and
flat-module orders. All selected sources were tracked and matched HEAD at
the observations. Comment and string handling and import parsing are
source-scanner checks, not Lean's authoritative `--deps` or a dynamic-load
audit.

The expanded graph has **42 flat research modules and 1,608 project modules**.
Of the project sources, **919** appear in the active current14 base snapshot
with identical source hashes and declared imports; **689** are additional.
There are no changed shared sources and no shared project nodes in the
computed dirty reverse closure. The proposed `project_rebuild_order` contains
those 689 nodes, and `local_order` contains all 42 flat modules. The scan
finds no project-to-flat import edges, so this declared graph permits building
the project extension before the flat sources. It does not prove that those
compilations succeed, or that 919 cached objects are safe to reuse.

The six project imports used directly by flat modules are
`ArithmeticPellFirstIndex`, `Compact44.IPRAPositive64`, `Compact44.P64Graph`,
`Compact44.P64Norm`, `Compact44.P64Root`, and `ModelDifferenceRing`, all
under `DiophantineConsistency`. Only `ArithmeticPellFirstIndex` is in the
active 1,000-source base. The remaining five are among the 689 additional
project modules and have their own transitive dependencies. Three external
module names appear in this expanded graph beyond the base's declared list:
`Mathlib.Algebra.MvPolynomial.CommRing`, `Mathlib.Algebra.Order.Ring.Cone`
and `Mathlib.Data.Fintype.BigOperators`. Each corresponding `.olean` was
present in the captured package overlay at the observation, but none of its
`.olean` module paths appeared in the Foundation receipt's declared external
guard. A replay must establish and guard the actual direct objects,
companions and search-path/namespace resolution; these observations do not
authenticate their transitive or dynamically loaded ancestry.

A safe prospective replay is:

1. Wait for the current14 base's actual terminal success, and independently
   authenticate its source snapshot, outputs, direct imports, companions,
   target reports and current-workspace status. If it fails or drifts, do
   not reuse it as a current-source base.
2. Freeze and revalidate the 689 additional project sources and the 42 flat
   sources. Put authenticated base project objects and fresh outputs in a
   single guarded project namespace; use no unrelated historical project
   overlay. Guard package objects, companions and shadow absences, including
   the three new names, and verify `lean --deps` against each declared edge.
3. Build the 689 project modules in `project_rebuild_order`, then the 42
   research modules in `local_order`, checking actual exits, all axiom reports,
   source/direct-object hashes and final provenance. Recheck all retained
   base objects and source hashes at the end. A second isolated replay and
   independent artifact audit would supply stronger evidence.

This is a **plan, not a launched build**. The existing P64 captured replay
substituted an import-only shim for `P64Graph`; a coherent build of the
canonical project sources does not assume that shim or its cached objects
are compatible. It may uncover elaboration, provider, import or memory
failures. File/JSON, compressed coefficient and PDF semantics remain
separate. Renaming or promoting flat files into a project namespace would
change imports and must be reviewed and rebuilt as a separate change; this
packet does not perform promotion.

Recheck the deterministic source plan from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76y-source-closure-plan/survey.py
```

The script rejects ambiguous flat module names, missing mapped project sources,
untracked selected sources, tracked source changes and changed source hashes;
an unmapped missing import can instead be classified as external, so its
import classification must be reviewed before a replay. A changed graph
requires a new plan. SHA-256: `survey.py`
`aaae97248c99c8bf0dda4aabbb4b6738a68c537f305ed2ec27e269b17b9f539b`;
`result.json` `bc594561278d7242d5f377b333b5ef6c1af8db817d05e3b79c70bd80565bd5bd`.
