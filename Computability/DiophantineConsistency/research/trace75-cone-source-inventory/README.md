# Captured 186-module impact cone: source inventory

The read-only `check.py` inventories the 186 project modules reverse-reachable
from the four selected baseline nodes in the captured final fixed-endpoint
header graph. It pins the six producer results, the two historical source
plans, the previous four-node capture, and the final endpoint result. It
invokes no Lean and makes no changes to those inputs. The complete per-module
records, deterministic captured-header topological order, 141 direct
project inputs outside the cone and four direct outside names are in
`observations/attempt03/stdout`.

At the recorded Git HEAD, all 186 selected producer outputs matched a
recorded stage by realpath and object/companion hashes. All 186 retained
producer source copies, all 186 identified workspace source candidates, and
all 372 recorded stage-log hashes matched their records. All source-declared
imports matched the selected serialized headers. The identification methods
are distinct:

* 67 workspace paths come from the pinned 127-stage source plan.
* 60 workspace paths are explicitly recorded as sources of the later stages.
* 59 workspace paths are **inferred** by taking the prototype directory
  containing a captured 65-stage historical snapshot and looking for the
  module-named `.lean` sibling. The byte match is checked, but this naming
  convention is not itself a declaration of canonical status by the producer.
  All 59 corresponding historical snapshot-receipt hashes match.

Of the 186 identified workspace paths, 184 were in the Git index and two
were workspace-only at the recorded HEAD. The scanner does not stage or
modify them. Each has a tracked byte-identical alternative:

* `OffsetBound`: workspace-only
  `research/ten-positive-offset-bound-prototype/OffsetBound.lean`; tracked
  alternative `research/generic-transport-rebuild/OffsetBound.lean`, both
  SHA-256 `696900c026b495235e88def39125f56b774341f1ed6ddd5aaccc5a9d0080525b`.
* `DirectBFSOriginBlockResidue`: workspace-only
  `research/direct-bfs-origin-block-residue-prototype/DirectBFSOriginBlockResidue.lean`;
  tracked alternative
  `research/direct-bfs-80-coherent-rebuild/observations/attempt01/stage-044/source.lean`,
  both SHA-256 `286d8c9d20b09dce60fa2d3266f9c675d228d0531819ef4b9567aae92ebce79f`.

There were 470 captured producer-before/after direct-bundle comparisons
where those records exist, with no mismatch against the final selected
bundles. This is not a claim that all 186 stages recorded such bundles. The
captured graph has 294 internal edges; its 186 nodes admit the recorded
topological order. The four direct outside names are `Init`,
`Mathlib.Algebra.Ring.Divisibility.Basic`, `Mathlib.Tactic.Linarith`, and
`Mathlib.Tactic.LinearCombination`.

Attempt03 exited 0; checker SHA-256 is
`7e17c6d76e6f9baa78779b88b2976487a8cc3553ba906e8ef29a8262f9306e33`,
terminal SHA-256 is
`92a083a3e5303c190846f3dd0f083eef840b6cb3cd980d0fa05054a22970bcc5`,
and stdout SHA-256 is
`473df595296a18b16836906d2dd6daf4b740fea1e56014e1bebaaabd9fececbf`.
The [independent inventory audit](../../reviews/trace75-cone-source-inventory-independent/README.md)
rechecked the source-path classifications, both tracked alternatives,
producer/log evidence, direct-bundle comparisons and captured topology. It
did not run Lean or authenticate the missing upstream ancestry.
Attempt01 is **rejected for Git classification**: it omitted `--full-name`
and consequently labeled every path unindexed despite exiting 0. Attempt02
corrected that option; attempt03 adds a known-tracked sentinel so the same
failure cannot silently recur. Both earlier sources and outputs are kept.

This is a feasible *captured-header order* for a possible replay, not a
complete source-current build plan. The 141 direct project inputs need their
own source/object provenance and compatibility assessment; changes there,
changes to imports, and dynamically loaded or package-transitive inputs may
expand the required cone. Source snapshots, Git index status and matching
bytes do not by themselves establish historical producer selection or a
fresh Lean replay. The final endpoint's inherited ancestry and external-file
binding limits remain.
