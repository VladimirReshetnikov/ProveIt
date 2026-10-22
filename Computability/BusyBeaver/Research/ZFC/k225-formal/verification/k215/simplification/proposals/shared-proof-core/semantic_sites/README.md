# Semantic site contracts for the maintained K215 simulation

## Checked result

This packet refactors `BusyBeaver.ZFC.KSim` at ProveIt commit
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`. The Boolean site checker remains
unchanged. The simulation proof now consumes a semantic edge specification;
the existing checker is one producer of that specification.

Lean 4.32.0 freshly compiled the thirteen-module dependency closure and the
typed `SemanticAudit` client. The authoritative receipt is
`verification/build_result.json`, with raw compiler logs under
`verification/logs/`. The new KSim and audit files have no warnings. One
unchanged predecessor, KZip, retains an unused-simp-argument linter warning.
No full K215 endpoint or site-batch rebuild was performed for this packet.

The new `halts_iff_semantic` theorem has the following schematic interface:

```lean
SemanticCovered M p →
(∀ b, M 230 b = none) →
Rel p c T →
(RegisterPath.Halts p c ↔ KZip.Halts M T)
```

It has no symbolic-executor, fuel, Boolean-acceptance or `BoxLemmas` argument.
The theorem uses `propext` and `Quot.sound`. The old `halts_iff` theorem is a
wrapper with its original type and retains the original three standard axioms,
including `Classical.choice`. The nine printed dependency reports contain no
new assumptions or `sorryAx`.

## Why this boundary helps

The maintained `Covered` proposition asks that a particular bounded symbolic
executor return `true`. A proof that a shared primitive really reaches its
required continuation does not, by itself, prove that this particular executor
accepts. Consequently the exact decoder-prefix theorems could not directly
replace repeated site execution in the existing simulation proof.

`EdgeContract` specifies the mathematical result instead. For an ordinary
outcome it quantifies over every gap `n` and every valid register list `vs`, and
requires `Reach1` to the exact existing `tgtConf`. For a decrement it requires
both the zero and nonzero outcomes under their distinct `Valid` assumptions.
For a halt leaf it requires reachability of state 230. The terminal-row property
is kept separate, so `sim_step` keeps its old interface without a new terminality
assumption. Source length and register bounds are retained.

The adapter `edgeContract_of_check` proves that the original Boolean checker
implies the contract. `semanticCovered_of_covered` lifts this to all actual
consumed paths. The new semantic simulation proof is the old mathematical
argument with uses of executor soundness moved into this adapter.

`semanticCovered_of_allLeaves` supplies the second introduction rule: prove a
contract for every leaf of the actual source tree, plus the purely structural
check `allSites (fun _ _ => true) [] tree = true`, and obtain semantic coverage.
The structural check rejects missing decoder branches but does no machine
execution. Its proof accounts for the walk's implicit zero padding and exact
consumed word. Sharing is permitted inside the leaf-contract proof; coverage of
every occurrence remains mandatory.

## What is unchanged

`verify_invariants.py` compares the complete source text of all fifteen original
definitions: `D0`, `growth`, `start`, `tgtConf`, `FUEL`, `runTo`, `isHalt`,
`runHalt`, `allOnes`, `physOrder`, `physOf`, `vregs`, `checkEdge`, `Covered`, and
`Rel`. Every definition and the three direct imports are byte-identical.
`invariants.json` records each definition's SHA-256. Typed clients separately
check the original `runHalt_sound`, `sim_step`, `sim_stop`, `sim_halt`, and
`halts_iff` APIs. The transition table and source-program definitions are not
modified by this patch.

This is an enabling refactor, not an immediate proof-size saving: KSim grows
from 356 lines / 16,146 bytes to 480 lines / 21,995 bytes, an increase of 124 lines
and 5,849 bytes. No primitive obligation, branch case, or execution certificate
has yet been removed. No speedup is claimed from the reported build duration.

## Next concrete migration

Use `KDecoderPrefix215.leaf_prefix` to reach the exact primitive port while
retaining the complete consumed source word and its ancestry. Compose its
possibly zero-length prefix with a *positive* primitive/continuation theorem.
The existing `KZip.Reach.trans_reach1` already gives the required positive
whole-step result. A semantic shared proof for each leaf then feeds
`semanticCovered_of_allLeaves`.

The phase-nine notes identify a first CB1 suffix family with 86 literal leaf
occurrences. Its proposal remains uncompiled in the pinned source. It requires
the complete prefix, the length guard `|A| + 3 ≤ D0`, and a `LeftWord` guard.
Those hypotheses cannot be replaced merely by the physical entry state or a
short path suffix. A useful next result is one checked CB1 theorem with all
those hypotheses, followed by its exact leaf-family binding. Only after that
should the corresponding executor checks be replaced and a controlled timing
comparison made.

## Reproduction

All twelve unchanged predecessor sources are included with their original
headers; the only external dependency is the Lean 4.32.0 distribution (`Init`).
`provenance.json` binds them to the pinned repository. From this directory run:

```sh
python3 verify_invariants.py
python3 build_semantic.py --lean /path/to/lean-4.32.0/bin/lean --out /tmp/ksim-semantic-fresh
```

The output directory must not already contain `build/` or `logs/`. The script
compiles serially with `-j1`, records source/compiler/object/log hashes, and
uses the shared `/tmp/proveit-k215-proof-build.lock` on Unix. This receipt
reproduces a focused prototype check, not the full maintained endpoint.

`KSim.semantic.patch` applies to the pinned repository. For deterministic
regeneration of the proposed file and patch, use:

```sh
python3 refactor_ksim.py --repo /path/to/ProveIt --out /tmp/ksim-regenerated
```

The reference source and diff make the change reviewable without applying it.
Use a clean integration branch, refresh the affected endpoint clients and any
required dependency receipts, and retain the existing site checks until shared
primitive contracts are proved.

## Attribution

The unchanged runtime and register semantics are ProveIt sources retaining
their original attribution to Elliot Glazer's K230 development, Jeff
Ketchersid's m254 verification, Andrew James Wade's compiler framework, and
their stated upstream sources. The semantic interface, checker adapter,
compatible wrappers and focused audit in this packet were prepared for
Vladimir Reshetnikov's ProveIt project. No priority claim is made for the general
idea of semantic simulation contracts. The original project license and K215
notice are supplied in `provenance/`; inherited third-party terms are not
changed.
