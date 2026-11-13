# Preliminary same-witness symbolic congruence source closure

This is a source-only plan, not a paired build. It proposes compiling the
extended source `free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean`
from commit `f3afbc380f` on each corresponding side of the independently
audited graph-derived-radix pair. Its SHA-256 is
`d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0`.
This is **additional source**, not the first-root source pinned by the
separate review `d639105ccb`: the extended file repeats the original
congruence declarations and adds `symbolic_aligned` and
`fixed_symbolic_aligned`. Its two direct project imports are the same:
`CompactGraphDerivedRadix` and `ArithmeticModularCancellation`.

The separately rerunnable scan hashes that source against its committed
bytes, verifies the existing paired radix-audit receipt, compares 143
inherited object paths and hashes across both provider sides, records the 40
direct project companion slots and package Init, and requires all 20 target
companion slots absent. Its actual normal run exited 0; the optimized run
exited 1. A separate comparison found that its 143-object inventory, direct
slots, Init and two imports exactly match the earlier first-root closure
scan. These are point-in-time facts, not continuous source or filesystem
protection; the scanner does not rerun the parent audit or authenticate all
package, transitive or dynamic ancestry.

Both source files intentionally declare the same Lean module name
`FreeJGraphCongruenceExplore`. A future paired run for **this extended file**
must start with fresh overlays of the graph-derived-radix provider, confirm
that all target slots are absent, freeze and hash this source, and compile it
once per side. It must not overlay the original first-root object and treat
it as this extended source. The two object builds are distinct alternatives
unless the extended declarations are later refactored into a separate module.

A future driver should rerun and compare the full pinned parent audit, check
same-side direct imports and all their companion/output slots before and
after each child and after final audits, enforce regular non-symlink frozen
sources and outputs, and require exactly these five declarations with the
observed `[propext, Classical.choice, Quot.sound]` sets and no warnings or
admissions:

* `FreeJGraphCongruenceExplore.fixed_symbolic_aligned`
* `FreeJGraphCongruenceExplore.symbolic_aligned`
* `FreeJGraphCongruenceExplore.first_pair_mod`
* `FreeJGraphCongruenceExplore.graph_congruence`
* `FreeJGraphCongruenceExplore.graph_aligned_congruence`

The exploratory theorem uses fixed symbolic beta, low and high masks, an
arbitrary natural `K`, the literal graph zero, and positive graph variables.
It obtains the digit bounds and weighted congruence for the same `N,w`.
It does not bind K or masks to retained bytes, derive the specific
weighted-word decomposition or carry premises, construct the compact
decoder, prove machine correctness, or produce an internal iPRA proof.
A future launcher and resulting artifacts need independent prelaunch and
post-build review, externally coordinated clean initial loader, stable HEAD
and sole Lean slot. Compiler resource measurements remain sampled, and the
`--deps` and parent audit subprocess boundaries must be recorded separately.
