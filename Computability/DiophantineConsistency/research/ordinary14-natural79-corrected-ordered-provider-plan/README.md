# Candidate lexical provider order for the corrected natural-79 overlay

This is a **read-only candidate order**, not a build plan certified by Lean.
It combines the [196-module corrected inert overlay](../ordinary14-natural79-corrected-reflection-overlay/README.md)
with the [corrected lexical provider projection](../ordinary14-natural79-corrected-reflection-provider-cut/README.md).
Nothing is materialized or compiled.

An [independent review](../../reviews/ordinary14-natural79-corrected-ordered-provider-plan-independent/README.md)
checks the lexical order, frontier observations and bounded collisions without
establishing actual Lean resolution or provider provenance.

The receipt records **201 stages**: the five project sources missing from the
selected P72 frontier, followed by the 196 inert overlay modules in their
checked dependency-first order. The first five are, in order:

1. `DiophantineConsistency.DiscreteOrderedRingFacts`
2. `DiophantineConsistency.Compact44.FreeJ13`
3. `DiophantineConsistency.Compact44.FreeJ13Halt`
4. `DiophantineConsistency.BFS943.Direct80IndexOne`
5. `DiophantineConsistency.HAExpressionNoZeroEquiv`

The checker rereads every stage's selected source, pins its hash and actual
simple initial import header, and verifies every named import is in an earlier
stage or the selected frontier. It rejects duplicate unreserved primary output
names. The resulting order is a lexical candidate, not `lean --deps`, an actual
compiler command, a destination reservation or evidence of successful
elaboration.

The receipt also records current source and selected object path, resolved
path and SHA-256 for each of the **41 project** and **six external** frontier
names. Project records retain applicable earlier snapshot and base hashes.
External records include the newly selected Foundation `IOpen.Basic` and its
retained guarded source; five Mathlib sources come from the workspace package.
These observations and earlier snapshot links do not authenticate producers,
prove source-object identity, validate package or toolchain compatibility, or
establish complete transitive object and companion dependencies.

The checker repeats the corrected projection's bounded collision observation
for the 201 proposed stage names, eight historical roots and 13 suffixes. It
again finds two `.olean` observations for `DiscreteOrderedRingFacts`, in the
captured endpoint and carrier retry roots; their existence requires deliberate
collision handling. There are no other hits in that specified scan, which does
not inspect every possible destination or reserve any path. Foundation provider
name observations are separately recorded in the linked projection and are not
stage output names.

This packet is **not build-ready**. The retained package/source snapshots,
frontier objects, five candidate sources, output namespace and future runtime
would require independent authentication and review, complete dependency and
companion checks, current resource and collision guards, Lean elaboration and
executed axiom reports. This packet does not establish the iPRA equivalence or
the physical binding to the separate Carrier65 PDF.

To reproduce the deterministic observations, from the repository root while
the retained `/tmp` roots and workspace package sources remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-ordered-provider-plan/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-ordered-provider-plan/plan.json
```
