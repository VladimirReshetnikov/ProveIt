# Natural-80 combined overlay: bounded qualified-provider cut

This read-only, point-in-time inspection starts from the 40 direct qualified
imports in the pinned [natural-80 combined overlay](../ordinary14-natural80-combined-slim-overlay/README.md).
It rechecks all 184 inert source snapshots and their simple initial import
headers, then walks missing `DiophantineConsistency.*` source headers until
it encounters an existing `.olean` under the selected P72/lib path. External
names terminate the walk. This is a **lexical presence cut**, not `lean --deps`,
a complete dependency closure, an ordered build plan, or a guarantee that Lean
will resolve or accept these objects. The program neither invokes Lean nor
modifies retained evidence.

An [independent review](../../reviews/ordinary14-natural80-qualified-provider-cut-independent/README.md)
reconstructs the lexical walk and bounded collision observations without
establishing actual Lean resolution or provider compatibility.

At the observed filesystem state, five project modules lack a selected-P72
object and have the following current source candidates:

1. `DiophantineConsistency.BFS943.Direct80IndexOne` —
   `Lean/DiophantineConsistency/BFS943/Direct80IndexOne.lean`, importing the
   observed `ArithmeticPellPowerRecovery` frontier object.
2. `DiophantineConsistency.Compact44.FreeJ13` —
   `Lean/DiophantineConsistency/Compact44/FreeJ13.lean`.
3. `DiophantineConsistency.Compact44.FreeJ13Halt` —
   `Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean`, importing the
   previous source candidate.
4. `DiophantineConsistency.DiscreteOrderedRingFacts` —
   `Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean`.
5. `DiophantineConsistency.HAExpressionNoZeroEquiv` —
   `Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean`, importing the
   observed `HAExpressionAssembly` and `AdaptiveEquationSyntax2011` objects.

The first and last are additional to the previously reviewed three-source
[root74 cut](../ordinary14-root74-provider-survey/README.md). Exact source
hashes and all source-header imports are in `observation.json`. The inspection
also observes 40 selected-P72 project frontier objects and four external
Mathlib object names; compared with root74's bounded cut, nine additional
frontier names are listed in the receipt. The current frontier source hashes
match either the selected P72 source-snapshot entries (32 names) or the linked
base producer records (eight names); those eight recorded base object hashes
also match their current paths. Matching source and object hashes or recorded
names do **not** prove that every P72 producer was built from that source,
that all transitive providers/companions match, or that mixing roots is safe.
The four external object path/realpath/hash observations match the pinned
root74 survey; their transitive provenance is not inspected here.

For output-name observations, the checker scans exactly 189 names (184 bare
draft names and the five candidate qualified names), 13 historical output or
companion suffixes and eight explicitly listed roots. It finds two existing
`.olean` paths for `DiscreteOrderedRingFacts`, one in a captured endpoint root
and one in the failed Carrier65 retry05 root; both have the same observed
SHA-256 but distinct realpaths. Neither is in the selected P72/base route,
and equality of those two files does not authenticate their producers or
establish compatibility. The other observed slots in that bounded scan are
absent. No new output directory is selected or reserved, and collisions in
other roots, object suffixes, package/runtime imports or future paths remain
outside the scan.

The separate direct-qualified-object observations include paths under a
captured P72 endpoint root and the failed Carrier65 root. Six direct module
names have an alternate observed `.olean` whose hash differs from the selected
P72 object (including `ModelDifferenceRing`); multiple same-name paths may
also resolve to the same file. These are observations of potentially competing
providers, **not** an instruction to add those roots, or proof that differing
bytes imply a particular semantic incompatibility. Selecting an actual
provider route requires independently checked provenance, transitive and
runtime closure, companion handling, exact search precedence, immutable
inputs, resource and collision guards, and guarded Lean dependency resolution.
The old failed roots must not be silently mixed into the selected route.

All filesystem observations are non-atomic and depend on retained `/tmp`
paths. The simple header parser is not a Lean parser; it does not expand
qualified modules once an object is found, account for implicit imports or
`import all`, resolve packages, or run tactics and axiom checks. The output
is not a proof of the 80 endpoint, iPRA derivability, or physical byte/PDF
association. Reproduction from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural80-qualified-provider-cut/inspect.py | cmp - research/ordinary14-natural80-qualified-provider-cut/observation.json
```
