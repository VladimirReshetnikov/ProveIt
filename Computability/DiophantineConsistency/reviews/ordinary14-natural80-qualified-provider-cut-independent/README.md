# Independent review: natural-80 qualified-provider cut

The [provider-cut inspection](../../research/ordinary14-natural80-qualified-provider-cut/README.md)
is supported by this bounded, point-in-time recheck. Its original receipt and
the independent receipt below reproduce in the retained environment. Neither
runs Lean or certifies a complete or compatible provider closure.

The independent checker reads and hashes all 184 inert overlay snapshots and
re-extracts their simple initial import headers; their union contains the 40
recorded direct qualified names. Starting from those names, a separate FIFO
traversal follows current source headers for a `DiophantineConsistency.*`
module only when its `.olean` path under the selected P72 tree is absent.
It reproduces exactly five source candidates, 40 selected project frontier
objects and four external names. It independently verifies the observed 32
P72 source-snapshot and eight base-record source matches, and checks the base
object hashes where the pinned base record supplies them. Relative to the
root74 cut the two additional source candidates and nine additional frontier
names match the receipt. These are lexical source and point-in-time object
observations, not evidence that the source was the producer of each object.

The independent checker scans the same explicitly bounded 189 names, eight
roots and 13 suffixes, examining 19,656 paths. It reproduces two occupied
`DiscreteOrderedRingFacts.olean` slots: their hashes agree, their realpaths
differ, and neither is a selected-P72 object. It also rechecks all direct-name
object paths across those roots; six names have at least one alternate file
whose hash differs from the selected object, including `ModelDifferenceRing`.
Some same-name paths resolve to the same file. Different hashes alone do not
prove semantic incompatibility, and equal hashes do not authenticate producer
history or justify mixing roots.

The review shares the same pinned inventories and retained build records as
the original inspection. It does not independently authenticate the historical
P72 producer records, follow compiled imports or source imports after an
object is found, inspect all object/companion/runtime types, resolve Lean's
search order or `import all`, reserve resources, or check an endpoint and its
axioms. Reads are non-atomic and depend on retained temporary paths. The
observed cut is not a launch-ready build plan, iPRA derivation or byte/PDF
binding.

Run from the repository root while the retained paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-qualified-provider-cut-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-qualified-provider-cut-independent/result.json
```
