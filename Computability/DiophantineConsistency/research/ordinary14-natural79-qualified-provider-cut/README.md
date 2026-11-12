# Natural-79 combined overlay: bounded qualified-provider cut

This read-only **lexical source/presence cut** starts from the 195 inert
snapshots in the [natural-79 combined overlay](../ordinary14-natural79-combined-slim-overlay/README.md).
It follows simple initial project-source import headers until it reaches an
existing object under the selected P72/lib route, and records external names
at that boundary. It does not invoke Lean, choose providers, authenticate a
complete dependency closure, or supply a build-ready plan. All filesystem
observations are point-in-time, non-atomic, and may drift.

At the observed state, the overlay directly names 44 qualified modules (42
project and two Mathlib). The bounded traversal reaches **44 missing selected
project objects with current source candidates**, **46 selected P72 project
frontier objects**, and **five external Mathlib names**, each with an observed
guarded-package object. The exact names, source paths, source hashes, direct
imports, object paths, resolved paths and object hashes are in
[`observation.json`](observation.json). The observed project-frontier source
hashes match the selected P72 source snapshot or linked-base producer records;
for linked-base records the object hashes also match. These comparisons are
not proof that every object was built from that source or is compatible with
all of its transitive, private, runtime or toolchain dependencies.

Compared with the independently reviewed [natural-80 cut](../ordinary14-natural80-qualified-provider-cut/README.md),
this is 39 additional source candidates, six additional project-frontier
names, and one additional external name (`Mathlib.Algebra.Ring.Basic`); no
natural-80 candidate or frontier names were omitted in this sample. The main
new branch begins at the generic `natural_dvd_of_signed` helper in
`DiophantineConsistency.BFS943.Direct80NaturalProjection`, whose current
source imports an extensive ten-input graph/projection chain. This observation
suggests a separately reviewed small helper alternative may reduce the lexical
build cut, but no such replacement is part of this packet and neither the
existing import nor an alternative has been checked by Lean here.

The bounded collision scan covers **239** names (195 inert drafts plus 44
source candidates), eight explicitly named historical roots and 13 suffixes.
Six `.olean` hits occur in two nonselected roots: one each for
`ArithmeticPellPigeonhole`, `DiscreteOrderedRingFacts`, and `ModelProductPell`
in the captured endpoint and failed Carrier65 roots. Matching or differing
bytes do not establish producer compatibility; no alternate root is selected
or authorized by this observation. Future output roots, other paths and
suffixes, implicit imports and runtime loads are not covered.

This packet pins the overlay and prior cut inventories, selected P72 progress
and source snapshots, and linked-base state, and rechecks all selected source
and object hashes and observed slots. Its source scanner handles only the
observed simple initial import form. It is not Lean's parser, namespace resolver
or `lean --deps`; it does not authenticate complete provider ancestry, all
companions, source-to-object provenance, toolchain or dynamic libraries, output
collisions outside its named roots, immutable inputs, resource guards or an
exclusive build slot. A future build requires a separately reviewed plan,
guarded resolution and elaboration and executed axiom reports. No iPRA or
physical coefficient/PDF binding follows here.

An [independent review](../../reviews/ordinary14-natural79-qualified-provider-cut-independent/README.md)
reconstructs the bounded lexical cut and collision observations without
establishing Lean resolution or provider compatibility.

Run from the repository root while the selected retained roots remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-qualified-provider-cut/inspect.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-qualified-provider-cut/observation.json
```
