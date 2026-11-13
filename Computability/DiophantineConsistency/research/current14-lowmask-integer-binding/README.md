# Integer interpretation of the maintained low-mask recipe

`LowMaskInteger.lean` strengthens the separate [natural-number recipe](../current14-lowmask-display-binding/README.md).
It proves that the sparse support sum is at most `beta`, using a geometric-sum
identity and the actual support bound. Thus the natural subtractions in the
low-mask definition are exact, and `lowPort_int_recipe` identifies the port
with the displayed sequence of **integer** subtractions. The theorem
`port_two_int_recipe` states the same equality directly for slot 2 of
`CurrentMasks2011.ports K`, uniformly for every integer `K`. The maintained
`CurrentWindowCarry2011.ports` delegates definitionally to that tuple.

The existing [four-port assembly](../current14-literal-port-assembly/README.md)
already states the low-mask integer recipe as part of a structured recipe
identity for all four ports; the present packet is an independently developed
proof of the low-mask case using a different captured provider and a generic
radix support identity. The assembly also covers the high-mask recipe.

The recipe is represented as Lean terms; its relationship to the TeX or PDF
text still relies on external transcription checks. This packet itself does not
bind the other three constants, parse or assign semantics to TeX/PDF, replay
the iPRA endpoint, or authenticate transitive provider ancestry.

The bounded fourth author attempt exited 0, with both printed axiom reports
exactly `[propext, Classical.choice, Quot.sound]` and no warnings or
`sorryAx`. The source, Lean binary, directly imported recipe object, two direct
Mathlib objects and runner were hashed before and after; the receipt records
the actual command, exit, output, hashes and resource observations. Earlier
attempts record a recursion-depth failure, a successful first integer proof,
and an unsuccessful port-wrapper elaboration. Their source hashes refer to
those earlier intermediate versions, not the final source.

To rerun from the repository root with captured providers still available,
choose a fresh attempt name:

```sh
python3 Computability/DiophantineConsistency/research/current14-lowmask-integer-binding/run.py --attempt fresh-name
```

The guards do not establish full transitive project, package, dynamic-library,
or search-path ancestry. The imported recipe object is the output of the
[earlier checked author run](../current14-lowmask-display-binding/observations/author04/observation.json).
