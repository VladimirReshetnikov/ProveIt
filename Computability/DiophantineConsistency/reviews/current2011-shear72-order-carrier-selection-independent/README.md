# Independent review of the narrowed ShearOrder source selection

The alternate source differs from the original only in its import block; all
three theorem bodies and their assumptions are byte-for-byte unchanged. The
selected direct frontier change is exact: remove `ModelCarrierSpheres`, add
`Carrier65`, `Mathlib.Tactic.Linarith` and `Mathlib.Tactic.ByContra`. The
resulting selected graph has 15 draft names and 13 direct frontier names and
is reachable and acyclic. No missing source name was established by this
bounded inspection; that is not an elaboration or full import-closure result.

The source's project-specific expression is `Carrier65.core`, whose pinned
source declares the `c`, `f`, `rank` and `V` fields and the exact expression
`V=f²*(c*T−rank)−c`, with `T=v 6`. The generic ring/order arguments use
`CommRing`, `LinearOrder`, `IsStrictOrderedRing`, order lemmas and standard
Lean tactics. The independent checker pins and checks concrete source import
paths:

- `Linarith` publicly imports `Linarith.Frontend`, which declares both
  `linarith` and `nlinarith`; it also reaches the pinned ring and ordered-ring
  definition sources through public imports.
- `ByContra` publicly imports `Batteries.Tactic.Init`; the latter declares
  the plain `by_contra` syntax used in this file. The Mathlib module itself
  additionally defines the different `by_contra!` variant.
- `Carrier65` imports `ShortSystem`, which imports `ConsecutivePell`; their
  inspected source imports lead through integer/natural basics to the pinned
  linear-order source. The inspected ordered-ring source declares
  `IsStrictOrderedRing` and uses the relevant nonnegativity lemmas.

These paths provide narrower evidence than a complete imported-environment
inventory. In particular, they do not establish that the `simp`, `change`,
`nlinarith only`, instances or namespace resolution elaborate, and removing
`ModelCarrierSpheres` from this *direct* frontier does not prove its
transitive absence. No compiled object, package, collision, full ancestry,
model bridge or iPRA endpoint was authenticated here.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear72-order-carrier-selection/check.py | cmp - research/current2011-shear72-order-carrier-selection/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear72-order-carrier-selection-independent/check.py | cmp - reviews/current2011-shear72-order-carrier-selection-independent/receipt.json

Both receipts reproduce. No Lean, build, staging or reviewed-source mutation
was performed.
