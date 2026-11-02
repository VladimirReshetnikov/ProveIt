# Independent standard-length structured mask audit

The read-only [audit](audit.py) of `0f06df0a20` actually exited 0 in session
30574; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/object/log chains, both complete successor project
object overlays, direct imports, recorded child and outer exits, and a
successful rerun of the independent 684-row parent audit. Both logs contain
the three expected axiom reports with Lean metatheory `propext`,
`Classical.choice`, and `Quot.sound`, without warnings or `sorryAx`. No Lean
compile was rerun for this review.

The source constructs, in any IΣ₁ model, a structured radix-`2^67` block
for an arbitrary model support word. `standard_blocks_exists` uses **external
Lean induction on a standard natural length**, and its 8,807 specialization
supplies the three-way digit classification; the origin digit is `2^67−2`
under the explicit hypothesis that the support's zeroth bit is 1. The
support word is a parameter. Neither equality to the retained MC literal nor
an internally formalized PRA construction follows from this existence proof.
The graph's no-carry premise, coefficient bounds, machine simulation and
consistency equivalence remain separate.

The source packet retains three failed exploratory attempts and two later
successful attempts. The inherited Foundation outer-wrapper exit and full
package-transitive/dynamic ancestry remain outside the provider audit;
resource measurements are samples rather than hard whole-tree quotas.
