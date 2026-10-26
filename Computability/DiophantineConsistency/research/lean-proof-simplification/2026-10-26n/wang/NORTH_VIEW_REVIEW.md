# Index the new north-boundary classification by its color

Source pin: `b310142330df89e48413c8fce62e7de223e1c7d5`. This is an **uncompiled proposal**, not an accepted replacement.

The new `WangTiles942Boundary` module was introduced in commit `9cef0257dde4` during the reviewed interval. Its `high_north_cases` theorem already separates the six possible high-north tile shapes. Five following iff theorems each repeat the same six-way elimination and discard numerically impossible branches:

- `north_435_iff_start`, lines 76–84;
- `north_434_iff_initLeft`, lines 86–96;
- `north_436_iff_initializers`, lines 99–110;
- `north_438_iff_reset`, lines 112–125;
- `north_437_iff_seam`, lines 127–140.

[Read the exact pinned source](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Boundary.lean#L76-L140).

## Proposal

Define a small Prop-valued function `NorthView n t` by the literal north color:
434 gives the left initializer, 435 gives Start, 436 gives the two initializers,
437 gives the nine seam shapes, and 438 gives the three reset shapes. Its default
case is False. Prove `NorthView t.north t` once from `Allowed t` and the existing
`434 ≤ t.north` hypothesis using `high_north_cases`. This helper performs only
six cases, not an enumeration of all 942 indices.

The forward direction of every existing classification then has the same body:

    intro hn
    simpa only [hn, NorthView] using north_view ht (by omega)

The reverse direction stays its existing reflexive constructor proof. The
complete helper and five replacement theorems appear in `NorthViewCandidates.lean`.
They do not use any of the five target classification theorems to prove their
replacements. They use only the earlier independently proved high-north case
lemma.

## Preservation and tradeoffs

All five public assumptions and conclusions remain unchanged. The lower bound
on the helper is derived from the queried color, not added to an original
statement. Color 436 retains **both** initializers and the head initializer's
south color 4. The reset parameters remain restricted to `[434,435,436]`; seam
parameters remain `Fin 3`. Neither tile occupation, a unique Start, periodicity,
nor machine semantics is assumed. The literal `Allowed` language and tile table
are unchanged.

Measured nonblank code lines for the five old declarations are 9, 11, 12, 14,
and 14, totaling 60. The new wrappers use 34 lines and the two shared declarations
use 18, totaling 52. Thus the measured experiment saves only **8 lines** after
helper overhead; imports, comments and axiom-audit commands are excluded equally.
The principal benefit is one maintenance site for the color-to-shape result,
not a large compression claim. A new helper is not worthwhile if the five
classifications are unlikely to change or if the extra indirection obscures
local reading. Kernel-term size and elaboration cost remain unmeasured.

This representation is a semantic view of an already proved case distinction,
not a new data generator or a proof obtained by redefining the source table.
Keep the old named iff theorems as the public API. Do not globally mark the whole
view or high-north theorem as a simp rule; use the focused closed-color rewrite
at these five call sites.

## Novelty boundary and validation

The six audited prior packets contain Wang table chunk-dispatch and general
control-layout ideas, but no color-indexed view of this newly added high-north
classification. This proposal is scoped to the new five-theorem family, not a
renewed proposal to redesign all finite tables. See the incoming audit's exact
novelty decisions.

Before adoption, compile the helper and all five candidates under the pinned
Lean 4.32.0 project, compare their exported statement types, audit their axiom
sets, and rebuild the seam/initial-horizontal consumers. The source-text count
and ordinary reasoning here do not establish successful elaboration.
