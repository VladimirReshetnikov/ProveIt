# Independent review of reverse map and conditional iPRA client

The proposed reverse coordinate map and the conditional endpoint have the
correct mathematical and source-level directions; no concrete mismatch was
found. Both are unelaborated, their imported drafts are prospective, and the
endpoint still has both all-model zero maps as explicit hypotheses.

## Reverse map

The graph-bounds client proposes a positive model-natural m with
`(ι m)²=(V+y_child)²` at the same child valuation. Replacing slot 12 by
`m−1` and then applying the positive shift gives m because `m>0` implies
`1<=m` and `(m−1)+1=m`. All other shifted coordinates are unchanged.
The parent graph reads y directly only in `y*y`; hence its whole output
is invariant when that coordinate is replaced by another element with the
same square. This is the scope of `parent_eval_update_same_square`.

The proposed literal identity equates the child evaluation with the parent
at the signed shear `V+y_child`. Applying whole-output square invariance
with `(ι m)²=(V+y_child)²` yields the parent evaluation at the new shifted
valuation; the two `InternalZero` conversions then point from the child
zero to the parent zero. The current beta positivity and positive-shifted
coordinates are passed to the graph-bounds client. The checker independently
exercises 100 bounded full-graph replacements, including 16 with a negative
signed ordinate; these controls do not establish arbitrary-model extraction,
Lean simplification, the JSON-to-source relation or provider provenance.

## Conditional endpoint directions

`SameNoZero child parent` means child no-zero iff parent no-zero. For the
forward implication, a hypothetical parent zero is mapped by `ParentToChild`
to a forbidden child zero; for the reverse, `ChildToParent` maps a child zero
to a forbidden parent zero. The source uses these maps in those directions,
without requiring the two witnesses to be equal. The pinned bridge theorem
has signature `SameNoZero e f -> PolynomialBridge f -> PolynomialBridge e`,
so applying it to child, parent and the 71 parent bridge is correct.

The native theorem uses `equivalence_of_bridge`; the standard theorem uses
the reverse implication of `standardTheory ⊢ φ ↔ nativeTheory ⊢ φ`. For the
translated endpoint, the pinned `zfcEquiv` has direction translated-source
iff negated mapped refutation; the two proposed entailment compositions
produce child-no-zero iff translated-source in the same order as the selected
71 client. These are source-level conditional derivability statements, not
proofs of consistency, of the maps, or of a 72/46 theorem.

The magnitude, graph bounds, literal evaluators, forward and reverse maps,
cast and provider selection, tactic behavior, axiom reports and downstream
object-theory encoding all require a coherent Lean replay. The parent
historical endpoint retains its own provenance limits. No PDF semantics or
degree/minimality conclusion is established here.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-reverse-coordinate-map-draft/check.py | cmp - research/current2011-shear-reverse-coordinate-map-draft/result.json
    timeout 30s python3 -I -S -B research/current2011-shear72-conditional-ipra-endpoint-draft/check.py | cmp - research/current2011-shear72-conditional-ipra-endpoint-draft/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-reverse-map-conditional-endpoint-independent/check.py | cmp - reviews/current2011-shear-reverse-map-conditional-endpoint-independent/receipt.json

All receipts reproduce. No Lean, build, staging or reviewed-source edit was
performed.
