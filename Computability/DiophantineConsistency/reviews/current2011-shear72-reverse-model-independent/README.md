# Independent review of the two reverse model-magnitude drafts

The source-level interfaces and the mathematical magnitude argument match;
no concrete discrepancy was found. Both drafts and their prospective logical
imports remain unelaborated, so this review does not establish a Lean model
map, a provider closure, or an iPRA endpoint.

The existing source `ZRowsCoprimeSquares.abs_eq_ι` states, with the needed
orientation, that every `z : DiffRing V` has `|z|=ι n` for some model
natural `n`. For nonzero z, `|z|` is nonzero, hence n is nonzero and
positive; squaring gives `(ι n)²=z²`. The draft's `positive_magnitude`
uses that direction and its proposed rewrite is consistent with it. The
source `ModelDifferenceRing.ι_le_ι` has the direction needed to transport
`1<=y` into the difference ring. The `sq_abs`, cast simplification and
typeclass elaboration themselves were not tested.

The generic client instantiates the prior conditional nonzero lemma with
`rest=P²+(QW−1)²`, then applies the magnitude and same-square auxiliary
lemmas to exactly `Vr+ι y`. Its explicit `A>=0`, `I>=2` and natural `y>=1`
assumptions are passed in the right order; the sphere equality is reordered
by a proposed `linarith`. The older model-specific client instead derives
`I>=2` and `A=0 or A>=2` from explicit natural bounds `d,f,i>=1` and
`c>=2`, distinguishing f=1 from f>1 using natural discreteness. Both
approaches are conditional on their displayed zero equation.

The parent literal has exactly one direct occurrence of y, the row `y2=y*y`;
therefore replacing only y by any representative with the same square leaves
all downstream parent values unchanged. The candidate uses y in exactly the
sheared ordinate and product rows. The independent checker verifies these
source dependencies and runs 78 finite controls with nonzero signed
ordinates, comparing the complete candidate value with the parent value after
absolute-value replacement. Such finite checks do not prove the graph-to-Lean
AST binding or an all-model zero map.

The candidate's literal model evaluator, a derivation of the fact-level sphere
identity and its bounds from its actual zero, positive model-natural coordinate
replacement and same-valuation transport are still separate proof steps. So
are the forward map, all-model bridge, and endpoint transfer. The two
`DiophantineConsistency.ShearNonzero` and
`DiophantineConsistency.Shear72ReverseMagnitude` imports in the generic
client are prospective names, not authenticated built providers. `#print
axioms` commands in a source file are not reports until run and checked.

Reproduce all three bounded receipts from `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear72-reverse-magnitude-draft/check.py | cmp - research/current2011-shear72-reverse-magnitude-draft/receipt.json
    timeout 30s python3 -I -S -B research/current2011-shear72-reverse-generic-model-draft/check.py | cmp - research/current2011-shear72-reverse-generic-model-draft/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear72-reverse-model-independent/check.py | cmp - reviews/current2011-shear72-reverse-model-independent/receipt.json

No Lean process, build, staging or historical-file mutation was performed.
