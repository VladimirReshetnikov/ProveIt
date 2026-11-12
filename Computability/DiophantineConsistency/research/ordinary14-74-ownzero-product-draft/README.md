# Literal 74 own-zero signed-product extraction — source draft

This source-only client rewrites the literal 74 graph's own `InternalZero`
using its exact output shape, then uses signed-pair evaluation to extract the
product-equivalent-to-one statement. It switches the last two factors by an
explicit commutative signed-pair identity so the guard is the unrestricted
fourth factor. A second proposed theorem composes this with the literal first
factor client and its internal `m≥2` bound.

The main, auxiliary and strong negative-unit residue exclusions remain
explicit hypotheses, as do the positive beta/J/w/s and beta-port cast. This
file does not derive them from the literal graph, establish guard strictness,
prove 74↔75 or a model/iPRA endpoint, or verify providers. All imported drafts
and tactics are unelaborated; no Lean, byte or PDF claim is made.

Independent source review: [74 own-zero product](../../reviews/ordinary14-74-ownzero-product-independent/README.md).
