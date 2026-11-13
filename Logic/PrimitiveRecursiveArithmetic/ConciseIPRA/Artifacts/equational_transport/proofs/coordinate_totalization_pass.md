# Final focused pass: alternative depth offsets and junk syntax

No smaller complete bi-interpretable presentation was established in this pass.

## Concrete candidate tested mathematically

The proposed saving was to replace the uniform child-depth update

    d + 5 - len(a)

by `d - len(a)` or `d + 3 - len(a)`, possibly reversing the numerical order of free-parameter coordinates.

For the existing proper grammar, the arities are D=1, Eq=2, I=3, S=1. The existing update gives increments 4,3,2,4. The four-unit D increment reserves two numerical binding coordinates, the two-unit iterator increment reserves its state variable, and the parity of the three-unit equation increment switches formula to term positions. Some extra slots are deliberately protected; they are not all ordinary variables.

The substitution `5 -> 3` makes the iterator increment zero. Along an arbitrarily deep chain of iterator bodies the traversal then keeps the same depth threshold. Two successive iterator state variables cannot both have distinct locally addressable binding coordinates compatible with that same opener: the inner binding must protect its variable from substitution for the outer one, while an identical depth threshold cannot distinguish them. The public-variable scheme therefore needs an extra shifting/tagging mechanism. The original no-capture opening lemma does not survive this replacement.

Reversing the order of every numerical coordinate coherently, by a'=-a and d'=-d, sends the update to

    d' + len(a) - 5,

not to `d' - len(a)`. The retained-variable comparisons must also be reversed. This is a valid coordinate reflection in principle, but it does not remove the constant or shorten the arithmetic expression.

The pure `-len(a)` profile is a different allocation: D would move by one slot while binding two numerical variables, whereas I would move by three while binding one. Reversing the interval direction does not repair the too-small D block in the current integer-slot representation. Repeated D binders need two distinct accessible numerical coordinates per layer; a one-slot layer cannot maintain that representation without an additional encoding track, fractional coordinates, or a different binder. Those changes require a new opening operation and proof, rather than the proposed deletion.

These are obstructions to the specified simple rewrites of this opener, not a lower bound on arbitrary encodings.

## A meaningful alternative that remains unimplemented

A `3 - len(a)` depth scheme could be natural for a genuinely different grammar: D as one child binding two variables, equality as three children with no binding, and a two-child register iterator J binding one state variable. The article already supplies mathematical register-iterator presentations without a separate initializer. Their arithmetic update must distinguish increment from loading a value, or impose a syntactic guard on update bodies. Thus the desired syntactic saving moves a new obligation into computation. No complete checker below the existing frontier was obtained, and it would be incorrect to quote the shorter walker alone as an improvement.

## Why simply admitting junk does not supply the missing proof

The compact baseline already excludes a full public-grammar validator from its measured program. Admitting additional raw arrays therefore does not remove that code from the measured checker.

A proposed total decoder can map an invalid-arity term to 0 and an invalid formula to truth, but soundness in that chosen reading is insufficient for bi-interpretability. Its opposite formula roundtrip would require, for example, a derivation identifying every junk term with 0. The current raw computation rules generate equations headed by the designated iterator constructor, and they do not automatically identify an unrelated extra constructor or constant with 0. Treating the decoder's result as definitional identity instead adds a normalization/quotient operation, whose computation must be part of the complete checking contract.

Moreover tests based on syntactic shape, such as identical copies or guarded matrices, need a substitution-coherence proof for the decoder. Distinct raw children can become identical after substitution, so erasing only the originally noncanonical node need not commute with substitution. Restricting erasure to arity alone avoids that particular collision, but does not establish the missing theorem and formula roundtrips.

Consequently I found no justified route from untyped totalization to an executable checker below 461 normalized bytes, 239 significant tokens, and 256 AST nodes. The proved one-term equality restriction should be reported as a mathematical result with its measured implementation, without a frontier claim.
