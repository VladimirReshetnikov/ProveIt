# Category and model-theory source audit

Repository: VladimirReshetnikov/ProveIt; pinned commit `5f3be02388442f16487d2dc5c2529961dd783d2b`.

This supplement consolidates the category/model contributor's recorded source inspection. It is not a complete repository audit and does not claim that upstream modules were rebuilt. Historical packet status and current source status are kept separate.

## [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/PresentedCategory.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/PresentedCategory.lean)

Git blob: `af67b99aeadcd36259e15845843c5e8b563691e4`.

`Pres` has formula-level `Obj`, `Hom`, `Eqv`, terms for identities/composition. `Pres.Laws` supplies actual iPRA proof rules. `inverse_unique_closed`, `section_monic`, `retraction_epic`, `monic_split`, `terminal_unique` are supplied derivations. Predicates need not be decidable.

## [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/SetoidInterpretation.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/SetoidInterpretation.lean)

Git blob: `fb795d252a029eb68698b0e3f7378251a6a63a23`.

relativized numerical sort interpretation with domain and equality formulas; `Presentation`, `tr`, `tr_subst`, `cong`, `sound`. It already transports first-order proofs when interpreted axioms/closure/congruence are supplied. We do not repackage it as a new theorem.

## [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/Yoneda.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/Yoneda.lean)

Git blob: `6c944e39aaf0a3aaa54d445a7d93bc2cf5758013`.

presented contravariant families and specified natural transformations, no universe of arbitrary functions.

## [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/UniversalEvaluatorObstruction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/UniversalEvaluatorObstruction.lean)

Git blob: `0b0989b6e2e2cf9cc91a6b835ccea88ba465264a`.

must retain the distinction between fixed PR operations and a nonexistent universal PR evaluator.

## [Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/README.md](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/README.md)

Git blob: `6dbd3c6204744d2cb19269d386e11fe68c83422a`.

packet develops presented categories, finite functor categories, Yoneda, finite limits/colimits/exponentials, adjunction and Kan calculations, finite gluing and bounded coherent lifts. Packet itself says its Lean source uncompiled (historical snapshot `bb86091690bc4f920f046a37cfc87719299b4019`). Current Derivations must not be confused with that historical packet status.

## [Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/04_categories.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/04_categories.tex)

Git blob: `c4690f44f0db27207a6595fcfe2f4ddb4d24e56a`.

ordinary finite category theory already broad, so new section focuses on continuous completion and compact metric semantics.

## [Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/07_obstacles.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/07_obstacles.tex)

Git blob: `f5e3fdd3302e54f0faec388bf0aae1981a784b36`.

decidable thin groupoids with at most two classes do not uniformly admit finite representative lists, via halting. Positive cover data is essential.

## Primary source and scope

Itaï Ben Yaacov, Alexander Berenstein, C. Ward Henson, and Alexander Usvyatsov, *Model theory for metric structures*, in *Model Theory with Applications to Algebra and Analysis*, vol. 2, London Mathematical Society Lecture Note Series 350, Cambridge University Press, 2008, pp. 315–427. DOI: https://doi.org/10.1017/CBO9780511735219.011 . Author manuscript: https://math.univ-lyon1.fr/~begnac/articles/mtfms.pdf .

The contributor inspected the author manuscript, including Sections 2–3 on bounded metric structures, fixed symbol moduli, [0,1]-valued predicates, and inf/sup semantics. The report uses this as background and proves its finite quantitative assertions separately. It imports no general logical compactness, saturation, ultrafilter, or arbitrary-model existence theorem into iPRA.
