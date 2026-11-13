# Cast-based finite seed model facts draft

This uncompiled draft proposes to choose model `W` and `S` as the natural casts of `2^30` and the certified finite seed and prove the eight remaining assumptions of the [conditional seed specialization](../trace74-boundary-seed-specialization-rebuild/README.md): W/S positivity, source X/Y identities, the first-base subtraction cast, phase, exponential and growth. It proposes to transport small and finite natural facts using standard cast lemmas, without computing the 14k-bit Pell ordinates in the model.

This source contains no graph-zero theorem and has not been checked by Lean. Its implicit instances, imported provider compatibility, natural cast simplifications, finite arithmetic and resource behavior all remain to be verified. No model assumption is treated as discharged and no unconditional zero or fixed BFS tuple result is claimed.

The [independent source review](../../reviews/trace74-boundary-seed-model-facts-draft-independent/README.md) checked the eight target conditions and proposed cast/positivity route. Its scope does not include Lean elaboration, resource behavior or a zero theorem.
