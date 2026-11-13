# Scaled-square extraction in IΣ₁ models

This exploratory module formalizes the rational-square step needed by the separate ten-positive doubled product-square proposal. It proves the following in an arbitrary `IΣ₁` model with the repository's `ORingStructure` interface, without prime factorization, unique-factorization assumptions, or a premise that a scale divides a numerator:

* `scaled_square_of_coprime`: from `a>0`, `m>0`, `Bez a b 1`, and `a*z²=m²*b`, obtain `a=x²` and `b=y²` for model elements `x,y`.
* `scaled_product_factor_square`: from `m>0`, `Bez G (delta*Dy) 1`, and `delta*z²=m²*(G*Dy)`, obtain `G=g²`. No positivity of `G`, `delta`, `Dy` or `z` is assumed.

The second proof takes a model gcd of `z` and `m`, uses the resulting signed Bézout certificate twice to show the reduced denominator squared divides `delta`, and applies the existing `ModelProductPell.pp_square_of_coprime` to a genuine model square. This is an abstract arithmetic component. It does not bind the 84- or 85-operation JSON graph, fixed ports or a displayed equation, nor prove a model-to-halt theorem, an iPRA derivation, or consistency.

The guarded author attempt 04 exited 0 and printed `[propext, Classical.choice, Quot.sound]` for both theorems; its snapshot, logs, hashes and sampled resources are in `observations/attempt04/`. The current source SHA-256 is `ef223f29e93d9cae39fa58b58a996299a3e4df219801b990cb6ee50cd6e1608a`; the compiled object SHA-256 is `37ce988b94587130947097a868dd153f5564718dd280fafe6fd3b75aa2028691`. Attempt 01 exited 1 due to an extra tactic after a goal had closed; attempt 02 checked the first theorem only. Attempt 03 exited 1 with unsuccessful rewrites and `sorryAx` in the incomplete second theorem; its diagnostics are retained and are not evidence for the theorem. Attempt 04 resolved these issues and checked both.

`run.py` pins its source, runner, Lean executable and direct `ModelProductPell.olean` before and after, on the selected 90-operation author-join provider. The full project union, package-transitive and dynamically loaded dependencies and historical source-to-object ancestry are inherited, not independently rebuilt here. Resource observations are point samples. The `/tmp` provider and object may disappear; this is not a paired or independent replay.

Run from the repository root with a fresh name and free guarded Lean slot: `ATTEMPT=attempt05 python3 -I -S -B Computability/DiophantineConsistency/research/ten-positive-ipra-scaled-square-prototype/run.py`.
