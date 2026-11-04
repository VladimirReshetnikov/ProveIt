# High-digit bound: named-tail source draft

The separately retained v2 attempt failed with Lean's recursion-depth error at the explicit long-tail `change`; its axiom report contains `sorryAx` and no theorem was accepted. This unchecked v3 names the long list `highTail`, defines the same suffix as `mu :: highTail`, and uses that name in the positivity `change`. The high recipe, index, base and claimed theorem remain the same; the separate `high_split` normalization unfolds the named tail.

The precise reduction cost of the revised `high_split` or subsequent proof is unknown. This source requires independent review, a fresh pinned runner and a guarded check; no high bound, cover, model-cast or graph conclusion is claimed.

The [independent factual and source review](../../reviews/trace74-high-digit-failures-v3-draft-independent/README.md) confirms both prior failed outcomes and found no mathematical blocker in this uncompiled draft. Elaboration, resource use and warning-free acceptance remain to be checked.
