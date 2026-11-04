# High-digit bound: empty-append correction draft

The separately retained v4 check failed with a remaining `[] ++ tail = tail` normalization and reported an unused `List.singleton_append` simp argument; its axiom report consequently contained `sorryAx`. This source-only v5 removes the unused argument and adds `List.nil_append` to the `high_split` simplifier. The theorem statements, named tail, high recipe and other proof steps are unchanged.

This draft is uncompiled and requires independent source review, a pinned runner and a guarded check. No high bound, concrete cover or graph conclusion is asserted.

The [independent factual and source review](../../reviews/trace74-high-digit-v4-failure-v5-draft-independent/README.md) confirms the v4 failure and found no mathematical blocker in this draft. No Lean check was performed by that review.
