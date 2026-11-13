# High-digit bound: list-association correction draft

The separately retained v3 check failed its `high_split` proof with a residual equality differing only by cons/append association; its axiom report consequently contained `sorryAx`. This source-only v4 adds `List.cons_append` to that proof's existing `simp only` list. It preserves the named tail, high recipe, all theorem statements, and positivity argument.

This draft is uncompiled and requires source review, a pinned runner and a separate guarded check. No high bound, cover or graph conclusion is asserted.

The [independent factual and source review](../../reviews/trace74-high-digit-v3-failure-v4-draft-independent/README.md) confirms the v3 failure and found no mathematical blocker in this one-lemma draft change. No Lean check was performed by that review.
