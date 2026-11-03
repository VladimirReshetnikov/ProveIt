# Cast-based model facts repair draft

This uncompiled retry changes only the three proof branches that failed in the [first author check](../trace74-boundary-seed-model-facts-rebuild/README.md): explicit model identities for `1+1` and `2*2*2`, and a cast-subtraction argument via the natural subtraction/addition identity. The eight-fact statement and chosen W/S casts are unchanged. No assumption is yet discharged, no model zero is claimed, and this source awaits independent review and Lean checking.

The [independent source review](../../reviews/trace74-boundary-seed-model-facts-draft-v2-independent/README.md) verified the unchanged target and proof-branch changes; it did not run Lean.
