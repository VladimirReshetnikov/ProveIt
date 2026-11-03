# Prepared staged symbolic controller alias

All three sources here are **uncompiled**. The preceding same-provider join
attempt built the two ingredients but failed when the final theorem caused
Lean to expand the huge symbolic natural; local irreducibility plus a higher
recursion limit then reached the 3 GB kernel limit. See the preserved
[join observations](../compact44-symbolic-controller-join-prototype/README.md).

This alternative separates the work into three Lean modules:

1. `KernelAlias-DRAFT.lean` introduces an irreducible natural `kernelAlias`,
   with an explicit theorem `kernelAlias_eq : kernelAlias = paramKernel rho`
   and a residue theorem derived from the previously checked symbolic residue.
2. `AliasControllerUnit-DRAFT.lean` states the model unit theorem for this
   alias and uses the conditional controller theorem.
3. `ActualControllerUnit-DRAFT.lean` states the unit theorem with the actual
   `paramKernel rho` and attempts to rewrite it using `kernelAlias_eq`.

The equality in (1) is essential: an arbitrary new coefficient would not
establish the requested result. The third module is a separate attempt because
even if the alias and its unit theorem compile, kernel elaboration of the
literal expression might still exhaust memory. Do not infer that the literal
theorem has been proved from the success of the first two stages.

The prepared runner reuses and hash-checks the four earlier same-provider
objects, builds the three sources sequentially, and retains each stage's
source hash, dependency listing, compiler output and exit. It has not been
executed, and the inherited project/package/transitive provenance remains as
limited as in the earlier attempt. Neither a successful alias nor a successful
actual-symbol theorem would by itself connect retained bytes, rank variation,
dummy locations, graph zero or iPRA provability.
