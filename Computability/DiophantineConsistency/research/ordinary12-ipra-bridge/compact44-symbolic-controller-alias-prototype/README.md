# Prepared staged symbolic controller alias

The explicit equality-transport alias module has compiled successfully. The
alias-unit client failed kernel checking; the actual-symbol controller client
has not been run. The preceding same-provider join
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

The first bounded alias build exited 1 at `kernelAlias_mod` with recursion
exhaustion after reducing the large symbolic kernel. A second attempt added
local irreducibility and a higher recursion limit; it exited 1 at that same
declaration with excessive kernel memory consumption. Both logs show the
preceding `kernelAlias_eq` declaration and its printed axioms, but no complete
alias module or unit theorem resulted. The second failure's printed
`kernelAlias_mod` self-reference is error recovery, not a proof. Exact sources,
outputs and terminal receipts are retained in `observations/` and
`observations02/`.
`KernelAliasExplicit.lean` uses explicit equality transport and the imported
`Modulus` abbreviation instead of `rw` for the residue. It compiled on the
same provider in 2.13 seconds, exit 0, without warnings. Both
`kernelAlias_eq` and `kernelAlias_mod` print only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`. Its retained
source is byte-for-byte the successful input, so its opening draft comment is
historical. The logs and terminal receipt are in `observations03/`.
A separate attempt to apply `gamma_unit_nat` to the checked alias and residue
exited 1 with excessive kernel memory use, and did not run the subsequent
actual-symbol client. Its source and output are in `observations04/`; the
printed self-reference for the failed theorem is error recovery, not a proof.

The runners reuse and hash-check the four earlier same-provider
objects, builds the three sources sequentially, and retains each stage's
source hash, dependency listing, compiler output and exit. The two initial
attempts stopped at the first stage; the explicit-transport alias is proved,
but its attempted controller client failed. The inherited project/package/transitive provenance remains as
limited as in the earlier attempt. Neither a successful alias nor a successful
actual-symbol theorem would by itself connect retained bytes, rank variation,
dummy locations, graph zero or iPRA provability.
