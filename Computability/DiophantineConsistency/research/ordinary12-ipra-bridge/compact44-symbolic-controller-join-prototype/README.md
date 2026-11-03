# Prepared same-provider symbolic controller unit join

This is **uncompiled preparation**. The two successful earlier results use
different provider objects, including different `ArithmeticPow`,
`ArithmeticStandardCasts`, `ArithmeticPackingBlocks`, and
`ArithmeticWindowDigits` hashes. The present draft does not combine those
already-built objects or establish a unit theorem.

The proposed author-side build chooses the symbolic-kernel provider
`/tmp/compact44-k-radix-cert-01/lib`, reuses its existing project and package
objects, and rebuilds these sources in order on one overlay:

1. `Lean/DiophantineConsistency/ArithmeticControllerLift.lean`, importing
   that provider's `ArithmeticPow` and `ArithmeticModularCancellation`.
2. The compact controller data source, importing the rebuilt lift together
   with that provider's `ArithmeticStandardCasts` and
   `ArithmeticPackingBlocks`.
3. The conditional compact controller unit source, importing the rebuilt
   compact data.
4. The symbolic kernel residue source, importing that provider's
   `CompactSymbolicKernelOpaque` and using the same symbolic arithmetic
   objects.
5. `CompactSymbolicControllerJoin-DRAFT.lean`, which applies
   `gamma_unit_nat` to exactly `paramKernel rho` using `symbolic_kernel_mod`.

The runner creates an isolated overlay and copied source snapshot, checks for
direct shadowing of the five new modules, records selected base-object and
source hashes, dependency listings, stage logs and actual exits, and refuses
to overwrite an earlier attempt. It enforces a 3,000 MB Lean limit and
180-second timeout per compilation. The earlier compact data source has a
documented linter warning; all output must be inspected before describing any
successful run. The runner does not authenticate the inherited package,
transitive or dynamic dependency closure, protect against all between-check
mutations, or provide a second independent build.

Neither the client nor the runner has been executed. If compiled, the joined
theorem would still be a model-level controller unit only; it would not prove
retained-byte/display binding, the actual rank-variation identity, safe dummy
locations, a positive graph zero, or an iPRA derivation.
