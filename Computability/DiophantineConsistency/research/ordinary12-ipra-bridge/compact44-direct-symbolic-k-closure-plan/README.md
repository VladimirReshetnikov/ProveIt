# Preliminary direct symbolic-K source closure and replay plan

This is a point-in-time source-only plan, not a paired build. The source list and pinned imports are recorded in `scan.json`, in the following topological order:

1. `Compact943Data`: imports the same-side provider's `ArithmeticWindowDigits`.
2. `CompactCoefficientMass`: imports the freshly built same-side `Compact943Data`.
3. `CompactSymbolicKernel`: imports that side's new `CompactCoefficientMass`.
4. `CompactSymbolicKernelCast`: imports the new `CompactSymbolicKernel` and the provider's `ArithmeticStandardCasts`.
5. `CompactSymbolicKernelGeneric`: imports the new `CompactSymbolicKernelCast`.
6. `CompactSymbolicKernelOpaque`: imports the new `CompactSymbolicKernelGeneric`.
7. `CompactDirectParamGraphDraft`: imports the new `CompactSymbolicKernelOpaque` and the provider's `CompactGraphDerivedRadix`.

The scanner validates exact source bytes against their own commits, exact imports, the parent audit receipt/observation, 143 matching parent objects on each side, 60 external direct companion slots, 140 empty target slots and ten package Init slots. Its normal run exited 0 and optimized execution exited 1. These are point-in-time checks: the scanner does not rerun the parent audit, authenticate complete package/transitive/dynamic ancestry, freeze sources during a build, or monitor resources.

A future reviewed driver should create fresh corresponding overlays of `/tmp/ipra-compact-graph-derived-radix-pair-01/{author,peer}/lib`, compile all seven exact sources on each side, and ensure each new direct import comes from its own side. It must rerun and compare the exact independent parent audit and this independently reviewed closure before and after; pin and freeze all source bytes; require direct objects to exist; guard output, input and companion slots before/after children and after final parent checks; reject symlink outputs, unexpected warnings or admissions; and require corresponding object/log matches. Verify the exact 17 declaration names and their individual axiom sets, as recorded in the single-side exploratory logs: per source there are 3, 8, 2, 1, 1, 1 and 1 reports respectively. These sets are not identical across all declarations. Capture actual child and outer exits and review the driver independently before launch, then review actual paired artifacts. A clean initial loader, stable HEAD, exclusive Lean slot and fresh output must be externally enforced. Compiler resource guards are sampled; dependency-query and parent-audit subprocess protections must be stated separately.

The exploratory [direct-K client](../compact44-direct-symbolic-k-prototype/README.md) assumes positive graph variables and graph zero at the *new* symbolic `directK := paramKernel rho`, then derives a positive N, radix/repunit identity and digit bounds. Its single-side seven-child run passed; this plan does not promote that run to a pair. Neither this plan nor the client proves `directK` equals the retained raw K bytes or the displayed expression's coefficient. The masks and complete tuple also need exact binding. Weighted-word/carry premises, decoder and machine semantics, the construction direction, and an internal iPRA endpoint remain separate obligations.
