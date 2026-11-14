# Conditional PA194 source-to-parent iteration

These modules adapt the upstream PA196 runtime-contract,
primitive-instruction, and compiler-correctness proofs to the exact unfolded
PA194 parent machine. `PA194CompilerCorrectness.source_nonhalt_to_physical`
proves that, given its explicitly stated `Coverage` premise, nonhalting of
any specified source configuration implies nonhalting of the corresponding
physical parent frame. It handles arbitrary valid full register files, all
gap parameters, and indefinitely many source steps through a positive
invariant.

The `Coverage` premise requires a checked implementation for every source
instruction. The per-site checker in `../pa194-coverage` proves that successful tests
supply it; full coverage requires all 3,673 site checks to complete. The theorem is an ordinary standard-Lean result,
not a theorem internal to PRA/iPRA and not a PA consistency equivalence.

For a fresh pinned-source build from the repository root, run:

```sh
Computability/BusyBeaver/Research/PA/pa194-source-iteration/check.sh
```

The source files were checked against independently rebuilt private Lean
objects; a complete fresh run of this script can be done sequentially after
other high-memory checks. The three proof sources are adaptations of the
upstream files `PA196/RuntimeContracts.lean`, `PrimitiveSimulation.lean`,
and `CompilerCorrectness.lean`; their candidate-specific machine is
`PA194RuntimeEngine.machine`.
