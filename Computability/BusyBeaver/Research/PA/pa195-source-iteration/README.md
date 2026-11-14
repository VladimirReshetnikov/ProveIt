# Conditional PA195 source-to-parent iteration

These modules adapt the upstream PA196 runtime-contract,
primitive-instruction, and compiler-correctness proofs to the exact unfolded
PA195 parent machine. `PA195CompilerCorrectness.source_nonhalt_to_physical`
proves that, given its explicitly stated `Coverage` premise, nonhalting of
any specified source configuration implies nonhalting of the corresponding
physical parent frame. It handles arbitrary valid full register files, all
gap parameters, and indefinitely many source steps through a positive
invariant.

The `Coverage` premise requires a checked implementation for every source
instruction. The direct per-site tests in `../pa195-direct-coverage` are a
candidate way to supply it, but their connection to `Coverage` is not yet
proved in these modules. The theorem is an ordinary standard-Lean result,
not a theorem internal to PRA/iPRA and not a PA consistency equivalence.

For a fresh pinned-source build from the repository root, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-source-iteration/check.sh
```

The source files were checked against independently rebuilt private Lean
objects; a complete fresh run of this script can be done sequentially after
other high-memory checks. The three proof sources are adaptations of the
upstream files `PA196/RuntimeContracts.lean`, `PrimitiveSimulation.lean`,
and `CompilerCorrectness.lean`; their candidate-specific machine is
`PA195RuntimeEngine.machine`.
