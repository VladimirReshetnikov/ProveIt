# Lean outline: Staged Contract Kernel

The supplied files target the root ProveIt Lake workspace and the namespace
`LeanProofs.ConciseIPRA`. They deliberately use the current ordinary-iPRA
interfaces before exporting to the native scalar core.

## Files

- `StagedContractKernel/Kernel.lean`: the small proof-producing kernel. Its main
  addition is `instantiateInto` plus `NodeObligation.compile`, which normalize
  arbitrary local arities into one global parameter frame with `Prf.subst`,
  `Prf.weaken`, and `Prf.trans`.
- `StagedContractKernel/Interfaces.lean`: proof-bearing public theorem classes.
- `StagedContractKernel/Blueprint.lean`: bounded-formula, demand, viability, and
  shrinking-cloud data plus exact theorem targets in comments.
- `StagedContractKernel.lean`: umbrella import.

The files contain no `axiom`, `sorry`, or `admit`. The runtime used to prepare
this packet did not contain Lean or Lake, so no compilation claim is made. The
code was written against the interfaces inspected at ProveIt commit
`38e83bc0d09647a98ce9fe5edf45d6b34f820dff`.

The formal endpoint is always `Prf PRAAx`. A native-calculus theorem is obtained
only at the end by `pra_iff_native.mp`.
