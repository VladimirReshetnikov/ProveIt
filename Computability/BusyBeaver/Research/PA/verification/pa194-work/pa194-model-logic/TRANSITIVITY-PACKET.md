# Translated transitivity under arbitrary valid packets

`transitivity_any_packet` proves that the full source theory derives the exact translated PAeq transitivity axiom for every valid `ParametersValid 0 0 param` packet in every candidate PRA + IΣ₁ model, including nonstandard models. It applies the repository-replayed fixed-axiom root supplier and the repository-replayed arbitrary internal sentence packet-independence theorem. Every guarded-compiler identity packet satisfies the packet hypothesis. There is no packet-length premise.

This supplies one fixed axiom. The other remaining fixed axioms, arbitrary internal induction instances, nonvariable existential rule, complete guarded compiler, and physical-machine synchronization are separate obligations.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-transitivity-packet.sh "$PWD" /dev/shm/pa194-transitivity-packet-repo-NEW
```

The checker rebuilds one source module and a one-report axiom audit against the repository-replayed transitivity supplier and closed-sentence bridge, plus other explicitly listed prebuilt paths. It does not rebuild the full dependency closure.
