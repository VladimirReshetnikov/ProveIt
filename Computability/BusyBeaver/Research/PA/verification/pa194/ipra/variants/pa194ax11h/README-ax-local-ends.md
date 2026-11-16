# AX dispatch and gate output

`PA194AX11HAXDispatch.dispatch` proves the candidate's two opcode decrements take site 48 to site 50 with label `k`, when register 3 initially equals `k + 1 + 1`. It returns the exact full source file with only that register updated.

`PA194AX11HGateMeaning.gate_to_frame_ax` identifies the gate-stage result pushed onto the stack with the intended `axTop`, under the explicit premise that the preceding AX body supplied `oldBundleValue` in register 1. It strengthens the independently replayed positive-time 3519→25 gate and tail theorem. The body 50→3519 and its production of that premise, as well as the full scheduler and literal-machine correspondence, remain separate obligations. Both results hold in PRA models with IΣ₁ on the arithmetic reduct.

From the repository root, after replaying the gate-decoded and MP-command stages:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-ax-local-ends.sh /dev/shm/pa194-ax11h-ax-local-ends-repo /dev/shm/pa194-ax11h-gate-decoded-repo /dev/shm/pa194-ax11h-mp-command-repo
```

The output must be fresh. The checker records source and direct prerequisite hashes and retains the prerequisite stages' transitive prebuilt objects; it rejects `sorryAx` and reports Lean axioms.
