# AX11H gate with arbitrary stream contents

`PA194AX11HGateDecoded.gate_to_frame` removes the explicit stream-pair hypothesis from `PA194AX11HGateToFrame.gate_to_frame`. For every input file with registers 6 and 7 zero, the source executes from site 3519 to site 25 in positive model-valued time. The output frame has top zero, pushes the gate-stage result from register 1 onto the previous stack, takes the next data field and continuation from the first and second projections of register 8, and clears the other scratch fields. The theorem retains the same PRA-model and IΣ₁ assumptions and does not prove the preceding AX body or the literal-machine connection.

From the repository root, after replaying `check-gate-frame.sh`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-gate-decoded.sh /dev/shm/pa194-ax11h-gate-decoded-repo /dev/shm/pa194-ax11h-gate-frame-repo
```

The output must be fresh. The checker hashes the source and direct gate-frame object and retains the gate stage's transitive `leanpath.txt`; it rejects `sorryAx` and reports Lean axioms.
