# AX11H AX tail scheduler frame

`PA194AX11HAXTailFrame.ax_tail_frame` strengthens the independently checked AX fall-through: for every PRA model whose arithmetic reduct satisfies IΣ₁, it reaches source site 25 in positive model-valued time from site 3553. It assumes registers 3–7 are zero and register 8 is `cantor z l`; the exact output arguments are `![a 0, 0, cantor (a 1) (a 2), 0, z, 0, 0, 0, l, 0, 0]`, preserving the source-state tail.

This is a source tail theorem. It does not establish that execution reaches its hypotheses from the scheduler frame, nor the literal-machine or complete scheduler correspondence.

From the repository root, after running `check-ax-tail.sh` to produce the second argument:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-ax-tail-frame.sh /dev/shm/pa194-ax11h-ax-tail-frame-repo /dev/shm/pa194-ax11h-tail-repo
```

The output must not exist. The checker records source and direct prerequisite hashes; its `leanpath.txt` retains the AX-tail stage's prebuilt transitive dependencies. The audit reports Lean's axioms and rejects `sorryAx`.
