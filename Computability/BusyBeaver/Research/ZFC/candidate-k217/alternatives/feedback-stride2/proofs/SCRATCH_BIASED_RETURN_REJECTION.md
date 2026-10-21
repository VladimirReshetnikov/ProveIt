# Independent rejection of the scratch-biased 215-state source

## Verdict

The proposed scheduler calibration does not apply to the actual source. The received source has a control-depth error, and its first AX completion is followed by an unconditional halt. A complete physical primitive certificate is compatible with this result: it faithfully implements the wrong source.

This finding concerns the research-only `scratch-biased` experiment, not the separately calibrated MP-first transfer table.

## Exact artifact

Source SHA-256: `2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a`.

Native machine SHA-256: `f08bed9e62b9f43237b65c465d2f1bfc17474637b4b02785ca7f1813827bb0ce`.

The source has 4,733 leaves. Its inserted CI6 is ordinal 4696 at address `100110`; its following CC3 is ordinal 4697 at `100111`.

## Control error

A CCk instruction continues at the ancestor obtained by deleting the last k right edges. Before insertion, CC3 was at `10011`. Its third right edge from the end is the first edge, so its target was the root, source ordinal 0.

After insertion, the address is `100111`. Its right-edge positions are 0, 3, 4, 5. The third from the end is position 3. Thus its target is prefix `100`, whose first leaf is ordinal 23, CD3. It does not return to the scheduler.

The source transformation would require CC4, not CC3, if the intention were to retain the old return target while adding CI6. Such a correction requires a new physical implementation proof; changing prose or the claimed abstract scheduler does not correct this table.

## Exact halting suffix

Let the registers at ordinal 4696 satisfy A=H=X=Y=0, where A is logical register 3, H register 5, X register 6 and Y register 7. Let the top register T=t be any natural number. All other registers can be arbitrary.

1. CI6 sets X=1.
2. CC3 jumps to ordinal 23. CD3 sees A=0 and enters ordinal 4698, the clear-top loop.
3. The clear-top loop consumes all t units and exits at ordinal 4700 after 2t loop steps plus its final zero test.
4. The cache-copy loop sees H=0 and performs no copying. Its restoration loop nevertheless consumes the existing X=1, incrementing H once. It exits with T=0, H=1, X=0.
5. The inherited NIP comparator initializes X to 1, compares H with 1, and takes the halt leaf at ordinal 4718.

The exact number of source transitions from ordinal 4696 to the halt leaf is 2t+15. An owned independent prefix-interval CFG resolver records the full t=0 trace and checks additional t values in `RETURN_TARGET_COUNTEREXAMPLE.json`. The universal argument is the direct loop invariant above, not the finite tests.

## Application to the actual blank startup

The independently reproduced blank startup reaches source ordinal 64 during AX, and the complete register state agrees with the 172-step source prefix from ordinal 25 with seed

    (N,T,W,A,D,H,X,Y,L) = (1,0,3,0,0,0,0,0,0).

The entire AX body, ordinal 25 through its exit at 4589, retains the inherited arithmetic/command body. In particular its primitive word and internal/exiting CFG agree with the parent; its final CB1 exits to ordinal 4696. The inherited terminating AX contract gives A=H=X=Y=0 on this return. For this seed U=A=B=C=0, the gate is disabled and T=0. Consequently the source reaches its halt after 15 additional primitive transitions beyond AX completion.

The all-natural binary-runtime theorem and exact whole-tape blank bridge therefore imply that the binary machine also halts. No enormous literal simulation of the AX arithmetic is needed: the inherited terminating arithmetic contracts and the universally quantified physical simulation suffice.

The observed initial stack is indeed entirely safe: 3=P(2,0), and 2=Q_0(0) is a theorem. This valid observation cannot rescue the machine because the inserted scratch value is incorrectly restored into the formula cache before the halt test, creating raw cache 1 without a logical inference.

## What remains useful

The adjacent-pair cofinality argument may be correct for an abstract scheduler whose first-field bias is the previous command's 0/1 flag. It must be attached to a source that actually implements those equations. The existing literal source does not. A repaired CC4 implementation or another return sequence can reuse the mathematical idea only after fresh source and physical checks.
