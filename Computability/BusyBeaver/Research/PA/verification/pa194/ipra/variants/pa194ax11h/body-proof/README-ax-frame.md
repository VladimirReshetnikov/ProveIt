# AX11H concrete AX scheduler command

`PA194AX11HAXSchedulerFields.nextFields` evaluates the AX branch of `stepK .top true`, including the fourth stream field and the pushed gate. `PA194AX11HAXFrame.advance` composes source fetch/decode, AX dispatch, the source body, gate and revised tail, and those scheduler fields. For each PRA model whose arithmetic reduct satisfies IΣ₁, and each scheduler state with command tag `(c+1)+1`, it reaches the next concrete scheduler frame in positive model-valued time.

The frame theorem explicitly assumes `BodyRowsAgree` for source sites 50–3518. The separate finite row-binding stage must prove that premise. This is a source-command theorem; the literal-machine binding and full consistency equivalence are separate.

From the repository root, after replaying the body, fetch, AX-local, and scheduler-core stages:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/body-proof/check-ax-frame.sh /dev/shm/pa194-ax11h-ax-frame-repo /dev/shm/pa194-ax11h-body-proof-repo /dev/shm/pa194-ax11h-mp-frame-repo /dev/shm/pa194-ax11h-ax-local-ends-repo /dev/shm/pa194-scheduler-core-repo /dev/shm/pa194-ax11h-controller-scheduler-replay /dev/shm/pa194-scheduler-source-frame-repo-v4
```

The output must be fresh. The checker hashes its sources and named direct prerequisite objects, and retains the staged transitive objects listed in the prerequisite `leanpath.txt` files. It rejects `sorryAx` and reports Lean axioms.
