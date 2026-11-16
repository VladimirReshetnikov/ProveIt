# AX11H source body

This stage transports the existing primary 251-operation AX plan to the candidate source. The bounded-window execution lemmas establish the push, three copy operations, increment, two reads, and implication constructor. They apply to any transition code agreeing with the primary source on the required site window; in particular, they do not assume agreement at the changed dispatch rows 48 and 49.

`PA194AX11HBodyAll.body` proves the candidate's exact site 50→3519 execution with zero scratch registers. `PA194AX11HBodyToFrame.body_to_frame` composes it with the candidate gate and tail to reach the exact next site-25 frame in positive model-valued time. Both explicitly assume `BodyRowsAgree`, the finite statement that candidate and primary source instructions match at every site 50–3518. The separate row-binding stage must establish that premise. These are PRA-model theorems with IΣ₁ on the arithmetic reduct; the full scheduler and literal-machine equivalences are separate.

From the repository root, with previously source-replayed prerequisites:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/body-proof/check.sh /dev/shm/pa194-ax11h-body-proof-repo /dev/shm/pa194-ax11h-candidate-gate-repo /dev/shm/pa194-ax11h-compare-return-repo /dev/shm/pa194-ax11h-ax-local-ends-repo /dev/shm/pa194-ax-controller-repo
```

The output must be fresh. The checker records the source and named direct prerequisite hashes. It retains the staged prerequisite `leanpath.txt` entries, including their prebuilt transitive dependencies; consult those stages for their provenance. It rejects `sorryAx` and reports Lean axioms.
