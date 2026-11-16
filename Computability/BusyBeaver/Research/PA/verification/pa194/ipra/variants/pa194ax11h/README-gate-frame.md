# AX11H gate through the next source frame

`PA194AX11HGateExact.gate` proves that the revised source executes from site 3519 to site 3553 with the exact primary AX gate result, provided registers 6 and 7 are zero. It uses a model-length candidate copy, two destructive comparisons, and two register transfers; the candidate instruction rows are bound to the checked unchanged gate window.

`PA194AX11HGateToFrame.gate_to_frame` composes that result with the revised tail from site 3553. For arbitrary model-valued source files, when registers 6 and 7 are zero and register 8 is `cantor z l`, it reaches site 25 in positive model-valued time with the exact full frame `outputArgs (result a) z l`, preserving the source-state tail. These are PRA-model results with IΣ₁ on the arithmetic reduct. The preceding AX body 50→3519, initial fetch and dispatch, scheduler alignment, and literal-machine correspondence are separate obligations.

From the repository root, with the previously replayed prerequisite outputs:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-gate-frame.sh /dev/shm/pa194-ax11h-gate-frame-repo /dev/shm/pa194-ax11h-candidate-gate-repo /dev/shm/pa194-ax11h-compare-return-repo /dev/shm/pa194-ax11h-ax-tail-frame-repo /dev/shm/pa194-ax-controller-repo
```

The output must be fresh. The checker hashes its source files and named direct input objects. The AX tail frame's `leanpath.txt` retains the other staged and prebuilt transitive inputs; their provenance is documented by those prerequisite stages. The checker rejects `sorryAx` and reports Lean axioms.
