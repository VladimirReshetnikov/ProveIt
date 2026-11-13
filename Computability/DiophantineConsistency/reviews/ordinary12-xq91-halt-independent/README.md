# Independent review of the 91-operation fixed-port halt-model theorem

The accepted Lean source proves, for every model `V` satisfying the recorded
`IΣ₁` hypothesis, that a strictly positive zero of the 91 graph at the fixed
symbolic port tuple exists if and only if

```
∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0.
```

Separate theorems give the same model equivalence for the positive-shifted
graph and for its exact closed Lean byte recipes. The model coordinates and
`T` may be nonstandard. The 91-operation count applies to the positive
coordinate evaluator and excludes the separately expressed `x+1` shifts.
These are model-level statements; they do not themselves prove an iPRA
consistency equivalence or a Lean theorem interpreting external files or a
PDF.

For a positive 92-graph zero, the proof first transforms its `Y` coordinate
to obtain a positive zero of the older 95 free-J literal; `J` and `X` are
unchanged. The existing `FreeJGraphCongruenceExplore.symbolic_aligned`
theorem is applied to the exact symbolic beta, kernel, low and high ports.
Its explicit hypotheses require `(B:V)+1=Exp.exp((67:V)*8807)`, the natural
port equalities `L=lowNat` and `H=highNat`, positive coordinates, and the
old literal zero; the kernel port `K` is arbitrary. The client supplies
`CompactFixedBeta.beta_identity`, the two reflexive equalities and the
transformed zero. The theorem yields `X=q*w` without expanding beta. Since
`X>0`, the proof rules out `w=0`, obtaining a positive quotient. Together
with the direct `X=q*w` map and the earlier 91/92 transformed-zero theorem,
this gives the positive-zero existence equivalence. The fixed-symbolic
model-halt theorem is then composed with that equivalence, and the byte
version follows from `byteP_eq`.

The selected namespaced `FreeJGraphCongruenceExplore` object has SHA-256
`545daf0e…` and occurs in the recorded 92 halt project ancestry. The retained
paired graph-band receipt reports the same object hash and the exact extended
source hash `d748f8bb…` on both sides, with successful compiler/direct-import
checks and the `symbolic_aligned` axiom report. The selected object and that
source are rechecked here. This is useful provenance evidence, not a complete
rebuild or authentication of inherited project, package and dynamic ancestry.

The accepted author run exited zero, with empty stderr, no warning and no
`sorryAx`. All five named reports contain the Lean metatheory axioms
`[propext, Classical.choice, Quot.sound]`. The source, retained source and
runner snapshots, tool binary, logs and output object match the receipt.
Two recorded samples saw at most one Lean process and at least 18,455,396
KiB available memory; sampling is not continuous.

The checker rehashed the full recorded 1,294-file selected union and its
symlink targets twice. Its membership is exactly the earlier 1,291-file 92
halt union plus `QCube92Halt`, `XQ91`, and `XQ91Model`. It verifies recorded
source imports and their selected hashes, the 741-module planned serialized
project ancestry and selected symbolic-alignment object, and reruns the prior
read-only 91 ancestry and model reviews. Attempts 01 and 03 have recorded
nonzero exits and kernel-memory errors; they are not accepted proofs. Attempt
02's runner failed during monitoring and did not capture its child's exit;
no result or resource-monitor pass is attributed to that child.

Run `python3 -I -S -B check.py` from this directory, or pass the script path
from another directory. The captured execution exited zero with empty stderr;
see `observations/stdout`. The check needs the retained absolute `/tmp`
provider and output paths. No Lean process was started during this review.

This is an independent inspection of a single accepted author run and its
selected-project records, not a fresh independent kernel replay. The
serialized analysis inherits the earlier header inventory and does not
traverse package-transitive or dynamic imports. Complete historical
source-to-object provenance, the internal iPRA endpoint, and the external
coefficient-file and PDF bindings remain separate obligations.
