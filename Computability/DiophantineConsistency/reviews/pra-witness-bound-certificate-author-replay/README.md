# Generic candidate-PRA witness-bound certificate

`certificate_of_witness_bounds` derives the exact fixed-sentence
`BoundCertificate` from witness bounds in every candidate-PRA model, using
first-order completeness. `comparison_of_witness_bounds` combines that step
with the existing conditional no-zero comparison. Both retain the witness
bounds as explicit hypotheses; the latter also retains its IΣ₁ equivalence
and Σ₁ hierarchy hypotheses. Neither proves the ZFC instance.

Two separately compiled bridge objects matched SHA-256
`faa80d617334d21f8d4ea2ada8e2f39d6215f3791630cf3adbfc193150024a1b`.
The source SHA-256 is
`020aa37617f919f1e10c3d0fd607f18d5680b9cc446edca7e2d9ef8194962495`;
the attached scoped checks report only `propext`, `Classical.choice`, and
`Quot.sound`. Both bridge builds used newly compiled current-source
`PRABndRewriting` and `PRAWitnessCalculus` objects over the same historical
`/tmp/pra-after-open-bound-merge-refresh-9m9dtqdk/lib` parent and inherited
Foundation/package ancestry. The historical parent differs from current
project sources; these two scoped checks are not a current-source closure.

`replay.py` separately performs a guarded merged-source project dependency
refresh from that parent, rebuilding every changed/new node and its
descendants. The author run at `/tmp/pra-witness-bound-certificate-m09y1fhi`
passed all 50 rebuilt modules, guarded 198 declared project sources and 148
inherited project objects, and rechecked their hashes at the end. Its 50
source/log snapshots and terminal state are frozen in `author-evidence/`.
An independent same-parent replay is in progress. This is not a clean full
build: unchanged project objects and external Foundation/package ancestry
remain inherited; the guards establish their stability during this run, not
their complete provenance.
