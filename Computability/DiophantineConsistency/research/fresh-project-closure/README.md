# Preliminary fresh project-source closure rebuild

`prepare.py` freezes the source-declared import DAG under a new output directory, stores each project module with its SHA-256, and records external imports. `audit_snapshot.py` checks source snapshot bytes, workspace bytes, topological ordering and Git tracking at a point in time. The AQ29 endpoint preflight snapshot and its source audit are recorded under `reviews/fresh-project-closure-preflight`: 1,210 tracked project sources, 106 distinct direct external module names, and no source differences against the audited HEAD. The temporary snapshot remains at `/tmp/ipra-aq29-fresh-source-closure-v2`. These observations do not compile the closure; header parsing is independently checked against `lean --deps` during the proposed rebuild.

`rebuild.py` is a preliminary fresh-build driver. It requires explicit SHA-256 pins for the snapshot manifest and a successful Foundation-provider receipt, validates the corresponding pinned Foundation input and compiler, creates a new empty project object root, rejects project namespaces in fallback roots, checks compiler-reported imports against declared edges, checks direct objects and companions before and after each build, and authenticates the inputs and outputs again at the end. It records whether workspace sources still match the frozen snapshot at the end. The driver has passed a two-module real-Lean control and negative controls, but **has not run the 1,210-module project closure and has not established a native endpoint**. The guarded Foundation provider is still being built; independent driver review is pending.

The source graph covers source-declared project imports and does not by itself establish package-transitive, dynamic loading, executable/toolchain, transient-mutation, or hidden-import provenance. `lean --deps` reports direct module dependencies, not their complete transitive contents. A successful author run alone would not be an independent replay. No old project objects may be substituted into the fresh build, because mixed Lean providers can accept unsound combinations; see `reviews/lean-mixed-provider-counterexample`.

Once the guarded Foundation build has actually exited successfully and its receipt has been reviewed, the following commands prepare two sequential fresh project compilations. Replace the two SHA-256 placeholders only with the independently verified snapshot manifest and Foundation receipt digests; `run_pair.py` checks them again. The output directory must not already exist. The four endpoint axiom reports are the four explicit checks in `IPRAAQ29NativeChecks.lean`.

```sh
task_snapshot=/tmp/ipra-aq29-fresh-source-closure-v2
task_provider=/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json
task_foundation_input=Computability/DiophantineConsistency/reviews/foundation-provider-recovery/input-manifest.json
python3 Computability/DiophantineConsistency/research/fresh-project-closure/audit_snapshot.py "$task_snapshot" --output /tmp/ipra-aq29-source-audit-before-pair.json
python3 Computability/DiophantineConsistency/research/fresh-project-closure/run_pair.py \
  --snapshot "$task_snapshot" \
  --snapshot-sha256 VERIFIED_SNAPSHOT_MANIFEST_SHA256 \
  --provider-receipt "$task_provider" \
  --provider-sha256 VERIFIED_FOUNDATION_RECEIPT_SHA256 \
  --foundation-input "$task_foundation_input" \
  --expected-axiom-reports 4 \
  --output /tmp/ipra-aq29-fresh-project-pair
```

If the prelaunch audit reports source differences, freeze a new snapshot and audit it instead. The coordinator runs the second compilation only after an actual zero exit from the first; it compares the complete row order, source and output hashes, declared/direct dependencies, axiom logs, provider inputs, and guarded companion paths. Each run starts with an empty project output tree. It preserves per-run process logs, states and actual exit codes; a failure stops the sequence and must not be overwritten or presented as a pass. A matched pair is a same-provider replay, not a separate package-transitive or dynamic-input audit. If the workspace changes during either run, the result is for the frozen historical snapshot, not current workspace source. Do not restart a still-running job because a status observation times out.
