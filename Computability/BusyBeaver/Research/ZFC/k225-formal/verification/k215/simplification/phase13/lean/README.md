# Phase 13 recorded Lean checks

This packet records the shared generic implication core and its shorter classical-logic adapter. The primary selection contains 184 project modules (179 for the endpoint and five for the uniform decoder prefix), plus three API clients: 187 providers, with 36 fresh invocations and 151 exact phase-12 reuses. The two additional endpoint clients report the same ten named standard-axiom profiles. The API clients produce twenty reports: seven constructive generic reports, five numerical reports using `propext` and `Quot.sound`, and eight classical-adapter reports (seven constructive; completeness uses the three standard axioms). The generic core itself prints six constructive reports.

The compatibility selection contains 68 project modules and two existing clients: 70 providers, with 16 fresh invocations, 53 current-primary reuses and one phase-12 reuse (`Dag254`). It retains ten client reports and five existing `WFTheory` reports. The combined project set contains 199 distinct modules. All nine physical-site batches retain their exact earlier source, object and log identities; they were not rebuilt in this iteration. Warning counts are computed from the selected logs and separated by fresh and reused origin.

Five adopted files are checked separately from the historical compilation inputs: the generic core, `Lukasiewicz`, the maintained producer, its derivation data, and an attributed research renderer preserved as inert data. The two historical canonical before-inputs are the old maintained producer and derivation; their exact snapshots remain bound. No supplied renderer, new Rocq compilation, or changed machine is part of this packet.

`execution.tar.gz` contains only source and record material. It retains complete selected ledgers, fresh command/source/log records, API and endpoint audit sources/logs, planning and actual receipts, and the five adoption boundaries. Exact predecessor material is referenced through the pinned local [phase-12 packet](../../phase12/lean/README.md), not copied as ancestor archives or compiled objects. The phase-12 reader is invoked in historical mode; optional current-source comparison applies only to phase 13. The collector rehashes all live current providers, basis inputs, audit objects, logs and explicit historical snapshots after validation. The saved reader validates the recorded hashes and does not claim to recreate those objects or rerun Lean.

From a checkout containing the predecessor packets:

```sh
python3 -B review_saved.py --basis-repo /absolute/path/to/Proofs --repo /absolute/path/to/Proofs --output /tmp/phase13-saved-review.json
```

Omit `--repo` to review this historical source checkpoint without requiring current maintained sources to match. `basis.py` verifies the exact local predecessor reader and archive hashes before loading that maintained reader; no member of an evidence archive is executed. The collector and metadata controls are retained inside the archive as provenance. The preliminary source-only plan remains unchanged alongside the final preparation records.
