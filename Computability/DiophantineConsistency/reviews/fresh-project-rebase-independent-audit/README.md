# Independent selective-rebase control audit

[`audit.py`](audit.py) copies and hashes the rebase preparer and its two test
scripts, together with the parent-pair builder, coordinator and comparator.
It runs the copied toy graph tests and the real-Lean matched toy pair test;
[receipt.json](receipt.json) records the exact input hashes and process results.
The independent audit's actual zero exit is recorded in
[terminal-observation.json](terminal-observation.json).
The controls cover reverse project ancestry, hidden and misclassified direct
dependencies, parent terminal-observation pins, isolated sibling copies,
affected-object exclusion and unexpected companions.

This is a test of the preparation mechanism on a tiny example. It does not
accept a full 1,210-module parent, perform a successor preparation or rebuild,
or authenticate inherited package-transitive, dynamic or transient inputs.
