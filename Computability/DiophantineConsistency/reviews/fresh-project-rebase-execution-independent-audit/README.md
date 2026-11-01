# Independent selective successor rebuild control audit

[`audit.py`](audit.py) copies and hashes the selective preparer, builder,
comparator, coordinator and both test scripts, plus the fresh-parent pair
tools. It reruns the graph/guard controls and a real Lean toy parent pair,
selective successor pair and comparison. The toy's reason-specific negative
controls include missing direct imports, source drift, unexpected companions,
equal-byte cross-sibling hardlinks, seed mutation and unobserved parent exit.
The [receipt](receipt.json) records exact copied source hashes and child exits.
The [independent audit process](terminal-observation.json) exited zero.

This is not a full project successor replay. It does not establish transitive
package provenance, dynamic-import coverage or absence of transient mutation.
