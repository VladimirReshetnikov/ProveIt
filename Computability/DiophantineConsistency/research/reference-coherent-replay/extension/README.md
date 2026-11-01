# Experimental paired strict extension

These scripts adapt the guarded selective-rebuild workflow to append new
modules to an unchanged matched parent project graph. They have **not** been
run on the real AQ29 project pair. They inherit the parent provider's
package-transitive, dynamically loaded and transient-mutation limitations.

The committed [`task-policy.json`](task-policy.json) binds the uncompiled
joint wrapper `IPRAReferenceReplayChecks` and six exact declaration names,
including the selected Foundation consistency comparison and AQ29 composition.
The freezer accepts a strict current-source plan only after an observed parent
coordinator success, checks parent state and provider hashes, enforces a disk
reserve, freezes sources under logical module paths and records tool hashes.
That gate is not the full parent comparator: `prepare.py` independently
reproduces the parent comparison, checks the separately recorded freezer
terminal exit and emitted manifest hash, verifies the task policy and sources,
and copies each parent's objects into a distinct sibling directory.

`rebuild.py` checks actual Lean dependencies, rejects stale companions and
project fallbacks, and builds only the appended modules. `compare.py` checks
the two sibling states, full present/absent companion-key coverage, byte
equality of every fresh companion, project and parent inode separation, exact
target report names, logs, source and provider guards. `run_pair.py` preserves
both builder exits. The parent/extension manifests and actual terminal
observations must be pinned; the final reviewer must check the manifest's
target and task-policy identity, not merely a success status.

Nine tiny selection/observation controls and a Git-backed source-freezer
control pass on the current scripts. The final-source adversarial real-Lean
toy and the observed-freezer end-to-end toy also passed at low priority; an
independent reviewer reran the latter. Their scoped terminal observations are
in [toy-integration-observation.md](toy-integration-observation.md) and
[toy-adversarial-observation.md](toy-adversarial-observation.md).
No test here establishes the requested mathematical equivalence.

[`test_full_chain.py`](test_full_chain.py) constructs a small paired parent,
invokes the actual planner and freezer, records their terminal exits, and
passes the observed freezer output into the paired extension. Its declarations
use the target names for testing but are toy theorems; a passing run validates
this workflow on that toy, not the AQ29 endpoint.
