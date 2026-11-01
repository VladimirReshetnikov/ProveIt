# Experimental paired strict extension

These scripts adapt the guarded selective-rebuild workflow to append new
modules to an unchanged matched parent project graph. They have **not** been
run on the real AQ29 project pair. They inherit the parent provider's
package-transitive, dynamically loaded and transient-mutation limitations.

The committed [`task-policy.json`](task-policy.json) binds the uncompiled
joint wrapper `IPRAReferenceReplayChecks` and four exact declaration names.
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

Eight tiny selection/observation controls and a Git-backed source-freezer
control pass on the current scripts. An earlier revision also passed a small
real-Lean paired extension with mutation controls, but the freezer, policy and
observation chain were strengthened afterward. **The final script revision
has not yet passed a real-Lean paired integration rerun.** That rerun and an
independent audit are required before this prototype is used for the real
project. No test here establishes the requested mathematical equivalence.
