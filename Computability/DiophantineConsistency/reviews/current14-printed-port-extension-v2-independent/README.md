# Independent read-only review of extension driver v2

Reviewed exact driver, owned-session helper, guard, synthetic controls, and
retained control receipt hashes pinned in [`audit.py`](audit.py). Run
`python3 -I -S -B audit.py` to reproduce the read-only receipt and hash check.
No Lean, extension driver, or fixture was launched during this review.

Within its documented Linux `/proc` and `waitid` assumptions, the new helper
addresses the v1 monitor-exception orphan risk: both `lean --deps` and the
compiler run in a new session, the direct child remains unreaped until the
observed session drains, and exceptions cause passive waiting. Signals target
the original owned process group only after checking the unreaped leader's PID,
start time, parent, group and session. A successful call returns a receipt
asserting observed session drain and direct-child reaping. Separate session
escapes, forced termination, transient process-observation races and kernel
or `/proc` failures are not excluded; monitor failure or different-group
children can require an indefinite passive wait. The time/disk monitor is
sampled, and group signals do not target other groups in the same session.

The driver routes both dependency resolution and compilation through this
helper. It retains per-call receipts, dependency stdout/stderr paths and
hashes, compile logs and direct import records; final checks rehash those
logs and the driver/helper. The captured controls report successful normal,
monitor-exception, timeout and identity-mismatch fixtures with an unrelated
sentinel, plus refusal while the base was running. They are not a real Lean
success path and do not authenticate an actual extension.

This v2 driver is separate from the existing v1 coordinator and is not pinned
by it. Before use, a new independently reviewed coordinator must pin these
exact sources, check the per-call receipts and captured dependency logs, and
capture the actual driver exit and final source/object inventory. The driver
still inherits the prior direct-input routing and provider assumptions, with
package-transitive, dynamic, transient and adversarial filesystem races beyond
its guarantee. This review is not authorization or evidence of a build or an
endpoint theorem.
