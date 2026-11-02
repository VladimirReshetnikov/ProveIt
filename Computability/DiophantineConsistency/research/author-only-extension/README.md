# Preliminary author-only extension of a fresh project replay

This workflow is for *exploratory* source compilation against the separately
audited, completed AQ29 author pass while its peer is still running. It does
not claim a matched proof, a current-source result, source authentication of
inherited packages, a runtime-load trace, or an observed outer exit for the
Foundation builder. The guarded paired extension remains the acceptance path.

`run.py` takes a SHA-256-pinned additions manifest. Its source rows must name
tracked Git blobs at a pinned commit, with a topological order and declared
direct imports. It copies those exact bytes into a fresh source tree, creates a
separate namespace overlay whose links point only to the audited fresh author
project objects, and compiles new modules against that overlay and the same
fresh Foundation/package provider. It rechecks all parent objects, recorded
direct companion paths, frozen parent sources, Foundation artifacts, input
receipts and new outputs before and after compilation. It checks Lean's direct
dependency report and exact expected diagnostic names. Checks are observations
at points in time; mutations between observations, package-transitive and
dynamically loaded inputs remain outside scope. No historical mixed project
object may be substituted into the parent overlay.

Use idle I/O and CPU priority and coordinate with the active peer. The output
directory is fresh and does not alter the author or peer directories. A passing
result would be a single author-only compilation on a historical snapshot.

The bounded `test_guards.py` and `test_end_to_end.py` checks passed together
with actual session 93993 exit 0. They exercise a real Lean symlink overlay,
source and input guards, and production orchestration with a synthetic
one-module author and synthetic empty Foundation provider. The end-to-end toy
uses a copy of the runner with fixture-specific paths, pinned hashes, author
row count and I/O rate; its two fault cases additionally inject mutations into
that copy. An independent repeat and its limitations are recorded separately
by the AQ26 reviewer. None of these tests compiles the real extension or
authenticates inherited package or dynamic ancestry.
