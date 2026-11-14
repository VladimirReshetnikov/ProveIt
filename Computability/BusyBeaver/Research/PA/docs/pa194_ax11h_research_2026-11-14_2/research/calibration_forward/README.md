# Pinned sources for the written calibration construction

The active mathematical fragment is `proof/forward_calibration_completion.tex` in the archive root. The immutable files under `source/` are the inspected ProveIt extracts, with exact pinned Git blob identities in `source_manifest.json`. They support the explicit constructor recipes; this is not a newly built standalone Lean project. The ProveIt and imported James Chang licenses in `licenses/` apply.

All lower interfaces invoked by the term construction are supplied in `proof/forward_calibration_completion.tex`. The forward construction targets direct C4 derivation lists and does not reuse the stronger correctness theorem of the upstream verifyValue checker.
