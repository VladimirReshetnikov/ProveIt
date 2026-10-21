# Exact producer follow-up, not executed

Owner inputs are `generate_dominated_implication_lean.py` and
`dominated_implication_templates/core-suffix.txt`. Their current bytes are
pinned in `freeze.json`. The adapter and core-prefix templates need no change.

Keep the original Source149 input, thirteen shortcut checks, roots and acyclic
closure validation. This proposal changes only the final proof presentation:

1. After the existing abstract-variable/seed conversion, replace the unique
   application `(b12 h v0)` in b13 by b12's exact body. Replace the unique
   application `(b15 h v1)` in b16 by b15's body with v0 renamed to v1.
2. Omit the emitted b12 and b15 declaration blocks, retaining their validation
   ancestry and a metric saying they were inlined once. Require exact counts and
   exact expected proof bodies; do not silently apply the operation to a changed
   certificate.
3. Omit emitted b60 and replace only the suffix template's `basisK` alias by the
   b60 proof body with v0→a and v1→b. Retain `basisK`'s exact type and name.
4. Update the suffix template SHA in the producer and make metrics distinguish
   validated ancestry from emitted named helpers (three fewer). Preserve the
   original certificate/shortcut status rather than pretending the ancestry
   itself became smaller.
5. Generate into a fresh scratch directory, compare the complete core to
   candidate/DominatedImplication.lean and the complete adapter to the current
   unchanged DomRho8.lean. Test modified-input rejection and actual typed endpoint
   clients under the shared kernel lock at the next authorized checkpoint.

There is no producer change needed for handwritten KHomeReady.lean. The
source-only draft does not imply its tactic elaboration has already passed.
