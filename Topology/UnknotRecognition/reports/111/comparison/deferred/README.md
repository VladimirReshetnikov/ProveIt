# Attributed deferred-forest comparison

The four Python modules in this directory are unchanged copies from
`ProveIt_Deferred_Forests_2026-10-12/overlay/Topology/UnknotRecognition/fast/fastunknot/`
in the preceding incoming research package.  That package identifies baseline
commit `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5` and credits its own prerequisites.
These files are comparison inputs, not new implementation claims of this
Euler/group package and not a second production overlay to install.

`tools/audit_native.py` hashes these files, copies the integrated native
`fastunknot` package into a temporary directory, overlays only these four
comparison modules, and evaluates `forest_strategy="deferred"` in isolated
worker processes.  Each positive replays through the source verifier in that
temporary runtime.  The current checkout is never modified by the comparison.
This reproduces the preceding deferred-forest coverage on the same archived
120 source cases before evaluating the union with the new group terminals.

The preceding package states that its code follows ProveIt's MIT No Attribution
license.  The full upstream article and ZIP are not redistributed here.
