# Boundary binding drafts: warning cleanup

These remain **unchecked drafts**. They are copied from `../trace74-boundary-parent-binding-draft/`. The only source change is removal of `<;> ring` after a `simp` call in `Trace74BoundaryParent.lean`; the original strict attempt's Lean process exited 0 but reported that this tactic did nothing and was never reached. The other three source files are byte-identical to the earlier reviewed drafts. No stage from that warning-rejected attempt is promoted to accepted.

The compatible staged retry is in `../trace74-boundary-compatible-rebuild/`. Even if the conditional boundary graph theorem checks, the separate finite R=31 seed still needs a checked specialization. The arbitrary-port seed violates the fixed BFS port assumptions; no fixed-port, iPRA or completed graph-zero claim follows from these files.
