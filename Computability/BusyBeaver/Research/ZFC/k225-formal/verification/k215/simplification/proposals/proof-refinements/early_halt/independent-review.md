# Independent internal review

The machine-reduction reviewer compared the theorem with the actual
`L1_CompPerm.xstep` and `EnumPerm.ax_stack` definitions and confirmed:

- The pop counts are correct: j+1 before DROP, n+1-j afterward.
- The counter is unchanged in the numeric adapter.
- No opaque-tail entry is read; the final zero is loaded last.
- `P(0,0)=0` does not invalidate the proof because only `unP_P` is used.
- The eight axiom selectors are indices 0..7; GEN is index 8 of n=9.
- Existing GEN setup makes the saved pre-AX top zero.
- The standalone adapter duplicates the two command shapes, so a full
  project claim requires the explicit map into production `cmd` and
  execution equality. The completed production build compiles that map, execution equality
  and AX stack view. Recursive `coqchk` passed for the full small adapter
  closure. In the final review, the machine-reduction reviewer checked
  all eleven input hashes, confirmed that all three delivered new sources
  equal their compiled copies, and checked that the five pinned production
  sources differ only by three `Stdlib` to `Coq` import-prefix edits. The
  reviewer did not independently rerun the compiler; its raw evidence is
  separate in `production-verification-final/`.
- Existing `leaf_tac` already makes surface proofs short; no net LOC or
  measured compilation improvement has been established.

The proof-simplification reviewer independently checked the two-stage
argument: draining before+x loads x; DROP pushes G; draining G+after+zero
returns exactly the retained tail and zero cache. They confirmed the old-
cache alarm timing and arbitrary initial cache hypotheses. Their request
for an explicit counter frame was implemented in `NativeSelection.v`.

These are separate internal reviews within this research collaboration,
not external human reviews. The actual source/hash and compiler records
are retained independently in `verification/` and
`production-verification-final/`. The frozen production adapter SHA256 is
`80923e68cc13a43a3487d660fad67ca12c41103a1e140a49541ad69eb3af4905`.
