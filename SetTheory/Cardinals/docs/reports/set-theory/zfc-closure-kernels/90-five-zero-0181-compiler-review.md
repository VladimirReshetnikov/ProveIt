# Independent review of the semantic compiler

Reviewed `semantic-validation/build_semantic_machine.py` and the inherited
`build_routing_machine.py` bisimulation/bootstrap checks,
`parametric_affine_driver.py`, and the dispatch loop of
`parametric_prefix_affine.py` on 18 October 2026. This is a manual source review,
not a new proof-assistant certification.

No route to an unjustified `PASS_SOURCE_AFFINE_AND_BOOT` was found in the
composition checked. The relevant safeguards are:

- Semantic words are rederived from the immutable source AST and symbol data,
  while the candidate's rules serve only as a certificate. Every rule must
  concatenate to its key, have nonempty children, and use permitted physical
  terminal orientations. Strict word-length reduction prevents rule cycles;
  the separate expansion guard rejects atom-implementation cycles.
- Routed external entries are checked against every supplied projection
  obligation. Source-state incoming edges and literal decision edges are
  compared with the inherited table. The final table must have exactly two
  rows per working state and exactly one nonworking target, the halt state.
- The prechange AST is checked against the pinned source's complete physical
  instruction paths. The transformed AST retains the ordered 6,460 source
  instructions. A register bisimulation checks every decrement/halting pair,
  exact tested registers, both decrement outcomes, matching finite multisets
  of intervening increments, and exact successor-pair references. This is
  stronger than leaf-order preservation alone.
- Full checking then applies all 8,391 affine site obligations to the **actual
  generated transition table**, with both zero and positive cases for each
  decrement. The universal gap parameter, arbitrary register file, full
  successor paths, overflow cases, and positive literal progress are retained.
- A concrete blank run must reach a dirty-root frame with the necessary zero
  registers and sufficient header gap. A separate dense interpreter repeats
  the exact number of transitions and checks all surviving one-cells against
  the sparse run.
- The baseline audit reports 245 working states, 128 grammar rules, 3,013
  bisimulation pairs, 8,391 affine obligations, and an exactly replayed
  407,915-step bootstrap. `--audit-only` is correctly labeled
  `PASS_SOURCE_AND_ROUTING_ONLY` and does not claim runtime or bootstrap success.

One operational caveat was reported to the main author: a failed affine or
bootstrap stage writes `NOT_A_VERIFIED_COMPLETE_MACHINE` but the reviewed
builder version returns normally with process exit status zero. Automation
must assert the final JSON status, or the builder should return nonzero on
that failure. This does not invalidate the baseline's explicit PASS report.

The trusted boundary still includes the inherited source calibration, the
meaning and soundness of the affine rules and arithmetic boxes, and the
dirty-root source theorem. The current review does not replace those proofs.
The reference package is accepted as an immutable trusted input; provenance
hashes should bind it in the final reproducibility archive. The scanner's
reported longest zero run is a diagnostic; full acceptance comes from the
actual-table affine checks, not that scalar statistic alone.

## Additional independent frame review

`semantic-validation/verify_semantic_frame.py` was subsequently read in full
and executed against the rebuilt baseline. It passed all 8,390 nonhalting
successor normalizations and 8,391 guarded cases. Its integer successor
calculation includes the three complete-path carries (case indices 8267,
8356, and 8387); zero-extension normalization preserves the arbitrary gap
parameter. The resulting update is
`n_next = n + positive_decrement + full_path_carry`, so the admissible
nonnegative range is preserved. The baseline has minimum constant residual
padding 13 and initial parameter 117.

The verifier also checks a complete prefix tree, exact physical/logical
register mapping, exact canonical table relabeling, both table hashes, and a
reconstruction of every one-cell in the initialized tape, including all 167
spare fields. The integer/tape calculations introduce no new finite-bound
assumption into the frame induction.

The frame checker explicitly consumes separate source/runtime/blank-run PASS
records. It is not a substitute for generating those records. The main
reproduction workflow was confirmed by its author to rebuild those positive
audits before the frame checker consumes the JSON. The final archive manifest
should bind all of those files together. No additional mathematical defect
was found in this review.
