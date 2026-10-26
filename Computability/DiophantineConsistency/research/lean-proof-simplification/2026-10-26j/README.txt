SIX FURTHER WAYS TO SIMPLIFY DIOPHANTINECONSISTENCY LEAN PROOFS
26 October 2026

Repository: https://github.com/VladimirReshetnikov/ProveIt
Review pin: 8e8b5dcb954969621c484588f0b902be1cfea7b3
Lean toolchain: leanprover/lean4:v4.32.0
Mathlib pin: 81a5d257c8e410db227a6665ed08f64fea08e997

READ FIRST

report.pdf is the complete article; report.tex is its LaTeX source.
The six proposals were not found in the audited proof-simplification packets.
This is a scoped comparison, not a literature-wide claim of originality.

The main directions are decoder invariant fusion; signed-congruence transport;
internal constructor views with one unique-existence induction; definable
recursive-graph preservation/fusion; automated depth-budget certificates; and
explicit least/greatest cyclic carries with their ambiguity classification.

VALIDATION STATUS

1. lean/SignOrbit.lean
   Checked generic signed equivalence and concrete integer modulo transport,
   including natural-absolute-value transport. Generic probes: no axioms.
   Integer probes: propext only. Production Mathlib/Pell integration not run.

2. lean/DecoderGraph.lean
   Checked exact graph characterization for a generic binary decoder with
   explicit one-step encoding/inspection laws. Production adapter not proved.

3. lean/ExactDecoderFusion.lean
   Checked the exact production decoder, offsets, and proposed fused proof
   after parameterizing only pair, unpair, and the pair_unpair inverse law.
   Reports propext and Quot.sound. This is stronger than a toy model, but
   is still not a rebuild of the project's Mathlib-dependent module.

4. lean/TaggedConstructor.lean
   Checked constructor discrimination and tagged-relation inversion on an
   arbitrary carrier. Axiom-free. Concrete BoundStep equivalence and internal
   unique-existence theorem remain production proposals.

5. lean/IterationGraph.lean
   Checked graph preservation and fusion over an arbitrary internal index
   type, requiring induction for the EXACT invariant. Both axiom-free.
   The actual ThetaG adapter and object-formula specifications remain work.

6. lean/DepthBudget.lean
   Checked numerical depth-certificate soundness and source-shaped factorial
   and product plans (512+50=562; product overhead66 with floor16384).
   Standard Lean axioms only. GraphRep adapters and automated extraction
   are NOT implemented. Hand-copying the certificate alone is not a saving.

All six files were checked with Lean 4.32.0. See evidence/validation.json and
individual logs for exact exit codes, source hashes, and axiom probes.
No production module, project-wide endpoint, or Mathlib dependency closure
was rebuilt. No source-level proposal is described as fully integrated.

PROPOSED PATCH

patches/DecoderFusion.proposed.patch applies to the pinned source and leaves
the executable definitions and old public theorem names intact. It replaces
a 56-line source region by 38 lines (18 fewer physical lines). Applicability
was checked with git apply --check. Production Lean compilation remains
required before adopting it. It has NOT been applied to the repository.

CYCLIC CARRY RESEARCH

The article gives an ordinary general proof, independently reviewed, of the
least/greatest formulas and exact two-solution boundary for a genuine cycle,
length>0 and radix>1. This theorem is NOT formalized in Lean here. The Python
script provides 57,540 raw-array/budget instances, including 2,323 exhaustive
bounded-fixed-point enumerations. These are finite experiments only. Keep
the existing more-general arbitrary-predecessor existence theorem.

REPRODUCTION

  python3 scripts/verify.py --lean /path/to/lean
  python3 scripts/verify.py --lean /path/to/lean --repo /path/to/ProveIt
  python3 scripts/check_cyclic_carries.py
  python3 scripts/build_pdf.py

The standalone Lean files require no Mathlib installation. Lean must be 4.32.0.
The Python scripts use only the standard library. The PDF build needs pdflatex
with the ordinary packages listed in report.tex. The review's PDF was rendered
and visually inspected after compilation.

EVIDENCE

evidence/prior_ideas.md: 43 excluded prior proposal families and their sources.
evidence/prior_archive_inventory.json: original ZIP and 112 member hashes.
evidence/source_inventory.json: 574 Lean files, physical-line counts, hashes.
evidence/snapshot_tree.txt: pinned Git blob identifiers for source/incoming.
evidence/depth_budget_review.md: source-shape and missing-adapter review.
evidence/peer_review_carry.md: independent general proof and boundary review.
evidence/semantic_review.md and algebra_review.md: detailed analysis notes.
evidence/lake-manifest.json: repository dependency lockfile, not installed deps.
SHA256SUMS.txt: integrity inventory of final package files (excluding itself).

No scripts from previous incoming archives were executed for this review.
No commit, pull request, or remote repository modification was made.
