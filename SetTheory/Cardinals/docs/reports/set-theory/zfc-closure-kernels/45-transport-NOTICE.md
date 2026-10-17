# Provenance and attribution

This research package was prepared for Vladimir Reshetnikov's ProveIt
request on 17 October 2026. It contains new mathematical exposition,
reference implementations, finite checks, and separately identified
unchanged source material. It does not claim a new complete binary Turing
machine below the existing 253-state construction.

The root MIT No Attribution license applies to the new material and to
material already covered by that license. It does not relicense any
third-party source lacking such a grant. See `machine_control/NOTICE.md`
for the explicit upstream source and backend boundaries.

## Existing work used here

- ProveIt was inspected at commit
  `61e77836565f63582561f54745f633d50efd9c7d`. The three commits named in the
  request and the later research/Lean changes were read in that context.
- `code/vendor/four_kernel.py` and `code/vendor/stream_four.py` retain the
  complete four-operation kernel and streaming comparator from the
  source-28 research artifact, without modification. The tagged syntax,
  logical axiom families, signed unary codec, and classical four-map
  factorization are inherited or adapted from that work.
- `code/two_kernel.py` changes the primitive whole-formula name operations
  of that checker. The CP/GIC and optional EPSC2 emitters in
  `code/fixed_theory.py` derive from the same source artifact. The separate
  unary-plus-binary-Union emitter materializes the calibrated schema from
  the incoming `zfc_unary_closure_research.zip` report; the calibration is
  prior work.
- The existence of abstract two-generator embeddings for countable
  transformation families is classical (Sierpinski, 1935). The report
  claims an explicit simple construction and its engineering application,
  not discovery of the abstract two-generator phenomenon. Historical
  priority of the particular pair has not been established.
- Fixed-zero quantifier normalization and substitution via generalization
  followed by universal instantiation use standard first-order logic.
  Earlier ProveIt binder work already demonstrates colliding substitution
  through GEN/UI/MP. No priority claim is made for that logical mechanism.
- The original register program and machine are attributed to Mira-Cult;
  Jeff and contributors provide the upstream Coq development; the public
  253-state reduction is attributed to mira-emmy. Andrew James Wade's
  compiler backend is retained with its original license. The 203-node
  structural sharing of the literal source was already identified in
  ProveIt's source-09 work.

## New work supplied

The explicit `u,w` finite-restriction construction, constructive reduction
of the four-map proof language, independently implemented checks, measured
component comparisons, integrated fixed-theory searches, smaller normalized
quantifier interface, and the register invariant/assembly experiments are
documented in the report. Some ingredients are standard; all claims of
measured improvement are scoped to the actual measured artifact.

The code and ordinary proofs here are not presented as new Lean/Coq
verification of the entire consistency-machine chain. Existing formal
results and remaining formal interfaces are identified in the report.

Pinned paths and hashes are in `provenance.json` and `MANIFEST.sha256`.
The nested machine-control package has its own unchanged manifest and
more detailed provenance.
