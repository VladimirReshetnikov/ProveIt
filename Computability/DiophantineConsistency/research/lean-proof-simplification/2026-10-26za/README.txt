POST-ADOPTION LEAN PROOF REVIEW
26 October 2026

Read report/report.pdf and its editable, multi-file TeX source first.

BASELINE AND EXCLUSIONS
  Proof-source pin: 22e020937caa81d0cb72a4f63071d6c0bcc1eba9
  Bounded final comparison: 1e2a853935a6155cbcf2aa199aaca51946c4fff9
  Source: https://github.com/VladimirReshetnikov/ProveIt
  Lean 4.32.0; mathlib 81a5d257c8e410db227a6665ed08f64fea08e997

Prior methods are treated as already available/completed for novelty and
marginal accounting, as requested. That does not assert that mutually
alternative patches coexist in a compiled tree. The supplied baseline is
the observed source snapshot, not a hypothetical merge of all proposals.

The final review covers 21 manuscripts: 18 placed packets and 3 incoming
archives. The initial 93-contract/383-section ledger has its own narrower
scope. Later ledgers supplement it; their overlapping counts are not added
as if they formed a disjoint census. Old reports are not rebundled here.
Exact source locations, artifact hashes and provenance are in catalog/.
For six newly placed reports, placed-file/report hashes were verified;
their retired original ZIP hashes were not independently recovered.

RETAINED PROPOSALS
  strip/: HeadBounds' two Fin 3 wall-bound proofs, 135 to 130 physical lines.
          This is a routine application of known order facts, not a new
          monotonicity method. No new helper/import is charged elsewhere.
  row/: Receiver causality in an actual operating row. Optional: +47 lines.
  machine/: Full interior tile equality to constructed stepTile. Optional:
            +28 physical lines, +26 nonblank lines, +3 proof-body lines.

The optional interfaces are stronger semantic contracts, NOT source-saving
patches. Together their composed RowStep file grows 205 to 280 lines.
Applying HeadBounds plus both optional interfaces gives +70 physical lines
overall. Do not claim the shorter consumer bodies as a net saving.

PATCH CHOICE
  Both standalone RowStep patches target the unchanged source pin. Their
  contexts overlap, so they cannot be applied sequentially in either order.
  Choose ONE standalone option, or apply ONLY:
    row/combined/causality-and-canonical-row.patch
  to get both. The combined source is separately audited. The HeadBounds
  patch is independent. No supplied audit changes your checkout.

WITHDRAWN AND NOT INCLUDED AS PROPOSALS
  The absolute-value trace cleanup and first-failure boundary factoring
  already occur in incoming reports. The periodic 435-versus-433 halting
  endpoint is already maintained in WangTiles942Soundness. Their candidate
  patches, future-endpoint draft and savings are excluded from this package.
  Their original maintained source files may of course appear in baseline/.

STATUS
  EVERY NEW LEAN CANDIDATE IS UNCOMPILED.
  Textual headers, exact patches, hashes and finite models were checked.
  No Lean elaboration, kernel checking, axiom audit or performance benchmark
  was run for these replacements. Upstream receipts concern upstream code,
  not the new proposals. No public repository or prior delivery was changed.
  See VALIDATION.json for a compact statement of scope.

STATIC REPLAY
  With Python 3, from the extracted package root:
    python3 -X utf8 -B verify.py
    python3 -X utf8 -O -B verify.py
  On Windows use your Python executable name (often python instead of python3).
  UTF-8 mode ensures Lean symbols decode consistently. No network, Git or
  Lean installation is required. Results are printed to stdout; save new
  receipts OUTSIDE the sealed tree. PASS_STATIC_REPLAY_NOT_LEAN is not a
  proof-validation result. The verifier checks all sealed bytes and all
  608 main-subtree Lean sources, then invokes the five read-only audits.

SOURCE AND DOCUMENT REPRODUCTION
  baseline/ contains the main Lean subtree and selected pinned documentation,
  not the complete external dependency closure. The broader source inventory
  also lists archived research files that are not repeated in baseline/.
  inventory.py accepts a full checkout when reproducing that broader census.
  report/build.sh rebuilds the paper using installed TeX packages; it installs
  nothing. Rebuild a copy outside the sealed tree because output files change.
  Corpus receipts describe the read-only review already performed; full
  manuscript replay requires the separately recorded repository/archive inputs.

BEFORE ADOPTION
  Use a disposable checkout with the exact toolchain/dependencies. Establish
  an unchanged baseline, choose the desired patch variant, compile each module
  and affected reverse dependencies serially, and run the explicit Checks/Audit
  modules as well as the aggregate target. LAKE_JOBS=1 alone does not prevent
  dependency fan-out in the repository's recorded Lake version.
  Inspect theorem types and axiom reports. Retain the exact receiver target
  membership (including 215), the original source configuration and open-strip
  bounds, and the temporal no-finish proof where needed. Receiver causality
  alone must not turn a possible finish tuple into a pass tuple.

The newer maintained marked-word equivalence is credited, not proposed again:
existence of a marked word corresponds to actual blank halting, while absence
of marked words corresponds to ConZFC. The actual polynomial converse and
internal-ZFC formalization remain separate obligations.
