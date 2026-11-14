Alternative PA consistency machine with 195 working states
========================================================

This package is a successful new 195-state layout, not a construction with
fewer than 195 working states. It is supplied as a reproducible intermediate
result. The starting diagonal PA source and its intended logical theorem are
those of docs/incoming/pa195_conpa_2026-11-13.zip in VladimirReshetnikov/ProveIt.

The binary, two-way, single-tape machine starts in state 0 on an all-zero tape.
Working states are 0,...,194. State 195 is a separate halt with no outgoing
rows. Each row in pa195_scanner8.tm is: state, read bit, write bit, L/R, next.
Its SHA-256 is:
  df6ec639713c4ae7bb3656e59c833dd55ca6336a46bea8327eca639341b34662

The construction changes binary association of the same 191-token AX word.
The complete 3,700-site primitive instruction word and all ordinal successor
edges remain identical to the diagonal source. A full free-algebra check
also verifies the entire emitted stack and final gate formula.

The regrouped source has seven-zero address runs. The original scanner's
threshold is too short for this grammar. We extend it by one state, using
the scanner-eight repair previously present in pa_consistency_research.zip:
  native 34/0 becomes 0 L 1999
  native 1999/0 is     0 L 75
  native 1999/1 is     1 L 2
Native label 1999 avoids collision with this compiler's AX labels 2000+.

Eight simultaneously certified contextual folds then give:
  134 inherited controls + 1 scanner control + 68 readers - 8 folds = 195.
The 32 exhaustive local cases take 1, 3, or 5 steps and do not read or change
the tape outside their two specified cells. Both unfolded and folded tables
pass every one of the 4,815 arbitrary-register symbolic primitive contracts.
All opaque register-block lemma rows remain unchanged. The blank startup
reaches exactly the original complete clean frame after 59,164 transitions.

Verification uses only Python 3's standard library:
  python verify.py
It works from any current directory. Run without -O. The optional --quick
switch skips the two runtime contract families and states that omission.
The reference_pa195 subdirectory supplies the unmodified original checker
and its pinned local dependencies, including source provenance and licenses.

Proof status
------------
These are executable mathematical certificates with the inherited paper
soundness argument. Positive finite simulation durations and exact startup
transfer halting equivalence through the unchanged ordinal source. Combined
with the supplied PA source proof this gives the paper-level PA-formalizable
equivalence between nonhalting of this table and Con(PA). This package does
not claim a new Lean/Rocq kernel-checked theorem for this exact literal table.
It also supplies no minimality or lower-bound result.

Principal files
---------------
grammar.json: new AX association, with the original macro word preserved.
folds.json: eight disjoint state pairs and their replacement actions.
local_fold_certificate.json: complete local whole-tape quotient traces.
source.json: primitive source sites and complete ordinal control flow.
unfolded203.native.tm: full table before contextual folds.
pa195_scanner8.native.tm: folded table in the inherited native labels.
pa195_scanner8.tm and labels.json: dense table and exact native conjugacy.
startup_certificate.json: complete finite-support blank startup endpoint.
validation.json: recorded quantified-runtime and structural results.
verify.py: deterministic reconstruction and replay of these obligations.
