Optional experiment: rotate four X-to-H-plus-one loops
====================================================

Scope
-----
This alternative still has 243 working states. It is independent of the
archive's main 242-state borrowed-return construction and is not used in its
proof. It changes only inherited state 142's two rows and rotates four source
fragments. It gives no further working-state saving.

For every pair of natural numbers H=a and X=b, each old and new fragment
returns H=a+b+1 and X=0, leaves the other seven registers unchanged, and takes
exactly 3*b+2 source instructions. The source checker verifies the induction
stages, the four matching exits, and every surrounding source-context edge.

The retained runtime evidence is affine replay using inherited box contracts:
6,455 source leaves and 8,386 guarded cases, with positive literal progress.
Expanded runtime replay has NOT been performed for this optional variant.
The checker's --expanded mode is available but is not part of the reported
evidence. This branch supplies no additional Lean, Rocq, or PA endpoint.

The recorded exact blank boot reaches the inherited frame after 407,975
steps. Its sparse and dense interpretations agree. The experiment does not
use that eight-step increase to claim any state-count benefit.

Run from this directory after extracting the whole archive
---------------------------------------------------------
Python 3.10 or newer, standard library only; run with assertions enabled.

  python rotate_h.py
  python check_h_source.py
  python check_h_runtime.py

The scripts locate their inputs relative to their own paths; a different
current working directory is also supported. Runtime imports use the
archive's ../../reference/runtime tree. The candidate defaults to rotate_h/.
The scripts overwrite only their experiment outputs under rotate_h/.

rotate_h/construction.json records the earlier construction-stage status
SOURCE_ROTATION_TRUE_TABLE_RUNTIME_UNCHECKED. It is intentionally retained as
an earlier status and is regenerated with that status by rotate_h.py. The later
source_context.json and affine-runtime.json record the completed checks; the
construction-stage string does not describe the final validation status.

Inputs and source provenance
----------------------------
All baseline inputs are from ProveIt commit
e58338db7545909907e07a7603e8eb88625c527a and its recovered incoming71 packet.

sites_logical.json is the exact combined243 logical source, also retained in
the archive's machine/sites_logical.json. SHA-256:
3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4

zfc_combined243_old.tm is the exact inherited-label combined243 baseline from
../../reference/combined243/zfc_combined243_old.tm. SHA-256:
4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300

support/check_source_244.py is copied byte-for-byte from the recovered packet's
research/grammar/historical_source/check_source_244.py. SHA-256:
5bfffffe31e6801ba0dc9eec1eafd53c4b612278d3e2484e127ad585825699c4
Only its Program parser and successor semantics are imported. Its separate
historical command-line checker is not the checker for this experiment.

Other exploratory files
-----------------------
  python semantic_fragments.py

This reproduces semantic_groups.json: bounded arithmetic signatures for
closed source fragments. Matches would be proposals, not universal proofs;
the recorded search found no duplicate signatures in its selected pool.

  c++ -O2 -std=c++17 borrow_two.cpp -o borrow_two
  ./borrow_two ../../machine/zfc_return242_old.tm

This optional bounded local search tries single-row replacements of 27/1
to serve both old return contexts 15 and 171. The recorded search tested 964
replacements and found none within its stated tape-window and step bounds.
It is not an impossibility result. The search is independent of the H loop
rotation and is not part of the source or runtime correctness evidence.
