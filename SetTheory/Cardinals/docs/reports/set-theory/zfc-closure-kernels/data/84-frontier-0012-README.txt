DECODER FRONTIER RESEARCH — 18 OCTOBER 2026

STATUS
No binary blank-tape ZFC-consistency machine with fewer than 246 working
states was found. This directory contributes a broader source transformation,
complete restricted search records, a discovery accelerator, and independent
replay code. No new end-to-end Lean/Rocq theorem or ZFC/PA proof object is
claimed. The recorded failures are failures of specified sufficient contracts.

WHAT IS NEW IN THIS DIRECTORY
1. Two successive closed rotations are composed while preserving original
   decoder-state ownership. The complete census covers 56,873 ordered
   two-move recipes, 4,678 shape-admitted recipes, 2,277 distinct source DAGs,
   and 9,108 emitted variants. There are 6,102 state-cover outcomes and 3,006
   sufficient-checker rejections, with no accepted sub246 table. A state-cover
   outcome means that a set of successful universal instruction-contract
   replays, together with fixed macro support, uses at least 246 labels.
   It does not mean all those labels are reachable from the blank tape.

2. Arbitrary shared-tree rotations need not be restricted to closed components.
   Break/Continue levels can instead be rebased when every source successor
   is preserved. Both edges of every decrement are checked. The complete
   single-rotation study has 331 rotations and two rebasing policies (662
   recipes); 522 pass its exact CFG test, 92 change a decrement scope, and
   48 cannot express the required control target. The shape bounds remove
   370 of the passing recipes. There are 76 distinct admitted source DAGs.
   Four emission policies give 304 attempts: eight lack a direct inherited
   control encoding; among the 296 supported attempts, 210 obtain a state
   cover and 86 fail the sufficient affine checker. The source study uses
   natural DFS instruction order; the double-rotation study uses the supplied
   35-site priority list followed by the remaining sites in DFS order.

3. Seven admitted 203-node source layouts actually change control levels,
   affecting 1, 120, 242, 242, 115, 1 and 1 leaf occurrences. They are exported
   in source_rebase_examples.json. A separate checker uses literal bit-by-bit
   path walking, with independent path arithmetic, to check all 8,390 successor
   edges of each layout: 58,730 edges in total. This is source equivalence,
   not a new machine-size record. The ordinary closed rotations and previous
   201-node source layout remain prior work; no historical priority is claimed
   for reassociation, compiler rebasing, or CFG bisimulation as general methods.

4. affine_screen.cpp accelerates the inherited Python sufficient oracle. It
   preserves the macro proof rows and cannot validate a changed macro. It is
   cross-checked on all 8,391 baseline guarded cases and the exact 492 used
   rows, plus three invalid decoder mutations. The small state-cover witness
   lists are subsequently checked with the inherited Python engine. Compiler
   discovery and proof replay remain distinct operations.

MATHEMATICAL SOURCE ARGUMENT
Let a finite binary decoder tree have leaves in left-to-right order. A program
counter denotes a leaf by walking its bits, using zero bits after the finite
word ends, and stopping at the first leaf. Suppose two trees preserve this
ordered set of occurrences and the Inc/Dec/Halt labels. Break/Continue leaves
may differ, provided their normalized successor occurrence is unchanged.
Require the successor occurrence of every increment and both decrement
branches to agree as well. Relate two source configurations when their
normalized leaf indices agree and their entire register vectors agree.
Each nonhalting instruction changes the registers identically and reaches
related configurations; halt leaves correspond. This is a one-instruction
bisimulation, valid for all register vectors and without assuming that any
component terminates. The root of either tree normalizes to leaf zero.

The discovery implementation locates normalized leaves by exact integer
intervals of a finite prefix code. The independent example verifier instead
walks individual bits through the tree. Neither implementation uses floating
point arithmetic. Source equivalence still needs a binary simulation and a
calibrated blank initializer before it can establish the requested endpoint.

FILES
  composed_rotations.py          Two-move generator and origin-aware emission.
  rebase_rotations.py            Scope rebasing with complete CFG preservation.
  affine_screen.cpp              C++ discovery oracle and state-cover witnesses.
  affine_acceleration.py         ctypes interface, baseline and mutation controls.
  case_order.json               35 source sites used only for search priority.
  verify.py                     Portable temporary-copy verification driver.
  verify_records.py             Replays every recorded machine-search decision.
  verify_source_examples.py     Independent literal path-walking source verifier.
  source_rebase_examples.json   Seven explicit rebased source DAGs.
  double_all_fast/results.json  Complete compact machine-search ledger.
  double_all/results.json       Earlier complete graph-size census.
  double_ties/results.json      Census restricted to the 40 inherited runtime ties.
  rebased/results.json          Complete source-rebasing study.
  vendor/                      Minimal attributed computational dependencies.
  vendor-manifest.json          Exact imported-file identities and archive paths.

REPRODUCTION
Python 3.10+ and a C++17 compiler are sufficient; no network, Python packages,
Lean or Rocq installation is required. Assertions must be enabled.

  python3 verify.py

The verifier works in a temporary copy. Its default checks imported identities,
compiles the C++ discovery helper, checks all baseline cases and mutation
controls, verifies the seven source examples, and independently replays every
saved double-rotation decision with the original Python sufficient oracle.
Byte-identical tables for the same source reuse an already checked proof.

  python3 verify.py --full

This also regenerates both the complete double-rotation census and the source
rebasing census, then compares their stable counts. The study has explicit
source shape bounds (at most 203 nodes, zero run at most seven, path depth at
most 40), fixed emission policies, and a 2,000-rule sufficient oracle. Search
fuel exhaustion and unsupported symbolic rules are not global impossibility
proofs. The full driver allows one hour for each discovery search; failure to
finish on a particular host must not be reported as completed coverage.
Set ZFC_DECODER_TEMP_PARENT to a writable directory to choose the verification
workspace. Optional manually run commands are in verify.py.

ATTRIBUTION
The exact computational dependencies are retained byte-for-byte from
ProveIt's incoming zfc-sub246-research-20261018.zip. The imported NOTICE files
and license boundaries are preserved. The original 254-state machine and
proof-search program are attributed to Mira-Cult, the upstream formalization
to Jeff Ketchersid, the inherited compiler to Andrew James Wade, and later
runtime/permutation/calibration work to the referenced ProveIt contributors.
This directory does not relicense that material. The inherited macro proofs
are not reproduced in full by this minimal computational dependency selection;
they remain required mathematical dependencies of the affine oracle. The
complete positive246 reference is supplied elsewhere in the enclosing research
package or available from the attributed incoming source.

The current repository audit was at ProveIt commit
79957d7b290ec807d434959a0c6ecc06ee90b419. Imported packet sources themselves
refer to their original ProveIt pin 8cdc55ff9281b0aaba49bf74b0b225d57f12b893
and Jeff/zf-254 pin c132d7eae8158cd3a9850ea3eb7251158c3dd821.
