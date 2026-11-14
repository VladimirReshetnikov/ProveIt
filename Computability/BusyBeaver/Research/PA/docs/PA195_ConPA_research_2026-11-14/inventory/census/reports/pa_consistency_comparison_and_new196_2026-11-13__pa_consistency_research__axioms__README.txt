THREE NEW 196-STATE PA-CONSISTENCY SEARCH LAYOUTS

This directory contains exact binary tables and reproducible executable
certificates for two primary layouts of the diagonal-vacuity calculus and a
third scanner-oriented layout in search/. All use 196 working states and
have an additional halting label 196. None is a solution to the requested
strict target of fewer than 196 states.

Run, without Python -O:

    python3 verify.py

Only Python 3 and its standard library are required. The verifier rebuilds
both literal tables, compares every supplied source site, checks the complete
relative control flow of every arithmetic macro against the pinned upstream
source, verifies the emitted formulas in a free algebra, checks all symbolic
instruction contracts for an arbitrary complete register file and an affine
gap, and executes the complete 58,154-step literal blank startup.

The symbolic register-block calls are justified by the unchanged upstream
M6 runtime interfaces. This executable certificate is not a new Lean-kernel
proof, and no new Lean theorem for either machine is claimed.

  diagonal196: 191 macro tokens, 3,700 primitive sites, 4,815 symbolic cases;
             9 AX stack items; guarded diagonal-vacuity clause.
  separate196: 190 macro tokens, 3,673 primitive sites, 4,780 symbolic cases;
             10 AX stack items; unconditional diagonal clause as a new head.

The search/scanner_best196 layout keeps the separate-head 190-token word
and has 69 AX reader nodes with 7 compatible folds. It also includes a
source-CFG-preserving exterior rotation. It passes all 4,780 contracts and
reaches the complete startup frame after 58,294 steps. Its six remaining
short-scanner obstructions leave the deletion of scanner state 34
unjustified by this simulation certificate. Reproduce the checked
196-state layout with the instructions in search/README.txt.

Both primary layouts have 68 AX reader nodes and 6 compatible simultaneous folds. The
retained fixed control has 134 states, giving 134+68-6=196 working states.
Every one of the 196 labels is reachable in the transition graph. This
ordinary graph assertion does not assert that every state occurs in the
actual infinite blank run.

PROVENANCE

The baseline is jamesyc/BusyBeaver at
407cdc356f6b586635e71ac92be394255f4bfea4, with literal table SHA256
 e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8.
The reference files are unchanged excerpts from that pinned MIT-licensed
repository. The James Chang license is retained in LICENSE.JamesChang.

The diagonal-vacuity mathematical reduction was already present in
VladimirReshetnikov/ProveIt, pinned here at
dc523e7b06ffb414093c90aa035500ca283e5f75, in
 docs/incoming/pa_consistency_research_2026-11-13.zip
and its sections/diagonal.tex. That prior text is retained verbatim as
proof/diagonal_prior.tex; it describes its older 199-state implementation.
Our diagonal196 changes its physical layout, not its 191-token emitter.
The file proof/changes.tex explains the additional separate-head variant.

The compiler and symbolic executor were adapted from the published
ProveIt incoming research package
 docs/incoming/pa_tm_comparison_and_reductions.zip
 pa_tm_research/distributed198/{compiler,symbolic_runtime}.py.
The ProveIt repository license is retained in LICENSE.ProveIt.
New verifier files, layout grammars and fold certificates accompany the
same MIT terms. Exact input/output hashes are in SHA256.json.

CALIBRATION SCOPE

The logical translations and the internal consistency biconditional require
the mathematical arguments in the accompanying report. The upstream Lean
endpoint explicitly exports PA-proves(nonhalting implies Con(PA)); it does
not by itself export the converse. The archive does not represent the
Python checks as a substitute for that missing exported Lean theorem.
