PA195: 195 working states, two symbols, one tape, blank input
==========================================================

The fixed result is pa195.tm, with start state 0, working states 0..194,
and separate halt label 195. Every state/read pair has one transition.
SHA-256: 5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455

Reproduce all executable checks using Python 3 and its standard library:

    python3 build_verify.py

No search, optimizer, solver, network connection, or proof-assistant build
is required. Run without -O, since the unchanged vendored source parser
uses assertions. To reconstruct derived certificates and the unfolded table:

    python3 build_verify.py --export

The --quick switch omits only the two full symbolic-runtime check lists.
It retains exact table reconstruction, literal state census, 28 complete
local quotient traces, all incoming-history checks, independent source
control-flow comparison, free-algebra emitter identity, and full blank
startup. The distributed validation.json is the result of the full run.

Files
-----
pa195.tm                 Complete dense binary transition table.
pa195.native.tm          Same table in inherited control labels.
labels.json              Dense-to-native conjugacy, including halt.
grammar.json             Exact AX macro association; 68 allocated readers.
folds.json               Seven disjoint simultaneous reader identifications.
unfolded202.native.tm    Deterministically compiled parent before folding.
source.json              All 3,700 primitive sites and exact successors.
emitter_tokens.json      The unchanged 191-token diagonal emitter word.
local_fold_certificate.json  22 incoming rows and 28 complete two-cell traces.
startup_certificate.json    Exact complete tape after 58,154 transitions.
validation.json          Full executable verification receipt.
fold_proof.tex           Global halting-preserving quotient argument in PA.
vendor/                  Unchanged compiler/runtime with pinned references.

Mathematical content and verification scope
------------------------------------------
The new grammar preserves the exact primitive instruction word and every
ordinal successor of the incoming diagonal196 program. Two independent CFG
resolvers check all 3,700 sites. The emitters have the same formula stack,
verified in a free algebra rather than by numeric samples.

The 202-to-195 quotient has a global, finite simulation proof. Each deleted
reader can be distinguished from its keeper by the left neighbor written
by its incoming transition. All 28 local cases are exhaustively checked
on two cells, with every other tape cell arbitrary and unchanged. The
positive block durations are 1, 3, or 5. See fold_proof.tex.

The 4,815 symbolic primitive contracts cover arbitrary register values,
both decrement branches, and an affine gap at least 48, using unchanged
register-block contracts from the included Runtime.lean. The largest
recorded symbolic execution length, 497, is not a bound on literal Turing
machine transitions: unary-register blocks may take much longer.

This bundle does not claim a newly kernel-checked end-to-end theorem of
the arithmetic consistency biconditional. The accompanying report must
supply and distinguish the inherited logical calibration and its uniform
PA formalization from the new exact finite compiler/quotient certificate.

Provenance
----------
The reference PA196 is James Chang's upstream revision
407cdc356f6b586635e71ac92be394255f4bfea4, imported by ProveIt.
The diagonal191-token calculus and the reference diagonal196 grammar are
from docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip in
VladimirReshetnikov/ProveIt, inspected at repository revision
906367250a7f96c923147b10df392294bced7be5.

Only the AX association and its physical allocation/quotient are new here.
No formula parameters, head order, antecedent order, gate, register engine,
startup protocol, or mathematical theory changed from diagonal196.
The search happened to allow head-local parameter permutations; the retained
winner uses none of them. Reproduction uses only the retained witness.
