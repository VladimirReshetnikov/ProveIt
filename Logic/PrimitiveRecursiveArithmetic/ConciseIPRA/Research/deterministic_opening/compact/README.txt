CONTINUATION FUSION FOR THE EXISTING CONCISE-IPRA CHECKERS
=======================================================

This directory contains three independently useful, completely standalone
implementations of the existing proof protocol. Their mathematical rule
basis is unchanged. The improvement is a verified reordering of goal
rewriting and scope allocation, explained in TRACE_PROOF.txt.

Pinned comparison: ProveIt commit
17898ea7e6a1300dfdcad71040d5daeed67916d4.

                       Tokens    AST nodes    Normalized bytes   Gzip-9
Compact control           265          306                 516      332
Compact fused             267          302                 508      330
AST control               260          278                 602      344
AST fused                 263          276                 580      343
Native validated control  358          413                 788      460
Native validated fused    360          409                 780      458

The separate authenticated token leader remains 256 tokens (283 AST nodes,
594 bytes). Thus the observed byte coordinate improves from 516 to 508 and
the observed AST coordinate from 278 to 276, in different programs. There
is no claim that one new program improves all three coordinates, and no
claim of an absolute lower bound or a new mathematical axiomatization.

The entire acceptance module is counted, including JSON reading, scope
checking, proof recursion, and the final ACCEPT verdict. CPython 3.12.14
ast.unparse plus one LF supplies the normalized text. These files contain
no docstrings, so docstring removal has no effect. Gzip-9 uses mtime=0 and
is informational.

PUBLIC INPUT CONTRACTS

The compact and AST profiles inherit the documented canonical integer/list
certificate language and closed guarded Eq/D public-goal contract. They
do not independently validate that public-goal grammar. The native profile
retains the complete public-goal validator of its upstream control. The
profiles have different accepted auxiliary languages, so comparisons are
always made within a matched control/candidate pair. In particular the
native control classifies two inherited auxiliary fixtures differently
from the guarded controls; the new native checker preserves its behavior.

The ordinary same-domain bi-interpretation of each control carries over
unchanged because the same input certificate is accepted by the new program
exactly when it is accepted by its matched control. Both equality and all
formula translations remain the inherited ones. This program-equivalence
proof is written mathematics, not a new Lean or Rocq formalization.

HOW THE CHANGE WORKS

The old code assigns a rewritten goal, constructs a hypothesis, decrements
the scope floor, then opens the continuation. The new code constructs the
hypothesis first and inlines the goal rewrite into the continuation:

    c(i(rewrite(goal), [(k := k - 1)]), new_context, k)

The argument evaluation order matters: rewrite(goal) is computed at the old
scope; the second argument allocates the fresh name; only then does i run
at the new scope. Rewriting and hypothesis construction commute because a
rewrite requires a nonempty major, whereas introduction changes the goal
only when that major is absent. The full accepted-trace proof treats the
partial opening operations, error cases and the local scope state.

FILES

- code/compact.py, code/ast.py, code/native.py: the three new complete modules.
- baseline/: authenticated, unmodified source controls and token leader.
- fixtures/: 21 authenticated upstream positive and negative fixtures.
- PROVENANCE.json: pinned repository paths and exact Git blob hashes.
- TRACE_PROOF.txt: universal accepted-trace equivalence argument.
- evidence/metrics.json: independently regenerated complete-module metrics.
- evidence/validation.json: the finite implementation-check record.
- reproduce.py: provenance check, measurement and regression runner.

REPRODUCTION

    python3 reproduce.py
    python3 code/compact.py < fixtures/computation_zero_local.json

Acceptance requires exit status zero and exactly ACCEPT followed by LF.
The reproduced checks comprise 252 standalone executions (normal Python
and python -O), 500 deterministic instruction mutations checked in three
matched pairs, and one fresh-parameter boundary checked in all three pairs.
Every accepted differential run also leaves the same instruction prefix.
The tests check the implementation; TRACE_PROOF.txt supplies the universal
argument. Ordinary finite memory and recursion limits are not part of the
mathematical presentation.

Attribution: inherited files are from Vladimir Reshetnikov's ProveIt under
the MIT No Attribution license, included as LICENSE-ProveIt.txt.
