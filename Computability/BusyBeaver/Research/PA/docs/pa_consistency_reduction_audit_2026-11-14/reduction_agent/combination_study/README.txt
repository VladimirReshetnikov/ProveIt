COMPOSING AXIOM-EMITTER AND MODUS-PONENS CHANGES

This bundle contains four explicitly checked source/physical implementations.
It does not contain a machine with fewer than 196 working states. It does not
provide a new PA proof of the consistency biconditional.

Run (Python 3, standard library only):
    python3 reproduce.py

The fixed incoming diagonal and separate-head AX grammars are composed with
the MP-success-H change from the earlier incoming comparison. At the source
level node163 = (node6,node55) becomes (node6,node147). At the physical level
native row 164/1 changes from 1 R98 to 1 R130. This removes 23 source sites.

The optional short-negation change replaces every structural macro expression
(node49,(inc1,node65)) by (node37,(inc1,node64)). The register meanings are
push;incrementT;cons versus drainTtoX;incrementT;pair-and-quadruple.
The arithmetic identity needs scratch register 7 to be zero on entry. The
old incoming audit established this condition for its earlier program; this
bundle checks the new physical implementation of the changed source and does
not claim a new global scratch invariant or a completed proof-command compiler.

RESULTS
name                         states  sites  branch contracts
---------------------------  ------  -----  ----------------
diagonal_mp_h                   196   3677              4785
diagonal_mp_h_short_neg          197   3461              4497
separate_mp_h                   196   3650              4750
separate_mp_h_short_neg          197   3434              4462

Every listed table has the advertised graph-reachable state count, preserves
the inherited boxed register routines, passes all complete symbolic-frame
instruction contracts, and reaches the exact standard clean seed from blank
in 58,154 steps. The symbolic checker represents arbitrary natural register
values and arbitrary permitted gaps using its inherited register/list lemmas.
It is executable evidence, not an independently generated Lean kernel proof.
The literal tables, source paths/CFGs, selected folds, and receipts are in
results/. Dense tables start at 0 and use the state count as the halt label.
The native tables start at 74 and use 254 as the distinct halt label.

PROVENANCE
Inputs/compiler.py, inputs/symbolic_runtime.py, inputs/support.py, the two
AX grammars, and the frozen PA196 reference files are copied byte-for-byte
from docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip in
VladimirReshetnikov/ProveIt at 906367250a7f96c923147b10df392294bced7be5.
The upstream reference table/program is James Chang's PA196. Its MIT license
is preserved in inputs/LICENSE.JamesChang. The archive's ProveIt license
is preserved in inputs/LICENSE.ProveIt. The inherited research code retains
its original attribution and license notices.
The optional shorter-negation construction comes from
pa_consistency_research_2026-11-13.zip; the MP change is also independently
replayed in PA/pa196-vs-u208/source-search/negation-mp197/replay.py.

Run python3 screen_ties.py to repeat the 100-grammar, 200-combination
portfolio screen. The input grammars and the complete count receipt are
included. The four selected representatives additionally have the full
physical checks described above.

Run python3 scanner_first_return_control.py to reproduce the correction to
a prior scanner rejection argument: the parent itself first returns to root
after 120 steps with a gap-filled intermediate tape, and reaches the actual
successor frame only after 462 steps. The shortened candidate first returns
after 118 steps. Its first-return mismatch alone is therefore insufficient
to reject a complete macro contract; the separate full symbolic checks and
subsequent trace behavior remain the relevant evidence. No inference from a
finite prefix to blank-tape nonhalting is made.
