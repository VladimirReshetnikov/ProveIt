Supplementary formalism research for K218
=======================================

None of these alternative formalisms is used in the accepted 218-state
consistency equivalence. additional_formalisms.tex records the positive
lemmas and the precise remaining calibration gaps.

Finite modal diagnostics (Python standard library only):
    python3 -B check_formalism_diagnostics.py

This verifies the explicit H3 x H3 model and the nine-element upset model.
It checks normality, seriality, B6, and the claimed failed proof steps.
Neither finite structure is claimed to model the full native seed-K bundle.

Exact parameter-register enumeration (optional C++20 research replay):
    c++ -O3 -std=c++20 rename_exhaustive.cpp -o /tmp/k218-rename-search
    /tmp/k218-rename-search parameter_problem.in \
        > /tmp/k218-parameter-best.txt 2> /tmp/k218-parameter-exhaustive.log

The supplied parameter_exhaustive.log and parameter_best.txt are the
complete reference outputs. The search evaluates exactly 6^8 independent
choices in a fixed parenthesization of the 205-node source checkpoint.
It does not search all source trees or all machine allocations.

parameter_problem.json is a readable version of the integer problem.
Its initial nodes are hash-consed source trees, with primitive leaves
represented by [opcode, register]. Its template consists of fixed nodes,
row-specific six-way slots, and binary pair nodes. All 97 templates are
reachable from root 96. The 281 initial nodes need not all occur in any
one choice. Each choice's exact reachable-node count is computed after
global hash-consing of all instantiated pair nodes.

The Python audit check_parameter_problem.py reconstructs this data from
the supplied source checkpoint and verifies the stored histogram and both
minimizers. Invoke it with --source pointing to the intermediate 205-node
sites.json, before the final state-188 source rotation. This source is the
construction's already verified intermediate checkpoint, not a new
unverified formalism.

From this directory, audit the supplied source checkpoint with:
    python3 -B check_parameter_problem.py \
        --source ../../verification/construction/intermediate_sites205.json

The readable supplement is report/research_supplement.pdf (from the packet
root); its LaTeX body is additional_formalisms.tex. The independent
check_modal_countermodels.py records another six-element example and the
same Booleanization obstruction. These diagnostics are supplementary.
