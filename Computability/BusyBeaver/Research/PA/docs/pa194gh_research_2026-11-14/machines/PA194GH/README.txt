PA194GH — explicit AX generalization with cached-head Shift
=========================================================

Literal binary, single-tape, blank-start TM; 194 working states, 388 rows.
Start state 0; head coordinate 0; blank symbol 0; two-way infinite tape.
Halt state 194 has no transitions and is excluded from the working count.
Table SHA-256:
b9fadcb197c33895603c71b7119bc92b1772c01960804e8850e2a66dd39a995e

This is a new combined command implementation: AX's saved theorem is
U(c,h), with the binder c supplied explicitly by the AX instruction;
MP returns its conclusion in the top without pushing a dummy zero;
Shift halts exactly when the cached head equals one. It is a fallback
194-state construction, not a claim of a sub-194 solution.

The full mathematical command proof is proof.tex. It includes arbitrary
carried stores, numerical stack-zero aliases, a reserved-zero MP compiler,
the shorter generalization word, the final Pop (not Shift) required for
refutation detection, and primitive-recursive witness constructions.
The new command-level interface is calibrated to the same numerical
calculus as the primary family. The repository's incomplete physical and
logical iPRA calibration to PA remains an explicit inherited obligation.
This package does not provide an end-to-end Lean/iPRA proof of Con(PA).

Reproduction (Python 3.10+, standard library, assertions enabled):

    python3 -B build.py
    python3 -B check_commands.py
    python3 -B independent/check.py . --output independent/results

build.py reconstructs the exact raw and folded tables from frozen G inputs
and five fixed-row edits, compares every shipped source artifact, verifies
all 4,754 arbitrary-register source outcomes and all 28 contextual fold
cases, and checks equality of the whole blank-start tape at step 57,922.
The independent check rederives four list-sweep induction lemmas from the
literal candidate rows; it does not import the builder or its arithmetic
box oracle. These checks are executable symbolic evidence, not a proof
assistant kernel. The complete source has 3,653 primitive sites.

Native labels (machine.native.tm) have start 74 and halt 254; labels.json
binds them bijectively to dense labels. Raw 201-state table raw.native.tm
uses 134 fixed controls plus 67 AX readers; folds.json merges seven pairs.
The source nodes, grammar, sites, and resolved instruction graph are all
provided explicitly. PROVENANCE.json pins copied inputs and changes.

Optional source search:

    g++ -O3 -std=c++17 search/source_search.cpp -o search_gh
    ./search_gh 3000000 202611140377 search/replay

The score is 134 + raw readers - optimistic helper matching. A score
below194 would still need compatible fold selection, full source checking,
and a complete logical argument. The source search permutes seven heads,
varies each head's parameters, exchanges selected premises, considers four
gate associations, and changes the shared source grammar. No lower bound
for arbitrary Turing machines follows from its results.

Original compiler/runtime ancestry and notices are retained in licenses/.
See the enclosing report for the complete current-corpus comparison,
absolute-versus-relative proof status, and further research questions.
