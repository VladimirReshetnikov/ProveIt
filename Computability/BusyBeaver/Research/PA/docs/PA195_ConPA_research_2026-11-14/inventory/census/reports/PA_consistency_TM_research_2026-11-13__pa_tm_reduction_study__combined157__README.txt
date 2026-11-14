COMBINED SOURCE: 157 INTERNAL NODES, 3,573 PRIMITIVE SITES

Result and scope
----------------
combined157.tree.json is a new representation of the experimental combined
negation/MP source in ProveIt. Its 3,573 primitive instructions and all their
ordinal control-flow successors equal those of combined197.tree.json.
The number of distinct internal tree nodes falls from 159 to 157. The longest
path changes from 38 to 41; the longest run of zero path bits remains 6.
The clean source seed remains ordinal site 25, path 100000.

This is NOT a 157-state Turing machine. No smaller binary transition table,
Lean kernel certificate, or PA consistency biconditional is supplied by this
bundle. The source inherits the semantic obligations of the existing combined
negation/MP proposal. Its scratch-zero and adapted command-compiler arguments
are separate from the representation equality checked here.

Reproduction
------------
Use Python 3.10 or newer. No third-party package is needed for the main check:

    python3 verify_combined157.py

The checker reads both source trees beside itself, checks the instruction
syntax, counts distinct internal nodes, and independently resolves source
control flow by (1) binary path arithmetic and (2) ancestor intervals. It then
compares all 3,573 resulting ordinal rows. The recorded output is
combined157_receipt.json. The alternative flat path/opcode representation is
combined157.sites.json.

Why the source equality is sufficient
------------------------------------
Both sources have configurations (i,r), with i the ordinal instruction index
and r the nine natural-number registers. Increments, decrements, jumps, and
halt are interpreted by their resolved ordinal rows. Equality of every row
therefore makes their one-step transition functions identical for every
configuration, including both zero and positive decrement outcomes. Induction
on any finite run length yields identical source runs and identical halting
behavior, from the seed or from any other ordinal configuration. The source
paths differ; the register semantics do not.

This argument is elementary and can be arithmetized in PA. The bundle does
not contain that formal derivation, and equality of source semantics alone
does not show that a particular binary table executes the new paths.

How the representation was found
--------------------------------
A seeded finite search applied global, directionally safe reassociations
((A,B),C) <-> (A,(B,C)), allowing temporary increases in grammar size.
The resulting witness was subsequently checked directly by complete CFG
equality, so its validity does not depend on trusting the search or its
rotation filters. The main witness came from seed 2, at zero-based proposal index 3,724
within the recorded 300,000-proposal run. Search failure beyond this witness
is not a lower bound.

Physical allocation experiments
-------------------------------
experimental/ contains separate, explicitly exploratory data and code. The
retained-group allocation estimate for combined157 is 200, despite its
157-node grammar. Reassociation loses some of the previous table's shared
reader-state opportunities. Run:

    python3 experimental/estimate.py

estimate_receipt.json records the exact decomposition. It is only a layout
heuristic; it is neither a machine nor a bound on all possible allocations.

The anonymous-label allocator experiment is described in
experimental/README.txt. It provides an identity positive control and an
UNSAT result for one restricted allocation model. Neither proves a global
state-count lower bound or any PA consistency result.

Provenance
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 38b84bce90b7d1c24c3319c0ff58d8ef92d96b21
Baseline source path:
Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/negation-mp197/source.tree.json
Its exact SHA-256 is recorded by verify_combined157.py. The baseline source
combines the negation rewrite from pa_consistency_research_2026-11-13.zip
and MP-success rewrite from conpa_tm_comparison_and_reduction_search.zip.
Original PA196 machine and calculus: James Chang. The broader compiler
lineage includes Andrew James Wade and ProveIt contributors. Original notices
and licenses are retained under licenses/. The upstream authors did not
review this new representation or the allocation experiments.

The new checker and transformations in this bundle are supplied under the
MIT No Attribution terms retained in licenses/LICENSE.ProveIt. This does
not remove the retained James Chang MIT attribution requirement.
