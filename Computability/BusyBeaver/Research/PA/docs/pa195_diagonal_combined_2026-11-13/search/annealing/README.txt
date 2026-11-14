Optional bounded search evidence
================================

No search is required to rebuild PA195DC. Its exact table and verification
are in the machine/ directory at the root of this package.

These searches explore binary reassociations of the AX macro tree, permutations of
the six heads, and independent parameter renamings in each unrestricted
head. They begin with the existing diagonal195 and separate195S grammars,
19 logically safe antecedent/rho variants, or two classical equivalents
of the diagonal Gamma axiom. The last run uses PA195DC's six changed core
transitions and also permits contextual folds involving fixed-core states.

The ordinary cost is the number of binary reader nodes minus a maximum
compatible family of two-cell history folds. Add 134 fixed states to obtain
the working-state count. Near the target, fold compatibility is checked
against the final simultaneously folded local table, not inferred only
from pairwise eligibility. Penalties filter scanner-depth constraints.
Fitness is only a candidate filter: any purported improvement still needs
independent Python reconstruction, source/logic binding, all source-step
contracts, exact initialization, and complete local fold certificates.

Build with a C++17 compiler, for example:

    g++ -O3 -std=c++17 search_order.cpp -o search_order
    ./search_order diagonal.txt leaf_attrs.txt diag_order 600 984194
    ./search_order separate.txt leaf_attrs.txt sep_order 600 713194
    ./search_order variants.txt leaf_attrs.txt variant_order 600 118194

    g++ -O3 -std=c++17 search_dual.cpp -o search_dual
    ./search_dual dual.txt leaf_attrs.txt dual_adaptive 600 618194

    g++ -O3 -std=c++17 search_dc.cpp -o search_dc
    ./search_dc dc.txt leaf_attrs.txt dc_order_broad 300 64194

The numeric inputs contain all fixed transition rows and initial source
shapes. They do not read a repository or use network resources. Inputs count
INC/INC2/INC4 in their expanded macro word, so positional head permutations
operate on the intended formula boundaries. The 600/300 arguments are
wall-clock limits in seconds; proposal counts depend on the executing host.
The seeds reproduce the random sequence until the time cutoff.

The source derives from the optional C++ annealer in the supplied archive
PA195_ConPA_research_2026-11-14.zip, construction195/search. The modifications
add explicit head-order tracking, head swaps, order-aware parameter renaming,
a new seed pool, an adaptive pool for the longer dual-Gamma sources, and an
optional expanded fixed-core fold universe. ProveIt snapshot:
5ed5a41fa5932433111eea096311364c6087e8e3.

summary.json and the five final logs record the observed searches. They are
bounded unsuccessful searches, not proofs of a 195-state lower bound.
Preliminary runs with an incorrect collapsed-token positional convention
were discarded and are not included or counted in that summary.

Final recorded outcome
----------------------
The five corrected runs proposed 39,661,078 moves and accepted 7,153,880.
No run found a candidate below 195 states. Both newly found 195-state
secondary witnesses passed complete finite implementation checks; their
folders explain the additional logical calibration limits. They are not
used as the main PA195DC theorem's basis.

A final radius-two neighborhood test examined the union of occurrence and
global subtree rotations around both secondary seeds. It checked 49,513
distinct endpoint trees: 25,196 for negative Gamma and 24,317 for rho-swap.
Every endpoint required at least 61 reader states after the tested exact
compatible-fold optimization, hence at least 195 total states. For this
neighborhood test, a scanner-depth penalty did not suppress any possible
sub-195 hit. This is a result about that finite neighborhood and fold model,
not a lower bound for Turing machines or arbitrary compiler optimizations.

    g++ -O3 -std=c++17 neighborhood_unfiltered.cpp -o neighborhood
    ./neighborhood neighborhood.txt leaf_attrs.txt neighborhood

The independent portable verifiers in secondary195/ and negative_gamma195/
accept the primary packet's baseline195 directory as their one argument.
Their retained tables passed those replays. The negative-Gamma logical
calibration is explicitly optional; its finite certificates alone are not
an end-to-end proof of the consistency equivalence.
