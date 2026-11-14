Discovery artifacts and the negative result below 194
======================================================

No verified sub-194 machine was found. The accepted PA194Q is reproduced
by ../reproduce.py without any search. The present directory records
bounded searches and local exclusions, not a global lower bound.

Root search families
--------------------
root_search_summary.json and the four .log files give original counters:
- Axiom-head variants: 2,832,997 proposal slots; best reader objective 60.
- Focused axiom-head search: 1,664,002 slots; best objective 65.
- Separation-matrix variants: 1,761,744 slots; best objective 61.
- Head-parameter permutations: 1,766,625 slots; best objective 60.

The fixed controller part adds 134 states. These proposal slots include
skips/repeated grammars, and are not distinct accepted machines. A score
from the heuristic screen is not a proof of literal source simulation.
The accepted 194-state endpoint separately passes the full builders and
independent source/tape checks. The 200 retained parameter hits are a file
cap, not a count of distinct successful constructions.

The source variants include exchange of curried premises, reversal of
primitive relation encoding, and equivalent separation matrices. Each
accepted logical rewrite needs its own proof. Unproved shorter logical
schemata were excluded. source_variants.py describes a wider exploration
set, not a list of certified machines. make_variants.py and gate_variants.py
can regenerate template inputs from the frozen construction references.

Representative bounded search commands, from this directory:

    c++ -O3 -std=c++17 logic_anneal.cpp -o logic_anneal
    ./logic_anneal variants.txt leaf_attrs.txt rerun_logic 240 202611140051
    ./logic_anneal gate_variants.txt leaf_attrs.txt rerun_gate 240 202611140053
    c++ -O3 -std=c++17 parameters.cpp -o parameters
    ./parameters parameter_seeds.txt leaf_attrs.txt rerun_parameters 300 202611140054

occurrence.cpp retains the alternate occurrence/shared-DAG rotation
search. Programs were refined during the discovery; the delivered source
records the final search family, while the actual logs retain original
counts and seeds. Time-bounded runs do not have hardware-independent
iteration counts. Reproduction of an accepted table uses the frozen
construction grammar and folds, not these stochastic searches.

Further invariant and local searches
-----------------------------------
The self-contained invariant/ addendum contains the independently bound
source invariant, specialized complete-tape replay, conservative local
windows, three finite enumerators, additional grammar code/inputs/logs,
and detailed scope notes. Its completed grammar runs record 15,895,250
proposal slots; interrupted runs add at least 4,572,000. The finite local
screens return no contraction under the restrictions documented there.

Run its verify_inputs.py to recompute its inductive invariant and exact
blank seed. run_local_screens.py requires a C++17 compiler. collect_affine.py
recomputes the symbolic contexts. These are optional discovery checks;
none is required for the validity of the delivered 194-state machine.

Search logs are evidence of the performed bounded work, not evidence
that 193 states are impossible. New logical encodings, a different
controller, nonlocal transformations and stronger invariants remain open.
