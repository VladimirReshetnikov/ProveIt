PARAMETERIZED GENERALIZER: REPRODUCIBLE 196-STATE SOURCE EXPERIMENT

This directory is a secondary research contribution. Its concrete machine
has 196 working states and does not improve the 194-state frontier. See
theory_note.tex for the exact command identity, four-field continuation
encoding, preservation proof, and limitations.

Rebuild the concrete table and check the symbolic compiler contracts:

    python3 build_parameterized_generalizer.py
    python3 check_prefix_semantics.py

The builder regenerates parameterized_generalizer/{machine.tm,
machine.native.tm,raw.native.tm,labels.json,folds.json,
local_fold_cases.json,sites.json,instructions.json,receipt.json}.
The prefix checker regenerates source_prefix_receipt.json.

Repeat the bounded association search (Node.js, no dependencies):

    node search_source.js 15000 20261116

The search writes parameterized_generalizer/search_replayed.json.
search_receipt.json records the discovery run, including its wall time.
Search heuristics are not proofs of a lower bound.

An additional unproved direct-top interface was screened with:

    node search_source.js 15000 20261117 direct_top_188.grammar.json 193

Its best score remained 195. Its proof-stack completeness is open;
direct_top_188_search.json is a search receipt, not an acceptance claim.

machine.tm uses five whitespace-separated fields per row:

    state read_bit write_bit direction next_state

Its start state is 0, working states are 0 through 195, and halt is 196.
Directions are L/R. All tape cells are initially zero. The head starts at
coordinate zero on a two-way infinite tape. machine.native.tm retains
construction labels and start 74/halt 254; labels.json maps dense labels
to these native labels and includes the halt as its final entry.

Dense table SHA-256:
ca44252ab21560889a4bccb05cd68a7c07f319a7292609e3c4250e80dac06190

The compiler checks the 4,799 source outcomes via the inherited symbolic
arithmetic block interfaces, all 28 contextual fold cases on the final
simultaneous table, graph reachability, and complete blank startup.
These are stronger than short execution sampling, but do not constitute
a new Lean theorem or an independent reconstruction of the literal
arithmetic-block simulation. The written reduction uses the original
calculus/PA calibration and the new exact AX offset-addition identity.

Provenance and attribution of the inherited construction modules and
data are recorded in PROVENANCE.json. Preserve the upstream notices and
the accompanying licenses in the containing distribution.
