# Bounded searches below 194 states

The search did not establish a machine below 194. This directory records
portable finite searches and the exact source inputs. It is separate from
the accepted PA194C/PA194CZ construction and its mathematical proof.
Read SEARCH_NOTES.md and final_receipt.json for scope and exact bounds.

The A/B inputs are the supplied 67−7 and 68−8 PA194 readers. The C input
installs the six-row Combined controller; CZ adds the proved zerojump row.
Each text input contains the full fixed machine core, terminal attributes,
190-token word, and initial association. No external checkout is needed for
the C++ searches. The successful parent grammars are also included.

Compile from this directory with a C++17 compiler, for example:

    g++ -O3 -std=c++17 code/association_search193.cpp -o /tmp/association_search193
    g++ -O3 -std=c++17 code/plateau_search193.cpp -o /tmp/plateau_search193
    g++ -O3 -std=c++17 code/mixed_association193.cpp -o /tmp/mixed_association193
    g++ -O3 -std=c++17 code/mixed_exact193.cpp -o /tmp/mixed_exact193

Run in a separate output directory, since the programs create candidate
files in their current directory. Exact commands and seeds are retained in
final_receipt.json. The cycle budget in those commands is the originally
configured cap, not a claim that an interrupted run completed that cap.
Use `completed_logged_cycles` for a deterministic prefix replay of an
interrupted anneal; no unlogged tail is included in the stated bounds.

For a plateau command the two seeds are A's input and B's .shape file.
Its budget counts parent expansions. The retained witnesses have score 194,
not 193. Their `.shape` and `.word` files can be decoded using:

    python3 reconstruct_grammar.py witnesses/beam_small_raw.json /tmp/grammar.json

Such decoding does not replace source-CFG binding, full runtime contracts,
blank initialization, and a simultaneous-quotient proof. The search fitness
field `effective_lower` is inherited terminology for the proposed net reader
allocation; it is not a mathematical lower bound on Turing-machine size.

Source attribution: association_search193.cpp derives from the association
search shipped in the supplied PA194 `(2)` archive. The same source packet
retains its preceding PA195/compiler/runtime attribution. The new files add
a plateau traversal, all-incoming fixed-control candidates, and unconditional
identical-row closure. No search result is claimed as a new proof kernel.
