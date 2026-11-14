Bounded QH6 grammar search
==========================

This optional experiment searches reassociations of the exact 190-token
QH6 emitter word. It is not needed to verify the delivered machine.
The accepted 194-state table remains unchanged by this search.

The frozen seed contains all 135 unquotiented H6 fixed controls and the
Q grammar. prepare_inputs.py derives source-leaf attributes from the actual
six-increment source nodes, rather than reusing coefficient-four bounds.
The general screen considers fixed/reader context folds and recognizes
the three-increment subtree through state 330. In this screen, score s
corresponds to 135+s states; the delivered baseline scores 59 and a
193-state nomination would require score at most 58, with zero address
penalty and simultaneous fold compatibility. Every promising nomination
would still require exact source, startup, and universal physical checks.

Sources are adapted from the pinned repository inputs: screen_h6.cpp from
pa194h6_conpa_2026-11-13/research/decoder/seven/, and search_qh6.cpp from
pa194qn_research_2026-11-13/research/logical_emitter/search_adaptive.cpp.
The modifications select the coefficient-six screen and seven-entry
parameter-vector type and correct the stopping thresholds for 135 fixed
controls. Register permutation mutations are disabled in the inherited
adaptive source, so this run preserves the complete macro word.

Reproduction (C++17 and Python 3.10+):
  python3 -B prepare_inputs.py
  c++ -O3 -std=c++17 search_qh6.cpp -o /tmp/search_qh6
  /tmp/search_qh6 qh6.seed.txt leaf_attrs.txt /tmp/qh6 120 202611140617

The stopping condition is elapsed wall time. A fixed random seed therefore
does not promise the same number of mutation slots on another machine.
The log, source hashes, input hashes, and results.json record this run.
A failure to find a smaller allocation is not a state-count lower bound.
