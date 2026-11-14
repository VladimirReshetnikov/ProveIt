RESTRICTED ALLOCATION OBSTRUCTIONS

Run python3 verify_hall.py with assertions enabled. It regenerates domains
from the actual source layouts, original PA196 reader bindings, protected
engine rows, and helper traces. It then checks an explicit Hall witness:
the union of the allowed labels of a set of source nodes has smaller
cardinality than that set of nodes. No z3 import or solver is needed for
these three cases, because the domain obstruction is already decisive.

The model fixes every recognized compatible old reader, protects the listed
core rows and contextual helpers, and injectively assigns new source nodes.
It does not allow changing those fixed readers or using a new context-sensitive
alias among new nodes. Thus the obstruction is not a general lower bound on
the source program's implementation and is not a lower bound of 196 states.

allocate.py is adapted from ProveIt's incoming archive
pa196_research_2026-11-13.zip, search/allocation/allocate_symmetric.py, at
dc523e7b06ffb414093c90aa035500ca283e5f75. It removes the exploratory label-order
constraints and adds maximum domain matching and finite Hall certificates.
The original source157, essential158, and layout158 are retained unchanged.
The reference helper files come from that archive's
search/rotations/allocator-screen directory. Their main CLI paths concern
older research constructions; only their parser and decoder functions are
used here. This package does not claim those historical main CLIs reproduce
the present result. Original MIT licenses are preserved.

To use allocate.py on a different source after domains admit an injection,
install z3-solver. Any SAT output still requires complete runtime and startup
verification; a prefix-only result is not an accepted machine.
