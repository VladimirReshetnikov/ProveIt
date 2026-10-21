# Attribution and scope

The baseline machine and source, source language utilities, and allocation
algorithm are from Vladimir Reshetnikov's ProveIt repository at commit
`aa66d0a33f1f8237a348899eb8095b045a502832`, under
`Computability/BusyBeaver/Research/ZFC/`. Source utilities come from
`candidate-k215/source_language.py`; the allocator, engine filter, and helper
come from `candidate-k215/alternatives/context-returns/code/` and its evidence.
Their notices and applicable inherited licenses are retained in `licenses/`.
The local allocator changes only its input-path defaults. It is used as a
restricted synthesis model, not as an accepted runtime theorem.

This contribution adds the application of alphabetic-tree prefix capacities
to source zero runs, the thirteen globally shared closed rotations, the compact
3,720-byte rotation certificate, verification scripts, exact source metrics,
the compact five-left-edge obstruction, and the recorded unsuccessful scanner
allocation experiments. It uses standard preorder tree-slot / Łukasiewicz
encoding; it does not claim that this underlying tree encoding is new.
The contribution was prepared with AI assistance on 21 October 2026.

No 214-state correctness theorem, no accepted new binary table, no proof of
unconditional nonhalting, and no new proof-assistant endpoint are claimed.
