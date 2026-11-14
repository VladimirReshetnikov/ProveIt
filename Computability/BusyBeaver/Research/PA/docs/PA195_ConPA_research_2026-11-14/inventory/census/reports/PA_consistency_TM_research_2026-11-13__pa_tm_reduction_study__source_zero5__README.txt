A SOURCE WITH 159 INTERNAL NODES AND AT MOST FIVE CONSECUTIVE ZEROS

This is a source-program witness. It is not a 159-state Turing machine and
not a construction below 196 states. It has 3,812 primitive occurrences
and 159 distinct internal binary-tree nodes. Its ordered primitive
operations and complete ordinal control graph equal the original PA196
program exactly. The maximum path length is 37, and every source path
has at most five consecutive zeros. The original bounds were 38 and six.

Run: python3 verify.py

The verifier uses two separate control-graph resolvers, compares every
source control row, and rejects a changed increment operand. It requires
only Python 3. OriginalProgram.lean is a byte-pinned source input by
James Chang, retained under LICENSE.JamesChang. This packet does not run
Lean or assert a new kernel theorem. The source seed is ordinal 25,
whose new path is 10100000.

A path bound of five could support a return scanner detecting six zeros,
saving one physical control compared with a detector for seven zeros.
The dynamic tape invariant, decoder allocation, arithmetic contracts,
and blank startup remain separate requirements. Contextual reader aliases
in the original table depend on preceding bits and cannot be assumed to
survive this source geometry. No physical allocation is included here.

source160_zero5.json is the earlier, dominated 160-node search witness.
The verifier and receipt use the improved source159_zero5.json only.
