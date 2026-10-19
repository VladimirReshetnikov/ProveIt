# Exact-step state packing by forced read symbols

Let M be a deterministic binary Turing machine. For each working state q, let A(q) be a subset of {0,1}. Assume a proved invariant of the intended executions establishes that whenever q is entered, the scanned symbol belongs to A(q). This must cover arbitrary permitted parameter values and every invocation, not merely finite tests.

Partition the nonempty domains into forced-zero states, forced-one states and two-symbol states. Pair any forced-zero state with any forced-one state. Let pi identify each chosen pair, leave other states distinct, and keep the halt state separate. In the quotient, its zero row is the projected row of the forced-zero member and its one row is the projected row of the forced-one member. Every row's write bit and movement remain unchanged; its target is mapped by pi.

For every intended execution, induction on the step number proves that the quotient configuration is exactly (pi(q), head, tape). Indeed, the invariant selects the unique member whose row is enabled for that symbol. Thus the quotient takes the same movement and write and enters the projected next state. Halting and its exact time are preserved, as are the whole tape and head at every step.

No separate incoming-edge restriction is necessary. This theorem applies to a complete composition only after all component entry contracts and the forced-read invariant are proved for that composition. It does not permit assigning arbitrary read domains from empirical trace coverage.

If there are n0 forced-zero and n1 forced-one states, disjoint pairing saves min(n0,n1) states. Multiple-entry components can participate if every caller's entry is projected correctly. A common invariant-failure sink may additionally be shared only when its rows and meaning actually agree.

Examples in this research are the two paired roles in the 19-state biased copier. The four modes of the fixed-header writer also supply four forced-one states: unseen4 and seen0/1/2. Its finite header contract has exactly 16 old/new cases, all represented in anchor_mode_writer_guards.json, and reads no exterior cells. Therefore exhaustive symbolic replay of these 16 complete cases is sufficient to prove those guards universally for that component.

The template oracle's leaf-output states are candidates for forced-zero roles only under its exact leaf-path-plus-zero-padding contract. A complete proof-search runtime must establish that padding premise and preserve it until the oracle call.
