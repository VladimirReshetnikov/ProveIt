# Independent source review

PASS, source only. The pinned inert graph is reproduced exactly by all 86 parsed nodes: 14 inputs, four ports, three literal nodes, and 65 topologically ordered binary gates (16 add, 12 subtract, 37 multiply). All 85 listed consumers are later actual consumers, providing paths to node 85 by increasing indices. An isolated generator execution reproduced the draft byte-for-byte.

The checker independently transcribes the actual `Carrier65.core/value` definitions and compares all major blocks and final expression to the circuit after normalizing multiplication association. In particular, `ell` is `E * (k * Y)` in the graph versus `(E * k) * Y` in the carrier, and `S` is `i * (delta * c²)` versus `(i * delta) * c²`; these match by associativity. The intended theorem quantifies arbitrary commutative rings and all four arbitrary ports. This is an external source comparison, not a proof that its Lean tactic succeeds.

The count/liveness statements concern the listed circuit and do not assert minimality. Topology, consumer certificate, counts, liveness, and essential `value_eq_carrier` semantic bridge are proposed Lean declarations only: no Lean run was performed and no theorem is claimed. No external PDF/file binding follows from this draft.
