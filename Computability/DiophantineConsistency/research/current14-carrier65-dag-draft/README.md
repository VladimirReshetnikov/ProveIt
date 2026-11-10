# Current 14-variable equation: 65-gate DAG source draft

This is an **uncompiled proposal**, not a Lean result. `generate.py` reads the
pinned inert graph in `research/carrier65-independent/INCOMING_CARRIER65.json`
and emits `Current14Carrier65DAG.lean`. The generator does not import or run
code from the graph. The historical graph's coefficient binding is not used;
the fourteen coordinates and four port values are arbitrary.

The proposed `ArithmeticDAG` has fourteen input leaves, four port leaves,
three literal leaves, and 65 binary gates. Its proposed count statements say
37 multiplications, 16 additions, and 12 subtractions. It includes a concrete
later-consumer certificate intended to prove every node is an ancestor of the
output, hence all 65 counted gates are live. `all_inputs` and `all_ports` are
separate proposed statements. Fixed integer leaves and inputs cost zero under
this arithmetic-circuit convention; it is not a bit-complexity measure, an
optimality claim, or a count of nodes in the expanded expression tree.

The essential separate proposed theorem `value_eq_carrier` states evaluator
equality to `Carrier65.value` for every commutative ring and every assignment
of ports and coordinates. The graph groups `ell` as `E * (k * Y)` and `S` as
`i * (Delta * c²)`, while `Carrier65.core` groups those products to the left;
associativity should reconcile them. Powers are to be expanded as repeated
products. The proof is an untested candidate and may need staging to stay
within resource limits. **The graph count establishes nothing about the
maintained equation unless this semantic equality also checks.**

No `totalDegree = 150` result is proposed here. The separate external audit in
`research/carrier65-independent/` reports factor degrees 22, 18, 62, 2, 46
and a degree-150 monomial coefficient `-8 * beta^88`; it is not a Lean degree
theorem. A Lean exact-degree proof would need both a kernel-checked upper bound
and a nonzero degree-150 coefficient, with a nonzero beta hypothesis or a
checked specialization to the actual positive beta port.

The [independent source review](../../reviews/current14-carrier65-dag-draft-independent/)
passed for all nodes, input/port mappings, consumer entries, and the arithmetic
comparison including multiplication association. A guarded no-Lean preflight,
an allocated Lean run, and terminal audit remain outstanding. The graph's
association with the TeX/PDF page remains the existing externally reviewed
transcription boundary.
