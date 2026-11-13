# Bounded two-gate cone screen for the eta/zeta-natural 85 graph

This screen pins the exact 85-row boundary probe and inspects each maximal predecessor cone whose internal gate outputs are used only inside that cone. For every output with a cone of at least three gates, it checks replacing the entire cone by two binary `+`, `-`, or `*` gates, using the graph inputs, ports, earlier non-cone wires and literal integers 0 through 4. The second gate must use the first gate's result, possibly twice. This is an exact-output identity search for all input and port values, not a zero-equivalence search.

The deterministic checker covers 35 cones and 165,779,916 ordered gate candidates in that finite family. It evaluates one reproducible assignment modulo 1,000,000,007 and indexes the possible second-gate operands algebraically; every candidate is rejected by that assignment. Nonzero target residues are explicitly verified, including for multiplication by zero and subtraction of the intermediate from itself. A failed modular evaluation is an exact counterexample to a polynomial identity over the integers. Four further deterministic assignments are applied only if a candidate survives the first. The receipt records the assignments, each cone's size and available-wire count, and the total enumeration.

This excludes only the stated replacements. It does not establish a global operation lower bound, exclude special fixed-port identities, simultaneous rewrites across different cones, more than two replacement gates, new constants, changes of variables, or a different equation with an equivalent zero set. No equation reduction, Lean proof, model transport or endpoint is claimed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta85-two-gate-cone-screen/check.py | cmp - research/ordinary13-eta-zeta85-two-gate-cone-screen/receipt.json
```
