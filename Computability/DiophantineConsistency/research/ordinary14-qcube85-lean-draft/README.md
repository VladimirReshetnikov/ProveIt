# Source-only literal 85/56 q-cubed graph

`P85QcubeGraph.lean` is generated literal `Expr (Fin 14)` source, **not an elaborated or compiled theorem**. The generator pins the independently reviewed 85-row candidate and `--check` reproduces exact source bytes without Lean. Slot 6 is positive X, slot 7 is the positive q-cubed quotient s, slot 8 is the original first-root coordinate, and slots 12 and 13 are gamma-old and h. Ports are beta, K0, MC and MF. Parsing, elaboration, resource use, source/object/Init and transitive provider ancestry, a graph count theorem and external file association are untested.

The external 84↔85 comparison uses the ring identity `X=q*w`, `gamma_prime=gamma_old+w`, `Y=q³*s`, so `E*q=U*w`. Its model proof still needs literal field/evaluation clients and **both** positive maps. For 84→85 it must derive `gamma_prime>w` from the modified graph's own positive zero before taking the natural difference; the separately source-reviewed `../ordinary14-modified-carrier-gamma-model-draft/` assumes the exact natural carrier, Pell coordinates and R≥3 rather than deriving them. For 85→84 it must obtain `q|X` and a positive quotient from the model-level parent calibration; the separately drafted `../ordinary14-modified-carrier-model-facts-draft/` gives only an explicit-premise Mersenne cancellation step. Neither an external standard-integer decoder nor an uncompiled draft can be treated as an already proved model client.

A future graph comparison must prove casts and slot updates without confusing natural truncated subtraction with difference-ring subtraction, and then connect this graph through the uncompiled 85↔86↔87↔88 and parent model clients. This packet does not prove a graph count, degree, iPRA endpoint, compact port/file association, or global minimum. Before any Lean run, independently review all exact source/object/Init and transitive provider routes, check the established disk/resource guard and coordinate an exclusive allocation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-qcube85-lean-draft/make_graph.py --check
```

Independent source review is recorded in
`../../reviews/ordinary14-qcube85-lean-draft-independent/`.
