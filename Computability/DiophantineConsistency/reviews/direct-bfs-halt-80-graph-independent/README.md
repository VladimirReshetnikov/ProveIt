# Independent review: internal halt to direct-BFS 80 graph

The accepted `DirectBFSHalt80Graph.halt_zero_of_model_ports` is a **one-way**, model-level graph theorem. For any `ORingStructure V` model of IΣ₁, natural ports `p : Fin 4 → ℕ`, and internal time `time : V`, it assumes the machine-215 halt condition and all four model equalities

```
(p 0 : V) = Exp.exp 590069 − 1,
(p 1 : V) = (direct-BFS symbolic kernel : V),
(p 2 : V) = low,
(p 3 : V) = high + (Exp.exp 590069 − 1).
```

It concludes that there exists a strictly positive `v : Fin 10 → V` with `InternalZero (graph (integerPorts p)).output v`. The port equalities are **hypotheses** in this theorem; it does not itself specialize them to a fixed natural tuple or identify any external coefficient bytes. The equation is the kernel-generic 80-row Lean graph at those ports, not the distinct trace75 graph or the original 14-variable PDF.

The proof starts with one `δ` and its **same** canonical `word = cellWord (row time) δ`, `N`, stride and direct-BFS `K` from the reviewed halt-Pell-seed theorem. It uses that word's packing, positive transport and `SeedRelations` witnesses; it derives the required positive beta, positive `w=Exp.exp (R−590069*N)`, rank phase and `r≥4`, with `R=2*r+1`, from the same packing/seed facts. Those same data and the four port hypotheses are passed to `PackingReverseGraph.packing_seed_zero`, which produces the positive zero. The final existential statement does not expose a fixed list of ten coordinates; one should not infer that the temporary vector used in an intermediate graph proof is itself the final output without inspecting the downstream constructor. This packet does not prove the reverse implication, an iff, an iPRA derivability theorem or external PDF/JSON/payload semantics.

`check.py` rehashes the source/copies, runner, Lean binary, selected direct inputs, output and logs, verifies equal direct-import snapshots and first resolution, and checks 59 chunk receipt hashes. Its four direct providers are reviewed `DirectBFSHaltPellSeed` `8d9892b6ff938f9766c042609e1a4bdd78da4769b6b2bd946fb7c275ddcd7762`, `PackingReverseGraph` `aa879b5d70f582eedce7f0d0665d916c3703fb33540925411d96520e746c021e`, `CompactRankResidueJoin` `756f04d7b963bab9c56670afd2652d9ea30671e3e9558c1f6f8c761f04d5da12`, and `Direct80RankLower` `317c0619b647d15f16cfa51455574b88822fb39225a66eb5cbee12a00064a960`. The final selected shared graph, BFS symbolic kernel, four-fields and difference-ring hashes match the corresponding earlier selected objects post hoc. Exact paths are in `check-output.txt`; this is not an independent compile-time transitive-closure or provider-history audit.

The accepted object is `95f9655fe3b57826b1ef5b786396ae31ea089c3e859dbc59e04c355204278de3`; its sole named axiom report is exactly `[propext, Classical.choice, Quot.sound]`, stderr empty, and the runner enforces that report's whitelist and rejects coded diagnostics. Its terminal precedes final assertions; the author reports outer exit 0, but no separately retained actual outer-exit receipt was found. No Lean replay or complete historical/project/package/dynamic ancestry audit was performed.
