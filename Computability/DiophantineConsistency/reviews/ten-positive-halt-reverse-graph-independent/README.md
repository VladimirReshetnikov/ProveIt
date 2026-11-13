# Independent review: internal halt to symbolic-port 80 graph zero

`TenPositiveHaltReverseGraph.halt_zero_of_model_ports` is a semantic model theorem over an arbitrary `ORingStructure V` satisfying `IΣ₁`. It takes a natural tuple `p : Fin 4 → ℕ` and a **model-valued** `time : V`; its halt premise is exactly `ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0`. Its remaining explicit hypotheses are model equalities

```text
(p 0:V)=Exp.exp (590069:V)-1
(p 1:V)=paramKernel rho
(p 2:V)=low
(p 3:V)=high+(Exp.exp (590069:V)-1).
```

Here `paramKernel` is the `CompactSymbolicKernel` function opened by the source, and `rho` is its symbolic row data. In particular, the second equation is **not** arbitrary p₁: the model cast of `p 1` must be this symbolic kernel value. The theorem does not supply this port equality, establish it for retained external K0 bytes, or define the halt premise as a literal syntactic iPRA proof. Its exact conclusion is existence of a positive 10-coordinate model valuation whose selected 80 graph output is `InternalZero`, at that same p.

The source calls `CompactHaltFirstSeed.halt_first_seed` once, obtaining one δ, one `word=perturb (baseCell (haltRow time)) δ`, its definability and `PackingInput`, and the associated `t,sY,n,eta,zeta,gamma` and `SeedRelations`. It derives the phase and size of the same packing rank, uses the seed's rank decomposition to obtain the same r, and feeds these witnesses plus the same K, N, stride, word, power and transport data to `TenPositivePackingReverseGraph.packing_seed_zero`. The port hypothesis is what supplies the latter theorem's `(p 1:V)=K`. The exported final theorem asserts existence only; it does not expose a particular valuation or retained-coordinate equalities.

This is a one-way **model** halt-to-symbolic-port-graph implication. It does not establish the graph-to-halt converse, derive the four model port equalities for a named external equation, identify the differing retained external K0, or prove an internal iPRA proof exists. In particular a model-valued halt time is not itself a claim that an actual standard execution halted.

`check.py` checks the accepted `observations/halt-attempt01/terminal.json`, current and copied source, `run-halt.py`, output and logs against hashes, scans the accepted source for `sorry`/`admit`, and independently resolves the first object for each direct import against the runner's hardcoded pins. The `PackingReverseGraph` selected object is byte-identical to the separately reviewed packing adapter. Exact three direct provider paths/hashes and terminal/source/runner hashes appear in `check-output.txt`. Accepted object SHA `f66996ade1c7634045981deb8296819176b12dbdf648aaa00c394abfa8d3b3ba`; author axiom report `[propext, Classical.choice, Quot.sound]` with no error, warning or `sorryAx`.

No Lean replay was performed. Direct selection does not establish full transitive selection, source-object, package or dynamic-library provenance.
