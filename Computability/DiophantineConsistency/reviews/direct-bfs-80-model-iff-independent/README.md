# Independent review: direct-BFS 80 graph / internal halt model iff

The frozen accepted `DirectBFS80ModelIffCorrected.positive_model_iff` proves a **two-way model-level equivalence** in every `ORingStructure V` model of IΣ₁. For arbitrary natural ports `p : Fin 4 → ℕ`, it assumes the four natural equalities

```
p 0 = betaNat,
p 1 = DirectBFSSymbolicKernel.paramKernel rho,
p 2 = lowNat,
p 3 = betaNat + highNat.
```

Under these four explicit hypotheses it equates existence of a strictly positive `v : Fin 10 → V` with `InternalZero (graph (integerPorts p)).output v` and existence of an internal model time `T : V` with `ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0`. The time and valuation may be nonstandard. Both directions use the **same p and the same kernel-generic 80 graph**, with the directly indexed BFS symbolic kernel specified at port 1; the theorem is not yet a fixed closed tuple specialization, an iPRA derivability theorem, the 75-row trace equation or the original 14-variable PDF.

The zero-to-halt direction applies the previously reviewed `DirectBFS80ModelHalt.graph_halts` with the same natural port equalities and witness. The halt-to-zero direction applies the reviewed `DirectBFSHalt80Graph.halt_zero_of_model_ports` with the same `p` and internal time after deriving the four corresponding model casts: beta using `beta_model`, the kernel by `congrArg` and the actual `DirectBFSFourFieldsPacking.kernel` definition, and the mask values using `low_eq` and `high_eq`. No extra model-port premise remains in the final theorem. `InternalZero` is the Lean-defined graph zero in the model's difference-ring setup; no external file semantics or bytes are parsed by this theorem.

`check.py` rehashes source/copies, runner, Lean binary, direct providers, output and logs; verifies equal before/after direct-import snapshots and first resolution; and checks 59 retained chunk receipt hashes. It also confirms the final, forward and reverse search paths presently first resolve the same `Direct80Graph` object `95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4` and direct-BFS symbolic-kernel object `69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f`. This is post-hoc object selection and direct snapshot evidence, not a complete serialized transitive/producer-time or package/dynamic ancestry audit. Exact four direct provider paths and hashes appear in `check-output.txt`.

The accepted output object is `4858598cb5d931d788b6a0a76e00029ecd47cd24062217afa4059713aba9116d`; its inner Lean exit is 0, stderr empty and the named report is exactly `[propext, Classical.choice, Quot.sound]`. The runner enforces a named axiom whitelist and rejects coded diagnostics. Earlier inline, conditional and full-port attempts timed out; a separate forward-branch diagnostic had a nonzero Lean exit and missing namespace. Timeouts alone do not establish a particular root cause. The terminal precedes final assertions; the author reports outer exit 0 but no separately retained actual outer-exit receipt was found. No independent Lean replay was performed. External gzip/JSON-to-symbolic-kernel equality and the eventual iPRA client remain separate obligations.
