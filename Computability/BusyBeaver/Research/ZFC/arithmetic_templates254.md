# Fixed constructor templates in weak arithmetic

`ArithmeticTemplates254.lean` gives literal parameter-free Sigma0 graphs for the live original base4 numerical functions `Code254.rho2` through `rho8`, `bundleC`, `bundleG`, and `bundle`. `ArithmeticCode254` already supplies `rho1`. The new graphs work in every ordered-ring arithmetic structure satisfying `IOpen`; the standard-Nat adapter identifies each function with the maintained `Code254` definition for every input.

The reusable `Circuit` datatype has four inputs, a constant of value 1, and exactly the four original constructor tags: implication 0, membership 1, universal quantification 2, and native equality 3. `Circuit.graph` recursively compiles a fixed finite circuit into a `𝚺₀.Semisentence 5`. At each constructor it quantifies both child values at most the parent value, then invokes the already checked tagged Cantor graph. `tagged_components` supplies both bounds, and `Circuit.defined` proves the graph correct by structural induction. The internal Cantor witness is also bounded by the output. This is a graph compiler for each fixed finite circuit, not a single arithmetic history evaluator with a circuit code as another input.

The specialized graphs preserve the original relative negation `A → F` with `F = 1`, the original existential and conjunction expansions, all eight logical rows, and the exact theory bundle `(C ∧ G) ∧ (membership vacuity ∧ equality vacuity)`. They retain native equality. They introduce no freshening convention or change in binder labels. Coincident labels and zero inputs are included in the numerical equalities. The cyclic formula-decoding alias at code 0 does not change these arithmetic constructor identities; the audit includes `wim(0,0) = 0`.

Each of the ten new fixed functions has three checked interfaces: an arbitrary-`IOpen` fixed graph, an all-input Nat equality to `Code254`, and a `HierarchySymbol.DefinedFunction` instance for the live Nat function using that same graph. The graph definitions have only the displayed numeric arguments; no parameters from an arithmetic model are inserted into their syntax.

The separate maintained checker freshly checks three modules and all three stored audits: `ArithmeticCantor`, `ArithmeticCode254`, then `ArithmeticTemplates254`. It imports the existing checker helpers and uses the maintained constructor checker as its prerequisite. The complete chain passed **97 named axiom probes and 83 callers** under the absolute official Lean 4.32.0 compiler. The template part contributes 41 probes and 36 callers, including arbitrary-`IOpen` clients, all ten Nat comparisons, all ten direct Nat graph instances, and zero/coincident-label controls. The template source has no warnings. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Source and object identities are checked after the run. Ten source-matched project dependencies and the existing Foundation/Mathlib objects are explicitly reused, with Foundation pinned to `32e1a0956a8622fad067328ca1959729a7634428`; those dependency closures are not freshly rebuilt.

The positive bundle graph is deliberately separate from the gates `c ≠ a` and `c ≠ b`. It computes the same bundle value even for inputs rejected by the checker. It does not yet represent the twelve-way row selector, proofcode-zero handling, rejection output 0, or a complete execution history. Output bounds for constructor intermediates do not justify bounding arbitrary rejected-row inputs by the rejection value 0. No internal PA simulation, whole-checker correctness theorem, new Turing machine, or consistency endpoint follows from this component alone.

Source/object identity records, compiler commands, and all 97 axiom reports are retained in the verification JSON and its nested prerequisite records. The stored audit is `arithmetic_templates254_audit.lean`; this package remains separate from the Std-only core runner and umbrella.

Run the maintained checker from the repository root, using an already populated and built dependency checkout and a successful source-verified core evidence record:

```sh
uv run --no-project python -B \
  Computability/BusyBeaver/Research/ZFC/check_arithmetic_templates254.py \
  --repo . \
  --dependency-root /path/to/built/Proofs \
  --core-evidence Computability/BusyBeaver/Research/ZFC/results/code-tuple-order-integration-verification.json \
  --output /outside/both/checkouts/templates-check
```

The output must be new or empty. `--source` and `--audit` accept template-only candidate overrides; the two prerequisite modules and their audits remain the maintained versions. Compiler/library/cache relocation options are forwarded to the existing prerequisite checker. The runner neither downloads dependencies nor invokes a dependency rebuild.
