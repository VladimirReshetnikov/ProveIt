# Arithmetic-circuit proof simplification review

Snapshot: ProveIt `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.
All paths below are under `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`
unless marked otherwise. Line counts are physical lines from Python `splitlines()`.
This review proposes changes; it does not assert a new consistency endpoint.

## 1. Use the existing power certificate for the generated power lemmas

**Priority: high.** `ArithmeticDAGPowers.lean:24-42` already proves `run_power`:
numeric labels, checked multiplication edges, and the existing topology imply
all labelled registers are powers of the designated base. The generated
`GapCircuitSteps66.lean:2436-3120` instead has 86 individual power proofs, and
`SplitCircuitSteps59.lean:2591-3443` has 107. Every one invokes `ring` after
rewriting previously proved power facts. This is duplicated proof work, rather
than a need for a new power-reasoning framework.

Emit an exponent-label list, one closed `PowerStep` certificate proved by
`decide +kernel`, and a private specialization of `run_power`. Preserve all
193 public theorem names and their exact types as one-line applications. In
the split family, `SplitJointPower59.lean` already carries the parent labels
and a private `natural_old_steps` theorem. In an integrated refactor, extract
that shared data/certificate into an upstream label module imported by both
Steps and JointPower; do not import a later recipe module and introduce a cycle.

Existing example:

```lean
theorem natural_power_25 (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 25 = naturalRegister p x 20 ^ 4 := by
  rw [natural_step_25]
  simp only [natural_power_24]
  ring
```

Candidate after introducing the shared certified helper:

```lean
theorem natural_power_25 (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 25 = naturalRegister p x 20 ^ 4 :=
  natural_power p x ⟨25, by decide⟩ (by decide)
```

The label zero is a sentinel for “no asserted power specification,” not a
claim that the value equals the zeroth power. Keep that interpretation and
the nonzero-label premise. Prove the certificate against the actual stored
node list, not against a second unlinked copy. This changes proof structure
without changing the circuit, operation count, or polynomial.

## 2. Share the specialization of `run_node_equation`

**Priority: high, low architectural risk.** `GapCircuitSteps66.lean` contains
484 `natural_step_*` declarations, `SplitCircuitSteps59.lean` contains 515.
Their proof bodies all call the same general theorem, repeat the same circuit
and topology constants, rewrite the same length, and decide one bound.

Define one circuit-specific theorem taking `i : Fin 484` or `Fin 515`, with
right side `(nodes.getD i.val (.literal 0)).evalAt p x (naturalRegister p x)`.
The existing explicit public equations then have bodies such as
`natural_step p x ⟨10, by decide⟩`. Keeping their public types explicitly
spelled out preserves good rewrite behaviour and human-readable interfaces.

The prepared candidate combines ideas 1 and 2. Measured source changes are:

| Family | Original lines | Candidate lines | Original nonblank | Candidate nonblank |
|---|---:|---:|---:|---:|
| GapCircuitSteps66 | 3,122 | 2,354 | 2,378 | 1,775 |
| SplitCircuitSteps59 | 3,445 | 2,563 | 2,607 | 1,932 |
| Total | 6,567 | 4,917 | 4,985 | 3,707 |

Thus 1,650 physical lines (25.1%) and 1,278 nonblank lines (25.6%) disappear
while 999 step statements and 193 power statements remain. The 193 `ring`
calls disappear. These are measured **candidate-source** savings, not measured
build-time or proof-term savings. A finite certificate can itself be expensive;
benchmark before claiming faster builds. The label tables and helper overhead
are included in these counts.

Artifacts: `generate_steps_candidate.py`, `generated-candidate/generated-steps.patch`,
the full candidate sources, and `generated-steps-metrics.json`. The generator
is non-mutating and outputs a separate tree. Before upstream integration,
update `tools/generate_split_recipe_steps59.py` and the gap wrapper using the
same template; applying only the generated-source patch will make upstream
generator `--check` comparisons fail. Existing public statement preservation
does not establish performance or successful elaboration.

## 3. Factor the recurring topological induction

**Priority: medium.** Compare `ArithmeticDAGSemantics.lean:97-109`
(`run_eq_of_node_equations`), `ArithmeticDAGDegree.lean:65-82`
(`value_degree_le`), and `NaturalDAGQuartic.lean:43-53`
(`run_nonnegative`). Each uses strong induction on a register, rewrites
`run_node_equation`, and obtains each dependency bound from `htop` twice.

A generic `run_invariant` theorem takes a property `P : ℕ → R → Prop`
and one local preservation premise. Equality, nonnegativity, and degree
bounds become three small instantiations. `CircuitRefactoring.lean` includes
the complete proposed theorem and clients with the same upstream statement
shapes. The helper is roughly the size of one old induction; savings are
amortized across the clients. Its value is that dependency-bound bookkeeping
has one implementation and each client exposes just its mathematical invariant.

Do not force `run_power` into an unsuitable abstraction merely to unify all
inductions. Its base register is defined by the actual run, so the unrestricted
local preservation premise needs either a seed mechanism or a different
formulation. Three straightforward clients already justify this helper.

## 4. Move sum-of-squares syntax facts to a common module

**Priority: high for maintenance, moderate for line reduction.** The same
private `eval_sumExpressions` induction appears in `DAGQuartic.lean:83-86`,
`NaturalDAGQuartic.lean:110-113`, and `QuadraticRegisterSystem.lean:70-73`.
Immediately afterwards, each file proves its own `expression_zero_iff` by
the same `List.map_ofFn`, `Fin.sum_ofFn`, and
`Finset.sum_mul_self_eq_zero_iff` calculation.

Add a common theorem on an arbitrary residual family `Fin n → Expr σ`:
evaluation of the finite sum of residual squares is zero iff every evaluated
residual is zero. Keep it in a dependency layer below these compilers, near
`QuarticSyntax.sumExpressions`. Every compiler then uses one application;
the prototype includes signed-DAG and natural-DAG clients. The mathematics
and witness domains remain explicit. This is specifically an integer SOS
fact, so do not generalize it to arbitrary rings where squares may cancel.

Similarly, `DAGQuartic.lean:166-178` has a parameterized sum cost lemma,
whereas `QuarticCost.lean:65-74` has the special case with per-term bound 5.
Make the parameterized lemma public and let the special case delegate to it.

## 5. Certify commutative operand swaps instead of special-casing them

**Priority: medium, especially useful before another circuit variant.**
`GapCircuitTranslation66.lean:16-76` and `SplitCircuitTranslation59.lean:16-76`
are nearly the same proof. The ordinary finite `NodeRel` certificate excludes
exactly one row (421 or 452); the proof handles that row separately with a
register equation and `ring`. Both are multiplication with reversed operands.

Add `NodeRelComm`: for addition and multiplication it accepts either the
ordered pair of related operands or the swapped pair; subtraction retains
the existing ordered `NodeRel` condition. Prove its evaluation theorem once
using `add_comm`/`mul_comm`. Then the finite reference certificate can cover
the swapped row too, and the bespoke `hswap` branch disappears. The supplied
`NodeRelCommutative.lean` is a standalone candidate implementation.

The next step is to share the translation proof skeleton: parameterize the
two node lists, input-prefix equations, reference map, finite certificate,
and output correspondence. Reuse the existing local-equation uniqueness
theorem. Do not hide each final semantic equality as a field of a structure
and call that proof compression; the common theorem must derive it from
local data. Preserve all actual source indices and output bounds.

## 6. Reuse the existing syntax-degree bound earlier in the import graph

**Priority: medium.** `QuadraticRegisterSystem.lean:18-33` already defines
`syntaxDegree` and proves `polynomial_degree_le` by structural induction.
This is a suitable reusable abstraction but currently lives downstream of
`NaturalDAGQuartic`, so importing it into the earlier compilers would create
an import cycle. Move the definition and theorem to an independent
`ExpressionDegree` module importing `Representation` and polynomial degrees.

Then routine `wire_degree`, `rhs_degree`, and small residual degree bounds
can prove a numeric syntax bound and apply the shared soundness theorem.
Likewise, `ArithmeticDAGDegree` already offers certificate-driven circuit
upper bounds. Use those existing facilities before writing more large
chains of `degree_add`, `degree_sub`, and `degree_mul` applications.

There is an important limit: syntax bounds do not exploit cancellation.
`ShortFrontier.degree_main_norm` first proves a lower-degree algebraic
normal form; that identity must remain. Apply the structural bound to the
proved normal form, not the unreduced source, and keep exact-degree lower
bounds/leading-coefficient witnesses separate. The repository's comments
already make this distinction correctly.

## 7. Package the append invariants used by natural registers

**Priority: lower, local cleanup.** `NaturalRegisterProgram.Program.push`
(`NaturalRegisterProgram.lean:72-98`) repeats the same old-index/new-last-index
split once for topology and once for allowed nodes. `eval_old` and `eval_last`
(`129-152`) repeat list-append arithmetic again at the semantic level.

Add reusable append lemmas near `ArithmeticDAGSemantics`: topology of
`nodes ++ [n]` from the old topology and `n.dependencies < nodes.length`,
and indexed-predicate preservation under append. Use the existing `Op.dependency_lt`
and `Op.allowed` to instantiate them. This avoids a disruptive redesign of
`Program`; its intrinsically bounded `Op` type is already the right public
interface. A wholesale change of evaluator representation should wait for
profiling evidence, because it would cause wider proof and cache churn.

## Validation policy

Only label an artifact compiled after an actual Lean 4.32.0 invocation succeeds.
Run `#print axioms` on the proposed semantic helpers and representative generated
theorems. Preserve kernel checking of finite certificates. Rebuild downstream
register and recipe modules to verify rewrite compatibility, then regenerate
from the source scripts and require byte identity. Count generated data,
helpers, and wrappers in any reported source saving. The proposed work should
not change theorem hypotheses, output domains, arithmetic data, or the status
of an end-to-end equivalence proof.

## Actual validation result

`CircuitInvariant.lean` compiled successfully with the pinned Lean 4.32.0 compiler (exit 0). It checks the generic `run_invariant` theorem and both same-statement uniqueness and degree-bound clients. All three `#print axioms` results are exactly `propext`, `Classical.choice`, and `Quot.sound`. The 206.11-second wall time was dominated by shared-environment contention and is not a performance comparison. See `CircuitInvariant-direct.log` and `validation.json`.

The broader `CircuitRefactoring.lean`, `NodeRelCommutative.lean`, and full generated Steps candidates remain uncompiled; only the successful static signature/node-label audit is claimed for the generated candidates. Interrupted baseline dependency builds emitted no proof diagnostics. No further compilation was attempted after the isolated invariant check passed.
