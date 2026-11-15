# Conditional model-length simulation with a coded iterator and clock

`PA194IteratedSimulation.simulateIterated` is a Lean theorem in any model of
candidate PRA whose arithmetic reduct satisfies IΣ₁. It is generic in finite
primitive-recursive codes `next`, `cost`, `frame : Code 1`.
For every model element n, including nonstandard n, it derives

```
good(iterate(next)(n, seed)) ∧
stepper(clock(iterate(next), cost)(n, seed), start) = frame(iterate(next)(n, seed)).
```

The explicit primitive-recursive `iterate next` code starts at the seed and
repeatedly applies `next`; its all-model base and successor equations discharge
the separately required run recurrence of `simulateCodeRun`. Its syntactic
shape matches the scheduler’s `PA194StackCode.dropCode next`, although this
package does not itself import and identify the scheduler module.

The code `PA194CumulativeClock.clock` is explicit primitive recursion: it starts
at zero and at each iteration adds `cost(run(n, seed))`. Its equations hold in
every candidate-PRA model. `PA194ClockInvariantDefinable.invariantDef` proves
the whole invariant is Σ₁-definable when `good` is Σ₁-definable, using
`PA194CodeGraph.modelGraph` for all finite PR codes. The simulation theorem
then applies internal model IΣ₁ induction and the checked stepper composition
lemma, so the clock recurrence and invariant definability no longer need to be
separate assumptions.

These remaining premises are explicit and **not discharged** for PA194's full
source/scheduler run:

* `good` is Σ₁-definable and holds of the initial seed state.
* The literal packed `start` equals `frame(seed)`.
* `next` preserves `good`.
* For **every** good modeled state s, including nonstandard states, the literal
  stepper for `cost(s)` steps from `frame(s)` equals `frame(next(s))`.

No code supplied here certifies an all-site PA194 physical cost, an all-site
source-frame simulation, or a halt correspondence. The theorem is conditional
Lean model reasoning, not an object-theory iPRA proof or either consistency /
nonhalting implication. Its and the component theorems' printed Lean axioms
are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Staged source replay

`check-iterated-simulation.sh` pins and rebuilds five sources in one fresh
output: the conditional induction lemma, cumulative-clock code, invariant
Σ₁-definability proof, coded simulation theorem, and generic iterator specialization. It audits their printed
axioms and refuses `sorryAx`.

The machine root is the separately source-built coherent unified PA194 build,
but the proof of `PA194CodeGraph.modelGraph` is imported from an additional
retained **code-graph overlay**. This overlay also contains other precompiled
PA194/project objects and is searched before the supplied project root because
it contains graph prerequisites absent there. The checker pins the direct
code-graph object, two direct objects, one graph prerequisite and the current
graph source, but neither rebuilds nor authenticates their complete transitive
closure; matching hashes alone do not establish source/object compatibility.
The coherent machine build itself retains earlier startup/header and general
foundations. Thus this is a staged suffix replay with explicit prebuilt
machine, graph and logic prerequisites, not a clean full-closure rebuild.

From the repository root (all paths are session-local):

```sh
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-iterated-simulation.sh" \
  "$PWD" "$base" \
  /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git internal overrides and does not set them.
