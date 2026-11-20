# From the checked core to object-level iPRA derivations

## 1. The target already exists in ProveIt

The relevant source interfaces were inspected at ProveIt commit
`83421593771f877bc1ae98f4229eb35507bff05b`. The parent report records the
repository paths and source provenance. This package does not vendor or import
the full repository, and does not claim that the upstream project was built in
this run.

The namespace `LeanProofs.ConciseIPRA` provides:

* `PR : Nat → Type`, with constructors `zero`, `succ`, `proj`, `comp`, `prec`;
* `PTm n`, with constructors `var` and `app`, for arithmetic terms with `n`
  free variables;
* `Fm PTm n` for first-order formulas;
* `PRAAx`, containing the PR defining equations, successor axioms, and only
  **quantifier-free** induction;
* `Prf PRAAx Γ φ`, written `Γ ⊢[PRAAx] φ`, for intuitionistic derivability.

The actual final target for a closed arithmetic theorem is an inhabitant of

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] φ
```

The source `IPRADerivations.Foundations.BoundedFormulas` supplies
`bf_reflect`, `bf_cases`, `bf_dec`, `bf_choice`, and `bf_least` for fixed
bounded-formula syntax `BF`. Its `bitAt` constructs a *term* by recursion on
that fixed syntax. This is not a single PR universal evaluator applied to an
arbitrary internal formula code.

The source `IPRADerivations.Foundations.BoundedSyntaxInduction` imports the
scoped syntax `BFm n` and proves `induction`, `induction_at`,
`induction_rule`, and `bounded_induction_closed`. Its implementation applies
`PRA.qfInd` to the equation saying that the compiled Boolean term is one, then
uses bounded reflection to recover the bounded formula. This is the direct
mechanism required by the report.

## 2. Fix numerical encodings before transporting any theorem

Represent a binary word by a length and bit payload, or by the report's
self-delimiting natural-number encoding. Supply fixed PR symbols for length,
bit access, concatenation, bounded list access/update, tuple packing and
unpacking, and finite-table lookup. Malformed codes receive explicit default
values; a separate Boolean validity predicate guards meaningful instances.

Choose a finite multitape machine alphabet and a concrete transition-table
encoding. Define, by fixed PR syntax:

1. `validMachine(m)`, `initial(m,x)`, `step(m,c)`, `accept(c)`, `halt(c)`;
2. `run(m,x,0) = initial(m,x)` and
   `run(m,x,t+1) = step(m,run(m,x,t))`;
3. a PR code bound `C(m,x,t)` for configurations reachable in `t` steps;
4. a trace-code bound, for example a fixed-base digit bound with `t+1`
   configuration slots, and `TraceOK(m,x,t,z)` checking all adjacent pairs;
5. output extraction, length, and accounting predicates for transducers.

The universal parameter is a **finite machine code**, and its evaluation
always has a step bound. The fixed PR function `run(m,x,t)` is legitimate.
Removing the step parameter and claiming a PR evaluator for all PR functions
would be illegitimate.

For every item, construct an actual `PR k` syntax term and the needed
defining-equation derivations via `PRA.comp`, `PRA.precZero`, and
`PRA.precSucc`. A semantic `Nat → Nat` definition alone is not this step.

## 3. Transport the finite kernel

### Bounded search

Implement `bany` as a Boolean sum/signum fold, `ball` as a product fold, and
the witness as bounded minimization with a sentinel. The existing
`bf_reflect` and `bf_choice` interfaces already prove the object-level
reflection/witness principles. Establish the precise representation lemmas
connecting this package's Boolean convention with the upstream numeric bits
zero/one. Choose one convention and use it consistently.

### Iteration and trace uniqueness

Translate `iterate_add` to the arithmetic equation for `run` started at a
configuration. Its invariant is a quantifier-free equality. For trace
uniqueness at clock `t`, use the bounded invariant

`∀ i ≤ min(j,t), trace(z,i) = run(m,x,i)`.

All indices and configuration codes have explicit PR bounds. Compile this
invariant to a bit and use `bounded_induction_closed`. The ambient function
parameter `trace : Nat → State` is replaced by its finite trace code `z`.

### Reduction and resource composition

Numerically encode nonnegative-coefficient polynomials and construct an
explicit interpreter for this restricted polynomial syntax. This interpreter
is PR: the grammar is finite and its evaluation can be bounded by elementary
functions of syntax size and argument size. This claim does not extend to an
interpreter for arbitrary PR programs.

Implement composition of transducer machine codes. Prove a simulation lemma
with the explicit call costs and copying/control overhead. Then lower the
correctness equation and polynomial inequalities. The theorem
`PolyReduction.comp` verifies the algebraic certificate combination, but it
does not replace the machine simulation lemma.

### Midpoint reachability

Let `B` bound all configuration codes. Code a walk of length `l` as `l+1`
base-`B` digits (handle `B=0` and `B=1` explicitly). Its code is bounded by
`max(2,B)^(l+1)`. Replace the inductive ambient `Walk` relation with a bounded
arithmetical path checker.

The recurrence `reach(B,E,k,u,v)` has finite midpoint search. A direct PR
definition can construct an entire `B × B` Boolean relation table at level
`k`, then iterate the table update by primitive recursion. That supplies the
PR *function* independently of the later space-efficient implementation.

Use an outer precision parameter `K` when proving correctness through level
`k ≤ K`. The invariant bounds all vertices by `B`, all levels by `K`, and
path codes by `max(2,B)^(2^K+1)`. This converts the apparent induction over
unbounded path existence into a bounded formula with an explicit PR bound.
Apply bounded reflection/induction. The transformations in
`Walk.split`, `Walk.append`, `Walk.erase_stutters`, and `Walk.stay` become
primitive-recursive list transformations with their own bounds.

Separately construct and analyze the depth-first machine implementation of
the same recurrence. At each depth store two endpoints, one midpoint, a
phase bit, and the recursion depth. Prove its stack invariant using bounded
induction. This is the remaining machine-space proof for Savitch; evaluating
the table recurrence efficiently in Lean is not that proof.

### Circuit constraints and Cook--Levin

Assign a numerical code to an acyclic straight-line circuit. Require every
gate input index to be strictly earlier than its output. Construct its
evaluation array by bounded iteration and prove by bounded prefix induction
that it is the unique extension of the input assignment satisfying the gate
equations.

The checked `Gate.clauses_correct` and `GateSystem.clauses_correct` give the
finite Boolean content of the Tseitin step. Lower their eight/four/two-case
truth-table proofs to arithmetic bits, then append one positive output unit
clause. If target variable names are determined by syntactic occurrence,
also append the tautology `y_i OR NOT y_i` for every original input variable;
otherwise unused witness bits could disappear and witness multiplicities
would change. The full formula then has at most `3G + p + 1` clauses for `G`
gates and `p` inputs, while the checked gate-system component alone has at
most `3G`. Obtain assignment-extension and assignment-restriction witnesses
with explicit bounds. Exact-width-three CNF, if desired, follows by repeating
literals in clauses of width one or two.

The substantial remaining step is the bounded verifier-to-circuit compiler:
give a topological wire numbering for all time/cell/symbol/state bits,
construct local transition circuits, and prove their simulation invariant
for every cell and time index within the explicit tableau bounds. The total
gate count and the implementation's output time must both be bounded by
explicit polynomials. Combining this with the finite gate compiler proves
the internally represented Cook--Levin reduction.

## 4. Exact milestones

| Milestone | Deliverable | Status in this package |
| --- | --- | --- |
| Semantic finite kernel | Theorems in the five Lean modules | Compiled and axiom-audited |
| Fixed PR arithmetic encodings | `PR k` syntax terms and defining equations | Construction specified; not implemented here |
| Object machine semantics | Bounded interpreter and encoded trace derivations | Specified; not implemented here |
| Internal finite kernel | `[] ⊢[PRAAx] φ` for coded versions of core lemmas | Roadmap and upstream interfaces identified |
| Resource-machine compilers | Concrete simulation, reduction, and stack bounds | Mathematical report and outlined obligations |
| Cook--Levin, Savitch, coarse hierarchy | Closed object-theory derivations | Not claimed completed |

Each milestone should be accepted only after its actual Lean theorem type is
checked. An ambient statement quantified over `Nat → Bool`, arbitrary
predicates, or semantic machine objects must never be relabeled an internal
iPRA theorem merely because all its intended instances are computable.
