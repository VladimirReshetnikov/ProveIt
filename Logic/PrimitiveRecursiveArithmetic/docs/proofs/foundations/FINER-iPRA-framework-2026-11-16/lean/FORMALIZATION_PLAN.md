# FINER formalization plan

Target repository: `VladimirReshetnikov/ProveIt`, commit
`64bc0e997df6b8dbdf43f5ac9b3d9f74b4047ee5`.

The formal endpoint is always ordinary object-language derivability
`Γ ⊢[PRAAx] φ`.  Native-scalar export comes only after an ordinary derivation
exists.  The files in `lean/FINER/` are source-oriented blueprints and were not
compiled in the artifact environment.

## Phase 0 - pin and reproduce

1. Build `ConciseIPRA`, `IPRADerivations`, and `IPRABridge` at the pinned commit.
2. Run the existing axiom audit.
3. Copy `lean/FINER/KernelWrappers.lean` into
   `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Framework/`
   and adjust the module prefix.  It should be the first file elaborated.

## Phase 1 - fixed Boolean reflection

Implement a deliberately small syntax `FixedBoundedFormula n` whose atoms are
fixed equality terms and whose quantifiers are explicitly bounded.  The
compiler is Lean metacode/structural recursion producing a theorem-specific
`PR`; it is not an object-language universal evaluator.

Dependencies:

- `Core.Basic`: `ind`, `inst`, congruence;
- `Core.Pairing`: `eqb`, pairing and projections;
- `Core.Definitions`, `Core.MultiSums`: finite folds;
- `Core.Search`: least bounded witness.

Milestones:

- equality atom reflection;
- Boolean connectives;
- bounded existential through `Search.mu`;
- bounded universal through a product/failure search;
- a generated theorem `ReflectedPredicate` for each fixed formula.

Acceptance: no `sorry`, literal result type `Prf PRAAx`, axiom audit unchanged.

## Phase 2 - packed finite arrays

Add one canonical encoding, preferably nested `pairT` for the first checked
version.  Mixed-radix coding can be an optimization after correctness.
Prove lookup/update equations and boundedness at arbitrary terms.  Avoid a
large generic sequence library until the compiler needs it.

## Phase 3 - monotone demand closure

Specialise a finite vector dimension and capacities at the Lean metalevel.
Generate coordinate terms, the join step, and the coordinate sum.  Prove in one
quantifier-free induction:

1. coordinates stay within capacities;
2. the trace is monotone;
3. a nonstationary step increases the sum;
4. after `Σ M_i` strict increases the trace is stationary;
5. every prefixed point bounds every iterate.

Export `demand_stabilises` and `demand_least_prefixed` as closed derivations.
This is the first genuinely new generic object-theory component.

## Phase 4 - backward viability

Generate the viability table backwards for one fixed horizon.  Compile every
bounded existential with Phase 1.  The forward path constructor uses the
checked `Core.Search` theorem rather than a second search implementation.
Prove success and finite failure certificates.

## Phase 5 - observers and descent

Implement three independent eliminators:

- exact invariance;
- quotient congruence;
- metric diameter.

Then implement finite observational descent over a supplied spanning tree.
The tree and path tables are finite certificates.  Edge equality/error proofs
compose by induction on path length.

## Phase 6 - master certificates

Define `CompiledQuery` only after the preceding pieces are checked.  The
certificate existence proof is a residualized theorem, not a host-language
promise.  `compileQuery` should be a short composition of:

- demand closure;
- bounded certificate existence;
- `Search.search_found`;
- checker soundness;
- `Prf.trans`.

## Phase 7 - benchmark applications

Formalize in increasing order of difficulty:

1. exact rational bisection for `y^3+y=x`;
2. a finite relational path with an invariant observer;
3. finite-net approximate minimization under a supplied coverage modulus;
4. height-bound to complete-list conversion;
5. a root-cluster or spectral-projector example with no branch selector.

Each benchmark ends in a literal `Prf PRAAx` declaration and is added to
`Checks/Axioms.lean`.

## Phase 8 - bridge and repository adoption

Only closed ordinary endpoints should initially cross `IPRABridge`, matching
its current public interface.  Open-sequent bridge transport is part of the
repository unification plan and should not be silently assumed by FINER.
