# KIFC-R formalization plan

Pinned ProveIt commit:
`31784f0710fa04ccd8ee863ce9bad91fb1d8cf88`.
Re-audit imports and theorem signatures if integrating at a later commit.

## Phase 0 — build gate and namespace

1. Create `IPRADerivations/Framework/` in the existing Derivations Lake project.
2. Move `KernelCore.lean` to `Framework/Kernel.lean` and rename the namespace to
   `LeanProofs.IPRA.Framework`.
3. Compile `KernelRule.use`, `Schedule.compile`, `ConditionalTheorem.close`, and
   `LoopCertificate.compile/at`.
4. Record `#print axioms`; require no `sorryAx`.

## Phase 1 — checked-search adapter

1. Import `Core.Search` and inspect the current exact argument order.
2. Define `one`, the zero-success body `1 ∸ p`, and prove under Boolean range:
   `(1 ∸ p = 0) ↔ (p = 1)`.
3. Instantiate `Search.search_spec`, `search_minimal`, and `search_found`.
4. Export `firstValid`, soundness, foundness, and minimality.
5. Prove one closed least-witness example. No new induction is allowed here.

## Phase 2 — Boolean reflection and bounded folds

1. Wrap checked `eqb` equality reflection.
2. Define/prove Boolean `not`, `and`, `or`, and selector truth tables.
3. Generate `allB`/`anyB` for a fixed predicate using `PR.prec`.
4. Prove range and endpoint introduction/elimination with QF induction.
5. Combine `anyB` with Phase 1 to obtain explicit bounded witnesses.
6. Implement metalevel structural Booleanization for fixed formulas.

## Phase 3 — finite state and traces

1. Reuse checked `pairT`, `fstT`, `sndT`; generate fixed tuples.
2. Add length-tagged finite sequences and lookup/update equations.
3. Generate a two-branch packed loop and compile its QF invariant.
4. Add freeze-after-done and rank-counter patterns.
5. Prove one-loop lowering for a concrete nested-loop program before adding a
   generic source generator.

## Phase 4 — residual theorem compiler

1. Implement metalevel proof reachability and stable-key deduplication.
2. Generate a `Schedule` in residual-plus-permanent context.
3. Package it as `ConditionalTheorem`.
4. Test removal of an unused residual and closure by a supplied producer proof.
5. Add provenance JSON and graph hashes.

## Phase 5 — capped cyclic demand

1. Prove the host Lean vector theorem (monotone inflation, rank increase,
   stabilization, leastness).
2. Generate a fixed 3-coordinate object system with nested-pair state.
3. Prove cap preservation, inflation, change/rank, freeze, and terminal
   fixedness by `LoopCertificate`.
4. Prove leastness with an arbitrary pre-fixed vector as free parameters.
5. Export raw demand adequacy under `overflow = 0`; allow that formula to be
   residual.

## Phase 6 — finite relational viability

1. Implement finite Boolean tables.
2. Generate the reverse viability recurrence for a fixed width.
3. Prove the row invariant and a coded path checker.
4. Prove viability iff accepted suffix.
5. Select the least path using the Phase 1 adapter.
6. Prove exact and diameter observer elimination.

## Phase 7 — rational metric and benchmark

1. Implement total signed-rational codes `(p,m,d)` with denominator `d+1`.
2. Prove equality/order reflection, triangle inequality, clipping, and dyadic
   error algebra.
3. Define exact bisection for `y^3+y=x` on `[0,1]`.
4. Use `ipra_ring` for the monotonicity factorization.
5. Prove bracket preservation/width by QF induction.
6. Add represented-input transport and the `k+3` precision budget.
7. Close the ordinary `Prf PRAAx` theorem, then apply native transfer.

## Phase 8 — generated applications

Migrate one packet at a time. For each node, require an actual local proof or a
named residual formula. Generate the terminal theorem, source map, axiom audit,
and machine-readable status. Only after several examples compile should the
metalevel graph records be generalized further.
