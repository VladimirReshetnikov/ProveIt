# TAPIR-iPRA formalization plan

Pinned baseline: `VladimirReshetnikov/ProveIt`, commit
`58627ed89814ba122e1f0f012f1aba103cda267b`.

No Lean executable was present in the artifact runtime.  The status labels
below are therefore source-level only.

## Phase 1: small structural kernel

1. Copy `TAPIR/Kernel.lean` into
   `Derivations/Lean/IPRADerivations/Foundations/TAPIR/Kernel.lean`.
2. Confirm the repository-qualified import path resolves.
3. Elaborate `Plan.run` and resolve only dependent-pattern syntax issues.
4. Confirm `#print axioms Plan.sound` reports no unexpected axiom.

Expected mathematical work: none.  Every case maps directly to an existing
`Prf` constructor or `PRA.qfInd`.

## Phase 2: schedule compiler

1. Copy and elaborate `Schedule.lean`.
2. If dependent matching on `Schedule.cons` is brittle, replace `proveAll` by a
   theorem proved with `induction s` and preserve the same statement.
3. Add a two-node test where the second local plan depends on the first.
4. Check that `Schedule.sound` has literal endpoint `R ⊢[PRAAx] φ`.

Expected mathematical work: none beyond list-membership bookkeeping.

## Phase 3: certificates

1. Elaborate `sealCertificate`, `namedWitness`, and `sealExactObserver`.
2. Keep stable observers relation-parametric; do not hard-code rational metrics.
3. Add examples for local and named certificates.

## Phase 4: generic-arity search

1. Prove substitution lemmas for `liftBody`, `body`, and `mu`.
2. Derive `mu_zero` and `mu_succ` from `rec_zero`/`rec_succ`.
3. Port the invariant proof from checked `Core/Search.lean`.
4. Prove `search_found` and `search_minimal`.
5. Instantiate at `k = 1` and compare with the existing API.

This phase contains the first substantial binder-engineering work, but no new
mathematical idea beyond the current checked proof.

## Phase 5: reflected formulas

1. Elaborate equality reflection.
2. Prove sign/nonzero reflection.
3. Implement conjunction and disjunction by explicit bit case splits.
4. Implement negation constructively using bit decidability.
5. Elaborate existing one-parameter `ball` and `bex` wrappers.
6. Replace them with generic-arity versions after Phase 4.
7. Add a meta-level bounded-formula compiler only after the packages themselves
   are stable.

## Phase 6: traces

1. Keep `traceInvariant` as a thin alias of `IPRA.ind`.
2. Select a common bit API and prove `failureStep_spec`.
3. Add paired-state projection helpers from `Core/Pairing.lean`.
4. Exercise the checked `Foundations/Termination.lean` theorem in one example.

## Phase 7: conditional complete lists

1. Implement characteristic membership before a packed list code.
2. Prove scan soundness and completeness below a supplied code bound.
3. Demonstrate on an elementary polynomial equation with a proved coefficient
   bound.
4. Expose a separate residual formula for a deep height theorem.

## Phase 8: repository integration

1. Add modules to `IPRADerivations.lean`.
2. Update the derivations README and root unification plan.
3. Run the full Lake build and existing axiom audit.
4. Record compile times and proof-term sizes.
5. Migrate one existing unverified proof packet to a literal residual sequent.

## Shipping gate

Do not describe any new theorem as checked until:

- every `sorry` is removed from its dependency cone;
- the module elaborates in the pinned/rebased checkout;
- the endpoint is literally `Prf PRAAx`;
- the axiom audit is clean;
- residual producer assumptions appear in the theorem context and metadata.
