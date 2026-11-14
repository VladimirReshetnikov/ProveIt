# Proof audit at commit 1c9524d8bf2e0a27b9a16ff622359927f536e663

## Established status

The current PA README explicitly says neither machine-specific direction of
`iPRA ⊢ Con(PA) ↔ ¬Halt(PA194)` has been established. This is stronger than
"not yet compiled in Lean": the current arithmetic endpoint retains both
classical PRA machine reductions as hypotheses. The delivered research
packets claim ordinary PA calibrations, not iPRA calibrations.

Paths providing direct evidence:

- `Computability/BusyBeaver/Research/PA/README.md`.
- `Computability/BusyBeaver/Research/PA/pa194/ipra/README.md`.
- `Computability/BusyBeaver/Research/PA/pa194-forward-audit/README.md`.
- `Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/calibration.tex`.
- `Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/reference/original_pa195_calibration.tex`.

## Exact usable weak-base route

`PA/isigma1-transfer/README.md` states a checked transfer theorem. If a
bounded halting-history matrix δ satisfies

    IΣ₁ ⊢ (paRefutation ↔ ∃ t, δ(t)),

the witness-bound certificate plus conservation and Gödel–Gentzen translation
give the requested native iPRA equivalence. The machine-independent
certificate is supplied elsewhere. No machine is calibrated in that
directory. It is therefore legitimate to develop the remaining arithmetic
argument in arbitrary IΣ₁ models; it is not legitimate to substitute a
standard-natural-number simulation for such an argument.

## Progress already stronger than ordinary-number theorems

`pa194-model-fairness/README.md` gives checked `halts_iff_provable` for the
modeled scheduler and `TargetProvable` inside arbitrary IΣ₁ models, including
nonstandard proof codes, word lengths and run times. This is not yet the
physical table.

`pa194-distinct-gate-sound/README.md` states that the distinct-label gate
premise is discharged. Together with the equal-label case and scheduler
invariant it yields a checked iPRA theorem

    Con(PA) → ¬Halt(modeled scheduler).

The physical machine connection is still missing. Thus the informal claim
that "the gate is still the sole open issue" would be stale at this commit.

The forward PA-to-calculus compiler is also incomplete at the weak base.
`pa194-forward-audit/README.md` points to two actual uses of full PA
induction in the upstream PA196 proof:

- `ordinary_derivation_requested`, over `budgetedDerivationInvariant`,
  quantifies over smaller derivations and all environments.
- `fuel_invariant`, over `fuelInvariantFormula`, universally quantifies
  a table bound and asserts table-wide realization.

These predicates have not been shown Σ₁. The formula-substitution agreement
gap identified in the same audit has subsequently been repaired for all
IΣ₁ models (`pa194-paeq-formula-subst`). The uniform induction-axiom supplier,
remaining finite axiom suppliers, and numerical proof compiler are still
needed.

## A useful methodological result already in the repository

The tracked executor of `pa194-model-fairness` is the right pattern for the
remaining compiler. A direct invariant "there is a word that works on every
base stack" has an existential–universal shape. The implemented proof instead
constructs a single coded execution on an empty stack and records stack
height/underflow. Existence of that finite certificate is Σ₁, and a separately
proved frame lemma supplies the arbitrary-stack conclusion. This is a
mathematical reduction of induction strength, not source-code compression.

An analogous proof-carrying realization table might remove the environment
quantifiers from the remaining compiler invariants. However, one must supply
an actual uniformly bounded table construction; replacing ∀ environments by
"a certificate" without defining its coverage is not a proof.

## New relative transport component

`ipra_simulation_theorem.tex` supplies a written, explicit iPRA theorem for
primitive-recursive exact positive macro simulation, with frame guard,
startup, halting reflection and witness maps. It includes the cofinality
generalization allowing zero-duration administrative steps and a counterexample
to dropping positivity/cofinality altogether.

The forward halting-witness map is n ↦ d + T(n), where T is the primitive
recursive cumulative segment duration. The reverse map can be t ↦ t under
positive segments, using absorbing halts and T(t) ≥ t. This avoids any least
boundary search or inverse decoding of interior physical tapes. The theorem
does not hide its local soundness hypotheses and does not pretend to discharge
the original PA194 consistency calibration.

