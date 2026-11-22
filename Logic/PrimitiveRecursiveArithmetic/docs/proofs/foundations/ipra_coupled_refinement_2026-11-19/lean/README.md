# Checked arithmetic kernel and object-level adapter

`AffineBounds.lean` is a **compiled host-Lean proof**, using `Std` only. It
contains 18 proved theorems, with explicit primitive recursions for the
geometric sum, scalar envelope, and bounded sum. It has no `sorry`, no added
axiom, and no use of classical choice. Its axiom reports list only `propext`
and `Quot.sound` (or the smaller subset `propext`). This does **not** by itself
establish an iPRA derivation.

`ObjectAdapter.lean` is an **uncompiled integration outline** targeting ProveIt
commit `3ee850b4c2d650cf01263823fd5415963747c5d0`. It uses the exact existing
`GuardedLoop.Loop` and `TraceReflection.trace` interfaces. The adapter accepts
actual object-calculus proofs of base, preservation, and finish; it does not
accept semantic Lean implications as substitutes. No unproved theorem has
been installed as an axiom.

The three `*Blueprint.lean` modules are **typechecked definitions and theorem
targets**, also checked with Lean 4.32.0. `SmallGainBlueprint.lean` gives rational
boxes, approximate actions, gain certificates, and explicit samplers.
`TowerBlueprint.lean` defines finite models, refinement contracts, floor rounding,
and the nonlinear lattice. `MatrixBlueprint.lean` defines weighted matrix norms,
finite Neumann sums, and inverse targets. Their target propositions are ordinary
definitions; the universal proofs remain completion tasks. A successful check of
these files establishes that the definitions and statements elaborate, not that
the targets have been proved.

## Reproduce the check

With Lean 4.32.0 installed:

```bash
bash build.sh
```

Or pass a Lean executable explicitly:

```bash
bash build.sh /absolute/path/to/lean
```

The script compiles `AffineBounds.lean` and the three blueprint modules, writing
their `.olean` files and a combined `validation.log`. It does not compile
`ObjectAdapter.lean`. The checked version, arithmetic axiom reports, and blueprint
checks are in the supplied log; the large Lean distribution is deliberately not
included.

## Theorems

* `scaled_envelope`: denominator-cleared scalar recurrence with variable forcing.
* `envelope_constant`, `scaled_affine_bound`: finite geometric-sum formula.
* `geom_complement`: `G_n + c^n = (c+1)^n`.
* `affine_contraction_bound`, `affine_budget`: exact bound and finite target test.
* `nsum_mono`, `nsum_mul_left`, `nsum_mul_right`: bounded-sum algebra.
* `weighted_row`: finite nonnegative weighted matrix comparison.
* `coupled_envelope`, `coupled_contraction_bound`: simultaneous-component bounds.
* `bernoulli_clear`, `block_halving`, `geometric_clock`: explicit convergence clock.
* `residual_separation`: `(d-c)v <= r` from `dv <= cv+r` and `c <= d`.
* `two_component_residual`: determinant-gap elimination of two coupled errors.
* `finite_telescope`: finite accumulated-increment estimate.

The general host functions in theorem parameters are **schematic**. An iPRA
instance must use fixed primitive-recursive bodies, or a clocked evaluator
whose bound is part of its contract; the file makes no claim that every host
function has a primitive-recursive evaluation procedure.

## Exact repository API inspected

Paths relative to `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/`:

* `IPRADerivations/Core/Basic.lean`: PR term operations, `ind`, `inst`.
* `IPRADerivations/Foundations/TraceInvariant.lean`: `trace_invariant` and
  `trace_invariant_all` using `PRA.qfInd`.
* `IPRADerivations/Foundations/TraceReflection.lean`: `Obligations`, `trace_at`,
  `trace`, `loop_compile`.
* `IPRADerivations/Foundations/GuardedLoop.lean`: `Loop`, `obligations`, `loop_at`.
* `IPRADerivations/Foundations/BoundedFormulas.lean`: `BF`, `bitAt`, `fmAt`,
  `bf_reflect`, `bf_choice`, `bf_least`.

The repository toolchain is `leanprover/lean4:v4.32.0`; the top-level
`lakefile.toml` fixes mathlib at `v4.32.0`.

## Concrete completion tasks

1. Encode the coupled state as a finite list of signed rational numerators and
   positive denominator data, with the step, bounds, and budget as `PTm` terms.
2. Fix a common denominator at each finite query, or carry changing denominator
   products in the state. Do not silently apply the integral recurrence to
   rational errors that have not been cleared.
3. Express positivity, row bounds, all component inequalities, and the
   geometric-sum invariant as one bounded formula. Reflect it with `bitAt`.
4. Prove the base, transition, and finish in `Prf PRAAx`, using the source
   module's proofs as a guide. The transition is finite sum monotonicity and
   semiring algebra; the geometric clock is Bernoulli induction and powers.
5. Build a `Package`, use `export_at` or `export_closed`, and inspect the
   resulting theorem's conclusion and axioms.
6. Separately prove semantic adequacy for the represented objects: stability,
   region invariance, continuity/modulus and interpretation of the rational
   error inequality. A finite recurrence estimate alone is not a theorem
   asserting existence of an infinite real fixed point.
