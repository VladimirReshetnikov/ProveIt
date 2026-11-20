import IPRADerivations.Foundations.FiniteStabilization

/-!
# Sequential composition of deterministic trace systems

Packets: `foundations/ipra_finite_use_framework_2026-11-15` and its `_v2` edition,
`sections/04_deterministic.tex`, Theorem `thm:det-compose` ("Deterministic transducer composition"): if
`T₁` and `T₂` have iPRA-verified local obligations and the terminal certificate of `T₁` implies the input
guard of `T₂`, then their sequential composition is a deterministic trace system with an iPRA-verified
soundness theorem, whose bound is the sum of the component bounds plus one switch step.

A trace system is a step `f` with a quantifier-free invariant `R(s, y)` (state `s`, frozen metadata `y`)
preserved by every step (`Preserved`, a rule at arbitrary contexts). The composite run is
`B₂` steps of `f₂` after the switch map `w` applied to `B₁` steps of `f₁`, so `B₁ + 1 + B₂` steps in all.

* `run_invariant`: the invariant of a trace system holds after any number of steps
  (`FiniteStabilization.invariant`);
* `compose` (`thm:det-compose`): if `R₁` holds initially, the terminal certificate `A₁` holds after `B₁`
  steps, and the switch turns `R₁ ∧ A₁` into the input guard `R₂` of the second system, then `R₂` holds at the
  end of the composite run;
* `compose_sound`: with an output contract `R₂(s, y) → Out(s, y)`, the composite run meets the output
  contract.

The encoding as a single trace with a phase bit is not formalized: the composite is written as the
composition of the two iterations.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TraceComposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IterationFusion (app1 iter rel)
open LeanProofs.IPRA.Foundations.FiniteStabilization (invariant)
open Syn
open scoped Fm

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The invariant `R` is preserved by every step of `f`. -/
def Preserved (f : PTm 1) (R : Fm PTm 2) : Prop :=
  ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s y : PTm k}, (Γ ⊢[PRAAx] rel R s y) → (Γ ⊢[PRAAx] rel R (app1 f s) y)

/-- The invariant holds along the run. -/
theorem run_invariant {f : PTm 1} {R : Fm PTm 2} (hqf : R.QF) (hp : Preserved f R) {x y : PTm k}
    (h : Γ ⊢[PRAAx] rel R x y) (t : PTm k) : Γ ⊢[PRAAx] rel R (iter f t x) y :=
  invariant hqf hp h t

/-- `thm:det-compose`: the input guard of the second system holds at the end of the composite run. -/
theorem compose {f₁ f₂ w : PTm 1} {R₁ R₂ A₁ : Fm PTm 2} (hqf₂ : R₂.QF) (hp₂ : Preserved f₂ R₂)
    (hqf₁ : R₁.QF) (hp₁ : Preserved f₁ R₁)
    (hswitch : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s y : PTm k},
      (Γ ⊢[PRAAx] rel R₁ s y) → (Γ ⊢[PRAAx] rel A₁ s y) → (Γ ⊢[PRAAx] rel R₂ (app1 w s) y))
    {x y B₁ B₂ : PTm k} (h₀ : Γ ⊢[PRAAx] rel R₁ x y) (hacc : Γ ⊢[PRAAx] rel A₁ (iter f₁ B₁ x) y) :
    Γ ⊢[PRAAx] rel R₂ (iter f₂ B₂ (app1 w (iter f₁ B₁ x))) y :=
  run_invariant hqf₂ hp₂ (hswitch (run_invariant hqf₁ hp₁ h₀ B₁) hacc) B₂

/-- Soundness of the composite: the output contract holds at the end of the composite run. -/
theorem compose_sound {f₁ f₂ w : PTm 1} {R₁ R₂ A₁ Out : Fm PTm 2} (hqf₂ : R₂.QF) (hp₂ : Preserved f₂ R₂)
    (hqf₁ : R₁.QF) (hp₁ : Preserved f₁ R₁)
    (hswitch : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s y : PTm k},
      (Γ ⊢[PRAAx] rel R₁ s y) → (Γ ⊢[PRAAx] rel A₁ s y) → (Γ ⊢[PRAAx] rel R₂ (app1 w s) y))
    (hout : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s y : PTm k},
      (Γ ⊢[PRAAx] rel R₂ s y) → (Γ ⊢[PRAAx] rel Out s y))
    {x y B₁ B₂ : PTm k} (h₀ : Γ ⊢[PRAAx] rel R₁ x y) (hacc : Γ ⊢[PRAAx] rel A₁ (iter f₁ B₁ x) y) :
    Γ ⊢[PRAAx] rel Out (iter f₂ B₂ (app1 w (iter f₁ B₁ x))) y :=
  hout (compose hqf₂ hp₂ hqf₁ hp₁ hswitch h₀ hacc)

end LeanProofs.IPRA.Foundations.TraceComposition
