import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianNonmonicRD

/-!
# Computed approximate roots for arbitrary nonconstant rational polynomials

The unchanged finite residual clock now uses the proved nonmonic RD
instance. Only original length, positive degree, a nonconstant coefficient
and positive rational precision are required. Leading zeros and arbitrary
raw input fractions are allowed. The actual PR4 has the original argument
order N,C,p,q. This finite residual result does not assert convergence of
an infinite root name or the missing general travel estimate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNonmonicApproximateRoot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadius (inputContract)
open LeanProofs.IPRA.Analysis.GaussianNonmonicRD (step)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def approximateRoot (C N p q : PTm n) : PTm n := GaussianDescentClock.approximateRoot step N C p q
def rootF : PR 4 := GaussianDescentClock.approximateRootF step
def run (C N p q : PTm n) : PTm n := GaussianDescentClock.run step N C p q

@[simp] theorem subst_approximateRoot {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (approximateRoot C N p q) = approximateRoot (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by simp [approximateRoot]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (run C N p q) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [run,GaussianDescentClock.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem approximate_root (C N p q : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    GaussianDescentClock.result C (approximateRoot C N p q) p q :=
  GaussianDescentClock.approximate_root step N C p q (GaussianNonmonicRD.local_rd N C hInput) hp hq

theorem program_at (C N p q : PTm n) : Γ ⊢[PRAAx] run C N p q ≐ approximateRoot C N p q :=
  GaussianDescentClock.program_at step N C p q

theorem program_correct (C N p q : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    GaussianDescentClock.result C (run C N p q) p q :=
  GaussianDescentClock.program_correct step N C p q (GaussianNonmonicRD.local_rd N C hInput) hp hq

theorem actual_decay (C N k : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    GaussianDescentClock.decay step N C (GaussianDescentClock.initialNumerator C) (GaussianDescentClock.initialDenominator C) k := by
  have denominator : Γ ⊢[PRAAx] le one (GaussianDescentClock.initialDenominator C) :=
    RationalArgmin.denominator_positive _
  have rd : Γ ⊢[PRAAx] GaussianDescentClock.localRD step N C := GaussianNonmonicRD.local_rd N C hInput
  exact GaussianDescentClock.iterate_decay step N C (GaussianDescentClock.initialNumerator C)
    (GaussianDescentClock.initialDenominator C) k denominator
    (GaussianRationalL1.initial_bounded (GaussianRationalHorner.evaluate C GaussianRationalHorner.qzero)) rd

theorem concrete_nonconstant_approximate_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract (var 0) (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
      GaussianDescentClock.result (var 0) (approximateRoot (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (approximate_root _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem concrete_nonconstant_root_program_correct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract (var 0) (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
      GaussianDescentClock.result (var 0) (run (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (program_correct _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem concrete_nonconstant_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ approximateRoot (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem concrete_nonconstant_residual_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ GaussianDescentClock.decay step (var 1) (var 0)
      (GaussianDescentClock.initialNumerator (var 0)) (GaussianDescentClock.initialDenominator (var 0)) (var 2)) :=
  closeUniv 3 (.impI (actual_decay _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNonmonicApproximateRoot
