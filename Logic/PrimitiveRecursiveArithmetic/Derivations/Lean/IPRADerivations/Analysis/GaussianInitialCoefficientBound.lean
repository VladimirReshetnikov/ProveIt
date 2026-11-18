import IPRADerivations.Analysis.GaussianRationalL1
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# A computed initial integer coefficient bound

The approximate-factorization source permits any integer A0≥1 bounding all
input coefficient L1 norms. This deliberately coarse constructor takes the
finite maximum of their actual denominator-cleared L1 numerators, then adds
one. All original rational component denominators are independently decoded;
the bound requires no incoming coefficient-size estimate or representation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianInitialCoefficientBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalL1
  (qL1 rawDen rawGaussian raw_den_positive raw_represents qL1_represents)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at subst_finiteMaximum)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def naturalCode (a : PTm n) : PTm n := normalize (ZT.ofNat a) one
@[simp] theorem subst_naturalCode {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (naturalCode a) = naturalCode (Syn.subst σ a) := by simp [naturalCode]

theorem natural_code_monotone (a b : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] rationalLE (naturalCode a) (naturalCode b) :=
  GaussianRationalMetric.comparison_of_cleared _ _ a b one one (le_refl _) (le_refl _)
    (normalize_preserves_value _ _ (le_refl _)) (normalize_preserves_value _ _ (le_refl _))
    (le_congr (by ipra_ring) (by ipra_ring) h)

theorem raw_numerator_bound (q : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 q) (naturalCode (GaussianL1.norm1 (rawGaussian q))) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ (rawDen q) one (raw_den_positive q) (le_refl _)
    (qL1_represents _ _ _ (raw_den_positive q) (raw_represents q))
    (normalize_preserves_value _ _ (le_refl _))
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl _) (raw_den_positive q)))

def boundBody : PTm 2 := GaussianL1.norm1 (rawGaussian (entry (var 1) (var 0)))
def initialBound (C N : PTm n) : PTm n := one+finiteMaximum boundBody N C

@[simp] theorem subst_initialBound {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (initialBound C N) = initialBound (Syn.subst σ C) (Syn.subst σ N) := by simp [initialBound]

theorem bound_body_at (C i : PTm n) :
    inst2 boundBody i C = GaussianL1.norm1 (rawGaussian (entry C i)) := by
  simp only [boundBody,inst2,GaussianL1.subst_norm1,GaussianRationalL1.subst_rawGaussian,
    subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem initial_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (initialBound C N) := le_add_right _ _

theorem coefficient_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry C i)) (naturalCode (initialBound C N)) := by
  have h : Γ ⊢[PRAAx] le (GaussianL1.norm1 (rawGaussian (entry C i))) (finiteMaximum boundBody N C) := by
    simpa only [bound_body_at] using finiteMaximum_at boundBody hi
  exact RationalArgmin.transitive (raw_numerator_bound _)
    (natural_code_monotone _ _ (le_trans h (le_add_left _ _)))

def initialBoundF : PR 2 := PTm.toPR (initialBound (var 0) (var 1))
theorem initial_program (C N : PTm n) : Γ ⊢[PRAAx] ap2 initialBoundF C N ≐ initialBound C N := by
  simpa [initialBoundF,ap2] using toPR_eq (Γ := Γ) (initialBound (var 0) (var 1) : PTm 2) ![C,N]

theorem initial_coefficient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (initialBound (var 0) (var 1)) ⋏
      (lt (var 2) (var 1) ⟶ rationalLE (qL1 (entry (var 0) (var 2)))
        (naturalCode (initialBound (var 0) (var 1))))) :=
  closeUniv 3 (.andI (initial_positive _ _) (.impI (coefficient_bound _ _ _ Prf.hyp0)))
theorem initial_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 initialBoundF (var 0) (var 1) ≐ initialBound (var 0) (var 1)) := closeUniv 2 (initial_program _ _)

end LeanProofs.IPRA.Analysis.GaussianInitialCoefficientBound
