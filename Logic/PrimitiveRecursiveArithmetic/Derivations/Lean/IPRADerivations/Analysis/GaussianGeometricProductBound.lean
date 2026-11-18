import IPRADerivations.Analysis.GaussianGeometricProduct
import IPRADerivations.Analysis.GaussianGeometricProductTail

/-!
# A uniform bound for the actual finite geometric product

The complementary tail gap telescopes along the actual numerator and
denominator recursors. Once the finite computed tail budget is at most
one half, every later product is at most twice its value at that stage.
The prefix bound handles earlier stages. All counters and cutoffs are
internal; a final product bound or a product recurrence is never a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeometricProductBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeometricProduct
open LeanProofs.IPRA.Analysis.GaussianGeometricProductTail
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_order)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def comparison (C K T j : PTm n) : Fm PTm n :=
  le (numerator C K j*denominator C K T*gap C K T*pw K j)
    (denominator C K j*numerator C K T*pw K T*gap C K j)
def radius (C T : PTm n) : PTm n := two*pw (one+C) T

@[simp] theorem subst_comparison {m : ℕ} (σ : Fin n → PTm m) (C K T j : PTm n) :
    (comparison C K T j).subst σ = comparison (Syn.subst σ C) (Syn.subst σ K) (Syn.subst σ T) (Syn.subst σ j) := by
  simp [comparison]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (C T : PTm n) :
    Syn.subst σ (radius C T) = radius (Syn.subst σ C) (Syn.subst σ T) := by
  simp [radius]

theorem comparison_stage_congr (C K T j j' : PTm n) (e : Γ ⊢[PRAAx] j ≐ j')
    (h : Γ ⊢[PRAAx] comparison C K T j) : Γ ⊢[PRAAx] comparison C K T j' := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (comparison (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    (σ := ![C,K,T,j]) (σ' := ![C,K,T,j']) (fun i => by fin_cases i <;> first | exact e | exact .eqRefl _)
  have p' : (Γ ⊢[PRAAx] comparison C K T j) → (Γ ⊢[PRAAx] comparison C K T j') := by simpa using p
  exact p' h

theorem comparison_reflexive (C K T : PTm n) : Γ ⊢[PRAAx] comparison C K T T := by
  unfold comparison
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem comparison_step (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) (hj : Γ ⊢[PRAAx] le T j)
    (ih : Γ ⊢[PRAAx] comparison C K T j) : Γ ⊢[PRAAx] comparison C K T (succ j) := by
  have first := mul_le_mul_right (K*factor C K j) ih
  have localBound := gap_product_le C K j hK (small_mono C K T j hK hSmall hj)
  have second : Γ ⊢[PRAAx] le
      (denominator C K j*numerator C K T*pw K T*gap C K j*(K*factor C K j))
      (denominator C K j*numerator C K T*pw K T*(pw K j*gap C K (succ j))) :=
    le_congr (by unfold factor; ipra_ring) (by ipra_ring)
      (mul_le_mul_right (denominator C K j*numerator C K T*pw K T) localBound)
  apply le_congr ?_ ?_ (le_trans first second)
  · have u := natEq (numerator_succ (Γ := Γ) C K j)
    have f := natEq (pw_succ (Γ := Γ) K j)
    apply deriveNat
    ipra_simps
    rw [u,f]
    ring
  · have v := natEq (denominator_succ (Γ := Γ) C K j)
    apply deriveNat
    ipra_simps
    rw [v]
    ring

theorem comparison_offset (C K T m : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) : Γ ⊢[PRAAx] comparison C K T (T+m) := by
  have hK' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift K) := by
    simpa [Fm.shift,Syn.shift] using hK.shift
  have hSmall' : Γ.map Fm.shift ⊢[PRAAx] small (Syn.shift C) (Syn.shift K) (Syn.shift T) := by
    simpa [Fm.shift,Syn.shift] using hSmall.shift
  have all : Γ ⊢[PRAAx] .all (comparison (Syn.shift C) (Syn.shift K) (Syn.shift T) (Syn.shift T+var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_comparison,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact comparison_stage_congr C K T T (T+zero) (add_zero T).eqSymm (comparison_reflexive C K T)
    · simp only [subst_comparison,PTm.subst_add,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact comparison_stage_congr _ _ _ _ _ (add_succ _ _).eqSymm
        (comparison_step _ _ _ _ hK'.wk hSmall'.wk (le_add_right _ _) Prf.hyp0)
  simpa only [subst_comparison,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

theorem tail_comparison (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) (hj : Γ ⊢[PRAAx] le T j) : Γ ⊢[PRAAx] comparison C K T j :=
  comparison_stage_congr C K T _ j (eq_add_of_le hj).eqSymm (comparison_offset C K T (monus j T) hK hSmall)

/-- Only positive powers of K are cancelled; no tail or gap is cancelled. -/
theorem tail_ratio_bound (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) (hj : Γ ⊢[PRAAx] le T j) : Γ ⊢[PRAAx]
    le (numerator C K j*denominator C K T) (two*denominator C K j*numerator C K T) := by
  have first : Γ ⊢[PRAAx] le
      ((pw K T*pw K j)*(numerator C K j*denominator C K T))
      (two*(numerator C K j*denominator C K T*gap C K T*pw K j)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (numerator C K j*denominator C K T*pw K j) (twice_gap C K T hSmall))
  have second : Γ ⊢[PRAAx] le
      (two*(numerator C K j*denominator C K T*gap C K T*pw K j))
      (two*(denominator C K j*numerator C K T*pw K T*gap C K j)) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two (tail_comparison C K T j hK hSmall hj))
  have third : Γ ⊢[PRAAx] le
      (two*(denominator C K j*numerator C K T*pw K T*gap C K j))
      ((pw K T*pw K j)*(two*denominator C K j*numerator C K T)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (two*denominator C K j*numerator C K T*pw K T)
        (gap_le C K j (small_mono C K T j hK hSmall hj)))
  exact RationalValueBounds.positive_cancel
    (positive_product _ _ (RationalNonnegativePowers.denominator_positive K T hK)
      (RationalNonnegativePowers.denominator_positive K j hK)) (le_trans first (le_trans second third))

theorem late_bound (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) (hj : Γ ⊢[PRAAx] le T j) : Γ ⊢[PRAAx]
    le (numerator C K j) (denominator C K j*radius C T) := by
  have first := tail_ratio_bound C K T j hK hSmall hj
  have second := mul_le_mul_right (two*denominator C K j) (prefix_bound (Γ := Γ) C K T)
  exact RationalValueBounds.positive_cancel (denominator_positive C K T hK)
    (le_trans (le_congr (mul_comm _ _) (.eqRefl _) first)
      (le_congr (by ipra_ring) (by unfold radius; ipra_ring) second))

theorem early_bound (C K T j : PTm n) (hj : Γ ⊢[PRAAx] le j T) : Γ ⊢[PRAAx]
    le (numerator C K j) (denominator C K j*radius C T) := by
  have first := prefix_bound (Γ := Γ) C K j
  have second := mul_le_mul_right (denominator C K j)
    (GaussianFactorBudget.power_monotone_length (one+C) j T (le_add_right _ _) hj)
  have third : Γ ⊢[PRAAx] le (denominator C K j*pw (one+C) T) (denominator C K j*radius C T) :=
    le_of_eq_add (d := denominator C K j*pw (one+C) T) (by unfold radius; ipra_ring)
  exact le_trans first (le_trans (le_congr (mul_comm _ _) (mul_comm _ _) second) third)

theorem uniform_bound (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) : Γ ⊢[PRAAx]
    le (numerator C K j) (denominator C K j*radius C T) :=
  .orE (le_total j T) (early_bound C K T j Prf.hyp0) (late_bound C K T j hK.wk hSmall.wk Prf.hyp0)

theorem value_uniform_bound (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hSmall : Γ ⊢[PRAAx] small C K T) : Γ ⊢[PRAAx]
    rationalLE (value C K j) (fraction (radius C T) one) :=
  fraction_order _ _ _ _ (denominator_positive C K j hK) (le_refl one)
    (le_congr (one_mul _).eqSymm (mul_comm _ _) (uniform_bound C K T j hK hSmall))

theorem actual_tail_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ small (var 0) (var 1) (var 2) ⟶ le (var 2) (var 3) ⟶
      comparison (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (tail_comparison _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_uniform_product_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ small (var 0) (var 1) (var 2) ⟶
      le (numerator (var 0) (var 1) (var 3)) (denominator (var 0) (var 1) (var 3)*radius (var 0) (var 2))) :=
  closeUniv 4 (.impI (.impI (uniform_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_uniform_product_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ small (var 0) (var 1) (var 2) ⟶
      (rationalLE (fraction one one) (value (var 0) (var 1) (var 3)) ⋏
        rationalLE (value (var 0) (var 1) (var 3)) (fraction (radius (var 0) (var 2)) one))) :=
  closeUniv 4 (.impI (.impI (.andI (value_ge_one _ _ _ Prf.hyp1) (value_uniform_bound _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGeometricProductBound
