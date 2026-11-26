import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicCommonCutoff

/-!
# Equal lower endpoints for two actual logarithmic certificates

Two independent numerical cutoff demands admit original cutoff indices
with exactly the same eta denominator. Their actual heights are V*H
and A*H, so the exponent identity uses only native multiplication.
The top endpoints remain the original computed endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCertificateGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianEulerLogarithmicCommonCutoff (cutoff)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def heightBase (A R j : PTm n) : PTm n := height zero (two*A) (R+j)
def commonHeight (p q j R A S V : PTm n) : PTm n :=
  heightBase A R j+heightBase V S j+cutoff p j A+cutoff q j V+one
def leftIndex (p q j R A S V : PTm n) : PTm n :=
  monus (V*commonHeight p q j R A S V) (heightBase A R j)
def rightIndex (p q j R A S V : PTm n) : PTm n :=
  monus (A*commonHeight p q j R A S V) (heightBase V S j)
def commonTop (p q j R A S V : PTm n) : PTm n :=
  two*(A+V)*commonHeight p q j R A S V

@[simp] theorem subst_heightBase {m : ℕ} (σ : Fin n → PTm m) (A R j : PTm n) :
    Syn.subst σ (heightBase A R j) = heightBase (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ j) := by
  simp [heightBase,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_commonHeight {m : ℕ} (σ : Fin n → PTm m) (p q j R A S V : PTm n) :
    Syn.subst σ (commonHeight p q j R A S V) = commonHeight (Syn.subst σ p) (Syn.subst σ q)
      (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ S) (Syn.subst σ V) := by simp [commonHeight]
@[simp] theorem subst_leftIndex {m : ℕ} (σ : Fin n → PTm m) (p q j R A S V : PTm n) :
    Syn.subst σ (leftIndex p q j R A S V) = leftIndex (Syn.subst σ p) (Syn.subst σ q)
      (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ S) (Syn.subst σ V) := by simp [leftIndex]
@[simp] theorem subst_rightIndex {m : ℕ} (σ : Fin n → PTm m) (p q j R A S V : PTm n) :
    Syn.subst σ (rightIndex p q j R A S V) = rightIndex (Syn.subst σ p) (Syn.subst σ q)
      (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ S) (Syn.subst σ V) := by simp [rightIndex]
@[simp] theorem subst_commonTop {m : ℕ} (σ : Fin n → PTm m) (p q j R A S V : PTm n) :
    Syn.subst σ (commonTop p q j R A S V) = commonTop (Syn.subst σ p) (Syn.subst σ q)
      (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ S) (Syn.subst σ V) := by simp [commonTop]

theorem left_height_budget (p q j R A S V : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    le (heightBase A R j+cutoff p j A) (V*commonHeight p q j R A S V) := by
  have first : Γ ⊢[PRAAx] le (heightBase A R j+cutoff p j A) (commonHeight p q j R A S V) :=
    le_of_eq_add (d := heightBase V S j+cutoff q j V+one) (by unfold commonHeight; ipra_ring)
  exact le_trans first (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ hV))

theorem right_height_budget (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    le (heightBase V S j+cutoff q j V) (A*commonHeight p q j R A S V) := by
  have first : Γ ⊢[PRAAx] le (heightBase V S j+cutoff q j V) (commonHeight p q j R A S V) :=
    le_of_eq_add (d := heightBase A R j+cutoff p j A+one) (by unfold commonHeight; ipra_ring)
  exact le_trans first (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ hA))

private theorem index_budget (b d t : PTm n) (h : Γ ⊢[PRAAx] le (b+d) t) : Γ ⊢[PRAAx]
    le d (monus t b) := by
  have hb := le_trans (le_add_right b d) h
  exact le_of_add_le_add_right (le_congr (add_comm b d)
    ((eq_add_of_le hb).eqTrans (add_comm b (monus t b))) h)

theorem left_index_late (p q j R A S V : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    le (cutoff p j A) (leftIndex p q j R A S V) :=
  index_budget _ _ _ (left_height_budget p q j R A S V hV)

theorem right_index_late (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    le (cutoff q j V) (rightIndex p q j R A S V) :=
  index_budget _ _ _ (right_height_budget p q j R A S V hA)

theorem left_height (p q j R A S V : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    height (leftIndex p q j R A S V) (two*A) (R+j) ≐ V*commonHeight p q j R A S V := by
  have hb := le_trans (le_add_right _ _) (left_height_budget p q j R A S V hV)
  exact (by unfold leftIndex heightBase height; ipra_ring : Γ ⊢[PRAAx]
      height (leftIndex p q j R A S V) (two*A) (R+j) ≐
        heightBase A R j+monus (V*commonHeight p q j R A S V) (heightBase A R j)).eqTrans (eq_add_of_le hb).eqSymm

theorem right_height (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    height (rightIndex p q j R A S V) (two*V) (S+j) ≐ A*commonHeight p q j R A S V := by
  have hb := le_trans (le_add_right _ _) (right_height_budget p q j R A S V hA)
  exact (by unfold rightIndex heightBase height; ipra_ring : Γ ⊢[PRAAx]
      height (rightIndex p q j R A S V) (two*V) (S+j) ≐
        heightBase V S j+monus (A*commonHeight p q j R A S V) (heightBase V S j)).eqTrans (eq_add_of_le hb).eqSymm

theorem same_eta (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    etaDen (leftIndex p q j R A S V) (two*A) (R+j) ≐ etaDen (rightIndex p q j R A S V) (two*V) (S+j) := by
  have exponent := (congrMul (.eqRefl (two*A)) (left_height p q j R A S V hV)).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] (two*A)*(V*commonHeight p q j R A S V) ≐
      (two*V)*(A*commonHeight p q j R A S V)).eqTrans
      (congrMul (.eqRefl (two*V)) (right_height p q j R A S V hA)).eqSymm)
  exact congrAp2 powF exponent (.eqRefl two)

theorem left_top (p q j R A S V : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    top (leftIndex p q j R A S V) (two*A) (R+j) ≐ two*V*commonHeight p q j R A S V :=
  (congrMul (.eqRefl two) (left_height p q j R A S V hV)).eqTrans (by ipra_ring)

theorem right_top (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    top (rightIndex p q j R A S V) (two*V) (S+j) ≐ two*A*commonHeight p q j R A S V :=
  (congrMul (.eqRefl two) (right_height p q j R A S V hA)).eqTrans (by ipra_ring)

theorem top_balance (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    A*top (leftIndex p q j R A S V) (two*A) (R+j) ≐ V*top (rightIndex p q j R A S V) (two*V) (S+j) :=
  (congrMul (.eqRefl A) (left_top p q j R A S V hV)).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] A*(two*V*commonHeight p q j R A S V) ≐ V*(two*A*commonHeight p q j R A S V)).eqTrans
      (congrMul (.eqRefl V) (right_top p q j R A S V hA)).eqSymm)

theorem left_top_bound (p q j R A S V : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    le (top (leftIndex p q j R A S V) (two*A) (R+j)) (commonTop p q j R A S V) :=
  le_of_eq_add (d := two*A*commonHeight p q j R A S V)
    ((by unfold commonTop; ipra_ring : Γ ⊢[PRAAx] commonTop p q j R A S V ≐
      two*V*commonHeight p q j R A S V+two*A*commonHeight p q j R A S V).eqTrans
      (congrAdd (left_top p q j R A S V hV).eqSymm (.eqRefl _)))

theorem right_top_bound (p q j R A S V : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    le (top (rightIndex p q j R A S V) (two*V) (S+j)) (commonTop p q j R A S V) :=
  le_of_eq_add (d := two*V*commonHeight p q j R A S V)
    ((by unfold commonTop; ipra_ring : Γ ⊢[PRAAx] commonTop p q j R A S V ≐
      two*A*commonHeight p q j R A S V+two*V*commonHeight p q j R A S V).eqTrans
      (congrAdd (right_top p q j R A S V hA).eqSymm (.eqRefl _)))

theorem actual_two_certificate_logarithmic_geometry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 4) ⋏ le one (var 6)) ⟶
      (etaDen (leftIndex (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (two*var 4) (var 3+var 2) ≐
         etaDen (rightIndex (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (two*var 6) (var 5+var 2) ⋏
      (le (cutoff (var 0) (var 2) (var 4)) (leftIndex (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⋏
       le (cutoff (var 1) (var 2) (var 6)) (rightIndex (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))) :=
  closeUniv 7 (.impI (.andI (same_eta _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (.andI (left_index_late _ _ _ _ _ _ _ Prf.hyp0.andE₂) (right_index_late _ _ _ _ _ _ _ Prf.hyp0.andE₁))))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCertificateGeometry
