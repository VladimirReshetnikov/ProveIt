import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelTail
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderBernoulliMeshMargin

/-!
# A positive lower bound on one block of the original weighted mesh

All original rows are nonnegative. On the block from 3S through 4S
on the 8S mesh, the first unit panel has an explicit rational lower
bound independent of S.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPositiveRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num subst_num)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianFactorBudget (power_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation nonnegative_of_lower)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderBernoulliEnvelope (sample_envelope)
open GaussianStirlingAllOrderBernoulliMeshMargin (coarseDen margin positive_margin separated_mesh_margin)
open GaussianStirlingAllOrderCenteredBernoulli (sample endpoint_samples_zero denominator_positive)
open GaussianStirlingAllOrderKernel (row rowWeight offset weight_pos_den weight_nonnegative multiply_zero_right)
open GaussianStirlingAllOrderPairedWeight (weight)
open RationalAlgebra (add_congr add_commutative multiply_commutative)
open RationalArithmetic (add multiply multiply_monotone)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalNormalForm (normalize_well_formed)
open RationalReciprocalPowerTail (add_zero_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def boundDenominator (m : ℕ) (q A B : PTm n) : PTm n :=
  coarseDen m * pw (A+B) (succ q)

def rowFloor (m : ℕ) (q A B : PTm n) : PTm n := fraction one (boundDenominator m q A B)

@[simp] theorem subst_rowFloor {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (q A B : PTm n) :
    Syn.subst σ (rowFloor m q A B) = rowFloor m (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [rowFloor,boundDenominator,coarseDen,GaussianStirlingAllOrderCenteredBernoulli.denominator,pw,one]

theorem coarse_positive (m : ℕ) : Γ ⊢[PRAAx] le one (coarseDen m : PTm n) :=
  denominator_positive (m+1) (num 8) (by ipra_le 7)

theorem floor_den_positive (m : ℕ) (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (boundDenominator m q A B) :=
  positive_product _ _ (coarse_positive m) (power_positive _ _ (le_trans hA (le_add_right _ _)))

theorem row_nonnegative (m : ℕ) (q A B M k r : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (row m q A B M k r) := by
  let v := sample (m+1) r M
  let w := rowWeight q A B M k r
  have h := multiply_monotone w _ v (weight_nonnegative q A B M k r hA hM) (sample_envelope m r M hM hr).andE₁
  exact rationalLE_congr (multiply_zero_right w) (multiply_commutative w v) h

private theorem sample_lower (m : ℕ) (S r : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (hr : Γ ⊢[PRAAx] le (S*num 3) r) (hr' : Γ ⊢[PRAAx] le (two*r) (S*num 8)) :
    Γ ⊢[PRAAx] rationalLE (fraction one (coarseDen m)) (sample (m+1) r (S*num 8)) := by
  let M := S*num 8
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have sep := separated_mesh_margin m S zero r hS (zero_le _) hr hr'
  have e := (add_congr (endpoint_samples_zero (m+1) M hM).1 (.eqRefl (margin m : PTm n))).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right _ (normalize_well_formed _ _ (coarse_positive m))))
  exact transitive (positive_margin m) (rationalLE_congr e (.eqRefl _) sep)

private theorem weight_lower (q A B M r : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] rationalLE (fraction one (pw (A+B) (succ q))) (rowWeight q A B M zero r) := by
  let R := offset A B M zero+B*r
  let Q := succ q
  have hR := weight_pos_den q A B M zero r hA hM
  have hP := power_positive (A+B) Q (le_trans hA (le_add_right _ _))
  have cmp0 : Γ ⊢[PRAAx] le R ((A+B)*M) := by
    dsimp [R,offset]
    ipra_le Groth.ι (IPRA.Q.mk Γ B)*sl hr
  have cmp1 := pw_le_pw Q cmp0
  have cmp2 := pw_le_pw Q
    (le_congr (one_mul M) (.eqRefl _) (mul_le_mul_right M hB))
  have cmp := le_trans (le_congr (.eqRefl _) (pw_mul_base _ _ _) cmp1)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (pw (A+B) Q) cmp2))
  exact fraction_order _ _ _ _ hP hR (le_congr (by ipra_ring) (.eqRefl _) cmp)

theorem positive_box_row (m : ℕ) (q A B S r : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S)
    (hr : Γ ⊢[PRAAx] le (S*num 3) r) (hr' : Γ ⊢[PRAAx] le (two*r) (S*num 8)) :
    Γ ⊢[PRAAx] rationalLE (rowFloor m q A B) (row m q A B (S*num 8) zero r) := by
  let M := S*num 8
  let v := sample (m+1) r M
  let w := rowWeight q A B M zero r
  let a : PTm n := fraction one (coarseDen m)
  let p := pw (A+B) (succ q)
  let s := fraction one p
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have hP := power_positive (A+B) (succ q) (le_trans hA (le_add_right _ _))
  have hD := coarse_positive (Γ := Γ) m
  have hv := sample_lower m S r hS hr hr'
  have hw := weight_lower q A B M r hA hB hM (le_trans (by ipra_le Groth.ι (IPRA.Q.mk Γ r)) hr')
  have ha := nonnegative_of_representation (Γ := Γ) a one _ hD (fraction_represents one _ hD)
  have h := multiply_monotone a s w ha hw
  have k := multiply_monotone w a v (weight_nonnegative q A B M zero r hA hM) hv
  have eq : Γ ⊢[PRAAx] multiply a s ≐ rowFloor m q A B :=
    (fraction_multiply _ _ _ _ hD hP).eqTrans (fraction_congr (one_mul _) (.eqRefl _))
  exact transitive (rationalLE_congr eq (multiply_commutative a w) h)
    (rationalLE_congr (.eqRefl _) (multiply_commutative w v) k)

theorem actual_original_positive_reciprocal_box_rows_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
        (le (var 3*num 3) (var 4) ⋏ le (two*var 4) (var 3*num 8)) ⟶
        rationalLE (rowFloor m (var 0) (var 1) (var 2)) (row m (var 0) (var 1) (var 2) (var 3*num 8) zero (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (positive_box_row m _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPositiveRows
