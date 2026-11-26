import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinDecayPrefix
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactPowerMajorant
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Original Mellin quadrature on a positive time window

The compact left grid evaluates the original Mellin name and a finite
sum of the actual Euler decay samples at the same rational times.
A computed observation clock covers all decay rows uniformly.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinStrip

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaZetaMellinDecayPrefix
  (weightedValue roundingCost errorNumerator errorDenominator weighted_error)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Actual" => GaussianGammaZetaMellinIntegrand.nameF
local notation "actualData" => GaussianGammaZetaMellinIntegrand.data
local notation "parameterSource" => GaussianEulerExponentCompactBounds.source
local notation "timeDomain" => GaussianCompactLogarithmBounds.domain

def window (A C E H T : PTm n) : Fm PTm n :=
  (le one A ⋏ le one E) ⋏ (le E (H*A) ⋏ le (A+C) (T*E))

def data (p z D M N A C E : PTm n) : PTm n := sampleData p M A C E (pairT N (pairT z D))

private def entries (i d : PTm n) : Fin 6 → PTm n :=
  ![field0 d,fstT (field5 d),fstT (sndT (field5 d)),sndT (sndT (field5 d)),
    field2 d*field1 d+field3 d*i,field4 d*field1 d]

private def packed (f : PTm 6) : PTm 2 := Syn.subst (entries (var 0) (var 1)) f

def mellinBody : PTm 2 := packed (ap2 Actual (var 0) (actualData (var 2) (var 3) (var 4) (var 5)))
def decayBody : PTm 2 := packed (weightedValue (var 0) (var 2) (var 3) (var 4) (var 5) (var 1))
private def budgetBody : PTm 2 := packed (roundingCost (var 1) (var 4) (var 5))

def mellinValue (p z D M N A C E : PTm n) : PTm n := leftSum mellinBody M (data p z D M N A C E) C E
def decayValue (p z D M N A C E : PTm n) : PTm n := leftSum decayBody M (data p z D M N A C E) C E
def gridBudget (M N A C E : PTm n) : PTm n :=
  ap2 (LeanProofs.IPRA.sumF budgetBody) M (data zero zero zero M N A C E)
def clock (h M N A C E : PTm n) : PTm n := exponent (gridBudget M N A C E) h

@[simp] theorem subst_window {m : ℕ} (σ : Fin n → PTm m) (A C E H T : PTm n) :
    (window A C E H T).subst σ = window (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ T) := by
  simp [window,one]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p z D M N A C E : PTm n) :
    Syn.subst σ (data p z D M N A C E) =
      data (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ N)
        (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [data]
@[simp] theorem subst_mellinValue {m : ℕ} (σ : Fin n → PTm m) (p z D M N A C E : PTm n) :
    Syn.subst σ (mellinValue p z D M N A C E) =
      mellinValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ N)
        (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [mellinValue]
@[simp] theorem subst_decayValue {m : ℕ} (σ : Fin n → PTm m) (p z D M N A C E : PTm n) :
    Syn.subst σ (decayValue p z D M N A C E) =
      decayValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ N)
        (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [decayValue]
@[simp] theorem subst_gridBudget {m : ℕ} (σ : Fin n → PTm m) (M N A C E : PTm n) :
    Syn.subst σ (gridBudget M N A C E) = gridBudget (Syn.subst σ M) (Syn.subst σ N)
      (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [gridBudget]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (h M N A C E : PTm n) :
    Syn.subst σ (clock h M N A C E) = clock (Syn.subst σ h) (Syn.subst σ M) (Syn.subst σ N)
      (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [clock]

private theorem packed_at (f : PTm 6) (i p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst2 (packed f) i (data p z D M N A C E) ≐ Syn.subst ![p,N,z,D,A*M+C*i,E*M] f := by
  let d := data p z D M N A C E
  have read : inst2 (packed f) i d = Syn.subst (entries i d) f := by
    simp only [packed,inst2,Syn.subst_subst]
    congr 1
    funext k
    fin_cases k <;> simp [entries]
  rw [read]
  have tail : Γ ⊢[PRAAx] field5 d ≐ pairT N (pairT z D) := field5_at _ _ _ _ _ _
  have stem := (congrSnd tail).eqTrans (snd_pair N (pairT z D))
  exact Prf.eqCongr (Γ := Γ) (Ax := PRAAx) f (σ := entries i d) (σ' := ![p,N,z,D,A*M+C*i,E*M]) (fun j => by
    fin_cases j
    · exact field0_at _ _ _ _ _ _
    · exact (congrFst tail).eqTrans (fst_pair _ _)
    · exact (congrFst stem).eqTrans (fst_pair _ _)
    · exact (congrSnd stem).eqTrans (snd_pair _ _)
    · exact congrAdd (congrMul (field2_at _ _ _ _ _ _) (field1_at _ _ _ _ _ _))
        (congrMul (field3_at _ _ _ _ _ _) (.eqRefl i))
    · exact congrMul (field4_at _ _ _ _ _ _) (field1_at _ _ _ _ _ _))

theorem mellin_row_at (i p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst2 mellinBody i (data p z D M N A C E) ≐
      ap2 Actual p (actualData z D (A*M+C*i) (E*M)) := by
  simpa [mellinBody] using packed_at (Γ := Γ) (ap2 Actual (var 0) (actualData (var 2) (var 3) (var 4) (var 5)))
    i p z D M N A C E

theorem decay_row_at (i p z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst2 decayBody i (data p z D M N A C E) ≐ weightedValue p z D (A*M+C*i) (E*M) N := by
  simpa [decayBody] using packed_at (Γ := Γ) (weightedValue (var 0) (var 2) (var 3) (var 4) (var 5) (var 1))
    i p z D M N A C E

theorem tag_budget (i M N A C E : PTm n) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] le (roundingCost N (A*M+C*i) (E*M)) (gridBudget M N A C E) := by
  have eq : Γ ⊢[PRAAx] inst2 budgetBody i (data zero zero zero M N A C E) ≐ roundingCost N (A*M+C*i) (E*M) := by
    simpa [budgetBody] using packed_at (Γ := Γ) (roundingCost (var 1) (var 4) (var 5)) i zero zero zero M N A C E
  exact le_congr eq (.eqRefl _) (LeanProofs.IPRA.term_le_sum budgetBody hi)

theorem tag_domain (i M A C E H T : PTm n) (hw : Γ ⊢[PRAAx] window A C E H T)
    (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] le i M) :
    Γ ⊢[PRAAx] timeDomain (A*M+C*i) (E*M) H T := by
  have hA := le_trans (positive_product _ _ hw.andE₁.andE₁ hM) (le_add_right (A*M) (C*i))
  have hb := positive_product _ _ hw.andE₁.andE₂ hM
  have lower : Γ ⊢[PRAAx] le (E*M) (H*(A*M+C*i)) :=
    le_trans (mul_le_mul_right M hw.andE₂.andE₁)
      (le_of_eq_add (d := H*(C*i)) (by ipra_ring))
  have grid_upper : Γ ⊢[PRAAx] le (A*M+C*i) ((A+C)*M) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (A*M)) (mul_le_mul_right C hi))
  have upper : Γ ⊢[PRAAx] le (A*M+C*i) (T*(E*M)) :=
    le_trans grid_upper (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right M hw.andE₂.andE₂))
  exact .andI (.andI hA hb) (.andI lower upper)

theorem row_error (i p h z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T)
    (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] lt i M)
    (hc : Γ ⊢[PRAAx] le (gridBudget M N A C E*unit h) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (inst2 decayBody i (data p z D M N A C E))
      (inst2 mellinBody i (data p z D M N A C E))
      (errorNumerator h H N (majorant R H T)) (errorDenominator h H N) := by
  let a := A*M+C*i
  let b := E*M
  let k := GaussianGammaZetaMellinIntegrand.factorClock p z D a b
  have ht := tag_domain i M A C E H T hw hM (le_of_lt hi)
  have budget := le_trans (mul_le_mul_right (unit h) (tag_budget i M N A C E hi)) hc
  have e := weighted_error p h z D a b N H (majorant R H T) (.andI hz.andE₁ ht.andE₁)
    hz.andE₂.andE₁ ht.andE₂.andE₁ (original_power_observation k z R D H T a b hz ht) budget
  exact distance_congr (decay_row_at i p z D M N A C E).eqSymm (mellin_row_at i p z D M N A C E).eqSymm
    (.eqRefl _) (.eqRefl _) e

theorem quadrature_error (p h z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T) (hM : Γ ⊢[PRAAx] le one M)
    (hc : Γ ⊢[PRAAx] le (gridBudget M N A C E*unit h) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (decayValue p z D M N A C E) (mellinValue p z D M N A C E)
      (C*errorNumerator h H N (majorant R H T)) (E*errorDenominator h H N) := by
  let d := data p z D M N A C E
  let U := errorDenominator h H N
  let K := errorNumerator h H N (majorant R H T)
  have hU := positive_product _ _ (le_trans hz.andE₂.andE₁ (le_add_right H N)) (unit_positive h)
  have rows : Γ ⊢[PRAAx] termsDistance decayBody mellinBody M d d K U := by
    refine .allI (.impI ?_)
    let s (x : PTm n) := Syn.shift x
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] parameterSource (s z) (s R) (s D) (s H) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ws : Δ ⊢[PRAAx] window (s A) (s C) (s E) (s H) (s T) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hw.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift.wk
    have cs : Δ ⊢[PRAAx] le (gridBudget (s M) (s N) (s A) (s C) (s E)*unit (s h)) (unit (s p)) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hc.shift.wk
    simpa only [Δ,s,d,K,U,Syn.shift,subst_data,GaussianGammaZetaMellinDecayPrefix.subst_errorNumerator,
      GaussianGammaZetaMellinDecayPrefix.subst_errorDenominator,majorant,GaussianEulerCompactPowerMajorant.exponentRadius,
      subst_ap2,PTm.subst_num,PTm.subst_add,PTm.subst_mul,GaussianCompactLogarithmBounds.subst_radius,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      row_error (var 0) (s p) (s h) (s z) (s R) (s D) (s M) (s N) (s A) (s C) (s E) (s H) (s T) zs ws ms Prf.hyp0 cs
  exact GaussianCompactScalarMajorant.common_mesh_distance decayBody mellinBody M d d C E K U hM hw.andE₁.andE₂ hU rows

theorem scheduled_error (h z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T) (hM : Γ ⊢[PRAAx] le one M) :
    let p := clock h M N A C E
    Γ ⊢[PRAAx] distanceBounded (decayValue p z D M N A C E) (mellinValue p z D M N A C E)
      (C*errorNumerator h H N (majorant R H T)) (E*errorDenominator h H N) :=
  quadrature_error (clock h M N A C E) h z R D M N A C E H T hz hw hM (query_budget _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinStrip
