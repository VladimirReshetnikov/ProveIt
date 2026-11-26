import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicClientIndependence
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffSplit
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCoefficients

/-!
# Strict splits of the actual original logarithmic cutoff names

The numerical cutoffs use margin 2A and degree R+j, while every actual
logarithmic evaluator retains its original client radius R and order j.
Two genuine compact additions split the later interval. Exact original
cutoff refinement and checked client transport identify its middle with
the unchanged earlier full name, including that name's original clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCutoffSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicIntervalName (nameF data name_regular)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaCompactCutoffGeometry (ratio lowerWidth middleWidth upperWidth)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCompactCutoffSplit (add_data_congr)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A k l : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏ (le one A ⋏ lt k l)
def fullData (j z R B A k : PTm n) : PTm n :=
  data j z R B one (width k (two*A) (R+j)) (etaDen k (two*A) (R+j)) (top k (two*A) (R+j))
def lowerData (j z R B A k l : PTm n) : PTm n :=
  data j z R B one (lowerWidth k l (two*A)) (etaDen l (two*A) (R+j)) (top l (two*A) (R+j))
def middleData (j z R B A k l : PTm n) : PTm n :=
  data j z R B (ratio k l (two*A)) (middleWidth k l (two*A) (R+j))
    (etaDen l (two*A) (R+j)) (top l (two*A) (R+j))
def upperData (j z R B A k l : PTm n) : PTm n :=
  data j z R B (etaDen l (two*A) (R+j)*top k (two*A) (R+j)) (upperWidth k l (two*A) (R+j))
    (etaDen l (two*A) (R+j)) (top l (two*A) (R+j))
def rightData (j z R B A k l : PTm n) : PTm n :=
  data j z R B (ratio k l (two*A)) (middleWidth k l (two*A) (R+j)+upperWidth k l (two*A) (R+j))
    (etaDen l (two*A) (R+j)) (top l (two*A) (R+j))
abbrev tripleF : PR 2 := addF nameF (addF nameF nameF)
def geometricData (j z R B A k l : PTm n) : PTm n :=
  addData (lowerData j z R B A k l) (addData (middleData j z R B A k l) (upperData j z R B A k l))
def splitData (j z R B A k l : PTm n) : PTm n :=
  addData (lowerData j z R B A k l) (addData (fullData j z R B A k) (upperData j z R B A k l))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A k l : PTm n) :
    (source z R B A k l).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by simp [source]
@[simp] theorem subst_fullData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k : PTm n) :
    Syn.subst σ (fullData j z R B A k) = fullData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) := by
  simp [fullData,width,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k l : PTm n) :
    Syn.subst σ (lowerData j z R B A k l) = lowerData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by
  simp [lowerData,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_middleData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k l : PTm n) :
    Syn.subst σ (middleData j z R B A k l) = middleData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by
  simp [middleData,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_upperData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k l : PTm n) :
    Syn.subst σ (upperData j z R B A k l) = upperData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by
  simp [upperData,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_rightData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k l : PTm n) :
    Syn.subst σ (rightData j z R B A k l) = rightData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by
  simp [rightData,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_geometricData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k l : PTm n) :
    Syn.subst σ (geometricData j z R B A k l) = geometricData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by simp [geometricData]
@[simp] theorem subst_splitData {m : ℕ} (σ : Fin n → PTm m) (j z R B A k l : PTm n) :
    Syn.subst σ (splitData j z R B A k l) = splitData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ l) := by simp [splitData]

private theorem enlarged_source (j z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) : Γ ⊢[PRAAx]
    GaussianEulerUpperPowerCoefficients.source z (R+j) B :=
  .andI h.andE₁ (le_trans h.andE₂ (sq_le_sq (mul_le_mul_right B (le_add_right R j))))

private theorem geometry_source (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    GaussianGammaCompactCutoffSplit.source z (R+j) B k l (two*A) :=
  .andI (enlarged_source j z R B h.andE₁)
    (.andI (positive_product _ _ (zero_lt_succ one) h.andE₂.andE₁) (le_of_lt h.andE₂.andE₂))

private theorem original_radius (z R S B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hs : Γ ⊢[PRAAx] intervalSource z S B a C E T) : Γ ⊢[PRAAx] intervalSource z R B a C E T :=
  .andI (.andI h.andE₁ (.andI hs.andE₁.andE₂.andE₁ h.andE₂)) hs.andE₂

theorem interval_data_congr (j z R B a C E T a' C' E' T' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C')
    (hE : Γ ⊢[PRAAx] E ≐ E') (hT : Γ ⊢[PRAAx] T ≐ T') : Γ ⊢[PRAAx]
    data j z R B a C E T ≐ data j z R B a' C' E' T' := by
  have first : Γ ⊢[PRAAx] data j z R B a C E T ≐ data j z R B a' C E T := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0)
        (Syn.shift C) (Syn.shift E) (Syn.shift T)) ha
  have second : Γ ⊢[PRAAx] data j z R B a' C E T ≐ data j z R B a' C' E T := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a')
        (var 0) (Syn.shift E) (Syn.shift T)) hC
  have third : Γ ⊢[PRAAx] data j z R B a' C' E T ≐ data j z R B a' C' E' T := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a')
        (Syn.shift C') (var 0) (Syn.shift T)) hE
  have fourth : Γ ⊢[PRAAx] data j z R B a' C' E' T ≐ data j z R B a' C' E' T' := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a')
        (Syn.shift C') (Syn.shift E') (var 0)) hT
  exact first.eqTrans (second.eqTrans (third.eqTrans fourth))

private theorem interval_congr (z R B a C E T a' C' E' T' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C')
    (hE : Γ ⊢[PRAAx] E ≐ E') (hT : Γ ⊢[PRAAx] T ≐ T')
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx] intervalSource z R B a' C' E' T' :=
  .andI (.andI h.andE₁.andE₁ (.andI (le_congr (.eqRefl _) hE h.andE₁.andE₂.andE₁) h.andE₁.andE₂.andE₂))
    (.andI (le_congr (.eqRefl _) ha h.andE₂.andE₁) (le_congr (congrAdd ha hC) (congrMul hE hT) h.andE₂.andE₂))

theorem full_source (j z R B A k : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) : Γ ⊢[PRAAx]
    intervalSource z R B one (width k (two*A) (R+j)) (etaDen k (two*A) (R+j)) (top k (two*A) (R+j)) :=
  .andI (.andI h.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive k (two*A) (R+j)) h.andE₂))
    (.andI (le_refl _) (le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k (two*A) (R+j)).eqSymm
      (.eqRefl _) (le_refl _)))
theorem lower_source (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    intervalSource z R B one (lowerWidth k l (two*A)) (etaDen l (two*A) (R+j)) (top l (two*A) (R+j)) :=
  original_radius _ _ _ _ _ _ _ _ h.andE₁ (GaussianGammaCompactCutoffSplit.lower_source _ _ _ _ _ _ (geometry_source j z R B A k l h))
theorem middle_source (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    intervalSource z R B (ratio k l (two*A)) (middleWidth k l (two*A) (R+j))
      (etaDen l (two*A) (R+j)) (top l (two*A) (R+j)) :=
  original_radius _ _ _ _ _ _ _ _ h.andE₁ (GaussianGammaCompactCutoffSplit.middle_source _ _ _ _ _ _ (geometry_source j z R B A k l h))
theorem upper_source (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    intervalSource z R B (etaDen l (two*A) (R+j)*top k (two*A) (R+j)) (upperWidth k l (two*A) (R+j))
      (etaDen l (two*A) (R+j)) (top l (two*A) (R+j)) :=
  original_radius _ _ _ _ _ _ _ _ h.andE₁ (GaussianGammaCompactCutoffSplit.upper_source _ _ _ _ _ _ (geometry_source j z R B A k l h))
theorem right_source (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    intervalSource z R B (ratio k l (two*A)) (middleWidth k l (two*A) (R+j)+upperWidth k l (two*A) (R+j))
      (etaDen l (two*A) (R+j)) (top l (two*A) (R+j)) :=
  original_radius _ _ _ _ _ _ _ _ h.andE₁ (GaussianGammaCompactCutoffSplit.right_source _ _ _ _ _ _ (geometry_source j z R B A k l h))

theorem original_middle_alignment (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (fullData j z R B A k) (middleData j z R B A k l) := by
  let b := two*A
  let d := R+j
  let m := ratio k l b
  let C := width k b d
  let E := etaDen k b d
  let T := top k b d
  let U := top l b d
  have refinement := GaussianGammaCompactCutoffGeometry.eta_den_refinement k l b d (le_of_lt h.andE₂.andE₂)
  have scaled := interval_congr z R B m (middleWidth k l b d) (etaDen l b d) U
    (m*one) (m*C) (m*E) U (by ipra_ring) (.eqRefl _) refinement (.eqRefl _)
    (middle_source j z R B A k l h)
  have aligned := GaussianEulerLogarithmicClientIndependence.original_rescaled_client m j z R R B one C E T U
    (full_source j z R B A k h.andE₁) scaled (GaussianGammaCompactCutoffGeometry.ratio_positive k l b)
  have literal : Γ ⊢[PRAAx] data j z R B (m*one) (m*C) (m*E) U ≐ middleData j z R B A k l :=
    interval_data_congr j z R B _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) refinement.eqSymm (.eqRefl _)
  exact cross_data_congr nameF nameF (fullData j z R B A k) (fullData j z R B A k) _ _ (.eqRefl _) literal aligned

theorem full_regular (j z R B A k : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) : Γ ⊢[PRAAx]
    pointCN nameF (fullData j z R B A k) := name_regular j z R B _ _ _ _ (full_source j z R B A k h)
theorem lower_regular (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    pointCN nameF (lowerData j z R B A k l) := name_regular j z R B _ _ _ _ (lower_source j z R B A k l h)
theorem middle_regular (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    pointCN nameF (middleData j z R B A k l) := name_regular j z R B _ _ _ _ (middle_source j z R B A k l h)
theorem upper_regular (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    pointCN nameF (upperData j z R B A k l) := name_regular j z R B _ _ _ _ (upper_source j z R B A k l h)
theorem right_regular (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    pointCN nameF (rightData j z R B A k l) := name_regular j z R B _ _ _ _ (right_source j z R B A k l h)

theorem strict_geometric_split (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    crossEquivalent nameF tripleF (fullData j z R B A l) (geometricData j z R B A k l) := by
  let b := two*A
  let d := R+j
  let lo := lowerWidth k l b
  let mid := middleWidth k l b d
  let up := upperWidth k l b d
  let E := etaDen l b d
  let T := top l b d
  have hp := le_of_lt h.andE₂.andE₂
  have lp := GaussianGammaCompactCutoffGeometry.lower_positive k l b
    (positive_product _ _ (zero_lt_succ one) h.andE₂.andE₁) h.andE₂.andE₂
  have mp := GaussianGammaCompactCutoffGeometry.middle_positive (Γ := Γ) k l b d
  have upos := GaussianGammaCompactCutoffGeometry.upper_positive k l b d h.andE₂.andE₂
  have widths : Γ ⊢[PRAAx] width l b d ≐ lo+(mid+up) :=
    (GaussianGammaCompactCutoffGeometry.widths_total k l b d hp).eqSymm.eqTrans (add_assoc _ _ _)
  have firstInterval := interval_congr z R B one (width l b d) E T one (lo+(mid+up)) E T
    (.eqRefl _) widths (.eqRefl _) (.eqRefl _) (full_source j z R B A l h.andE₁)
  have firstSource : Γ ⊢[PRAAx] GaussianEulerLogarithmicIntervalAdditivity.source z R B one lo (mid+up) E T :=
    .andI firstInterval (.andI lp (le_trans mp (le_add_right mid up)))
  have secondSource : Γ ⊢[PRAAx] GaussianEulerLogarithmicIntervalAdditivity.source z R B (ratio k l b) mid up E T :=
    .andI (right_source j z R B A k l h) (.andI mp upos)
  have first := GaussianEulerLogarithmicIntervalAdditivity.original_additivity j z R B one lo (mid+up) E T firstSource
  have leftEq : Γ ⊢[PRAAx] data j z R B one (lo+(mid+up)) E T ≐ fullData j z R B A l :=
    interval_data_congr _ _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _) widths.eqSymm (.eqRefl _) (.eqRefl _)
  have rightEq : Γ ⊢[PRAAx] GaussianEulerLogarithmicIntervalAdditivity.addedData j z R B one lo (mid+up) E T ≐
      addData (lowerData j z R B A k l) (rightData j z R B A k l) :=
    add_data_congr _ _ _ _ (.eqRefl _) (interval_data_congr _ _ _ _ _ _ _ _ _ _ _ _
      (GaussianGammaCompactCutoffGeometry.lower_endpoint k l b) (.eqRefl _) (.eqRefl _) (.eqRefl _))
  have movedFirst := cross_data_congr _ _ _ _ _ _ leftEq rightEq first
  have second := GaussianEulerLogarithmicIntervalAdditivity.original_additivity j z R B (ratio k l b) mid up E T secondSource
  have rightSecond : Γ ⊢[PRAAx] GaussianEulerLogarithmicIntervalAdditivity.addedData j z R B (ratio k l b) mid up E T ≐
      addData (middleData j z R B A k l) (upperData j z R B A k l) :=
    add_data_congr _ _ _ _ (.eqRefl _) (interval_data_congr _ _ _ _ _ _ _ _ _ _ _ _
      (GaussianGammaCompactCutoffGeometry.middle_endpoint k l b d hp) (.eqRefl _) (.eqRefl _) (.eqRefl _))
  have movedSecond := cross_data_congr _ _ _ _ _ _ (.eqRefl (rightData j z R B A k l)) rightSecond second
  have proper := GaussianNameArithmetic.add_equivalent nameF nameF nameF (addF nameF nameF)
    (lowerData j z R B A k l) (lowerData j z R B A k l) (rightData j z R B A k l)
    (addData (middleData j z R B A k l) (upperData j z R B A k l))
    (lower_regular j z R B A k l h) (lower_regular j z R B A k l h) (right_regular j z R B A k l h)
    (add_fast _ _ _ _ (middle_regular j z R B A k l h) (upper_regular j z R B A k l h))
    (GaussianNameEquivalence.diagonal_refl _ _) (cross_to_diagonal _ _ _ _ movedSecond)
  exact cross_trans _ _ _ _ _ _ movedFirst proper

theorem replace_middle (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    crossEquivalent tripleF tripleF (geometricData j z R B A k l) (splitData j z R B A k l) := by
  have old := original_middle_alignment j z R B A k l h
  have inner := GaussianNameArithmetic.add_equivalent nameF nameF nameF nameF
    (middleData j z R B A k l) (fullData j z R B A k) (upperData j z R B A k l) (upperData j z R B A k l)
    (middle_regular j z R B A k l h) (full_regular j z R B A k h.andE₁)
    (upper_regular j z R B A k l h) (upper_regular j z R B A k l h)
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ old)) (GaussianNameEquivalence.diagonal_refl _ _)
  exact GaussianNameArithmetic.add_equivalent nameF nameF (addF nameF nameF) (addF nameF nameF)
    (lowerData j z R B A k l) (lowerData j z R B A k l)
    (addData (middleData j z R B A k l) (upperData j z R B A k l))
    (addData (fullData j z R B A k) (upperData j z R B A k l))
    (lower_regular j z R B A k l h) (lower_regular j z R B A k l h)
    (add_fast _ _ _ _ (middle_regular j z R B A k l h) (upper_regular j z R B A k l h))
    (add_fast _ _ _ _ (full_regular j z R B A k h.andE₁) (upper_regular j z R B A k l h))
    (GaussianNameEquivalence.diagonal_refl _ _) (cross_to_diagonal _ _ _ _ inner)

theorem strict_original_split (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    crossEquivalent nameF tripleF (fullData j z R B A l) (splitData j z R B A k l) :=
  cross_trans _ _ _ _ _ _ (strict_geometric_split j z R B A k l h) (replace_middle j z R B A k l h)

theorem original_observations (s t j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A k l) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 nameF s (fullData j z R B A l))
      (GaussianRationalHorner.qadd (ap2 nameF t (lowerData j z R B A k l))
        (GaussianRationalHorner.qadd (ap2 nameF t (fullData j z R B A k)) (ap2 nameF t (upperData j z R B A k l))))
      (GaussianCoefficientNameBounds.unit t+LeanProofs.IPRA.PTm.num 7*GaussianCoefficientNameBounds.unit s)
      (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) := by
  let P := GaussianCoefficientNameBounds.unit s
  let Q := GaussianCoefficientNameBounds.unit t
  let L := lowerData j z R B A k l
  let M := fullData j z R B A k
  let U := upperData j z R B A k l
  have hp := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) s
  have hq := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) t
  have hd := positive_product _ _ hp hq
  have lc := lower_regular j z R B A k l h
  have mc := full_regular j z R B A k h.andE₁
  have uc := upper_regular j z R B A k l h
  have outer := GaussianNameRingLaws.add_sample_error nameF (addF nameF nameF) L (addData M U) t lc (add_fast _ _ _ _ mc uc)
  have inner := GaussianNameRingLaws.add_sample_error nameF nameF M U t mc uc
  have inner' := GaussianNameRingLaws.sum_right_error (ap2 nameF t L) _ _ _ _ hq inner
  have raw := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hq outer inner'
  have scaled : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 tripleF t (splitData j z R B A k l))
      (GaussianRationalHorner.qadd (ap2 nameF t L) (GaussianRationalHorner.qadd (ap2 nameF t M) (ap2 nameF t U)))
      (LeanProofs.IPRA.PTm.num 6*P) (P*Q) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hq hd
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold GaussianNameRingLaws.three; ipra_ring)) raw
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hd
      (GaussianNameEquivalence.cross_at _ _ _ _ s t (strict_original_split j z R B A k l h)) scaled)

theorem actual_strict_original_logarithmic_cutoff_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent nameF tripleF (fullData (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))
        (splitData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (strict_original_split _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCutoffSplit
