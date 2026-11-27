import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadApartness
import IPRADerivations.Analysis.Gamma.Poles.LocalFactors.GaussianGammaLocalPoleGuards
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedProductApartness

/-!
# Apartness of the original Barnes head with one factor removed

On the closed half-unit disk about the negative integer -m, every other
translated Gaussian integer numerator is nonzero. The two literal
factor ranges before and after m therefore remain apart even at the center.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedHead

open_ipra
open GaussianBarnesCanonicalFactor (source)
open GaussianBarnesCanonicalHeadApartness (allNonzero)
open GaussianGammaEulerHeadLower (translated poleAt)
open GaussianGammaLocalPoleGuards (center translated_pole_left translated_pole_right)
open GaussianGammaPoleZeros (poleNumerator)
open GaussianRootAlgebra
  (equal equal_of_values equal_refl add_equal normSq_equal re_add im_add re_neg im_neg re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (bounded normSq normSq_neg normSq_scale normSq_one scale oneCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameReciprocal (apart)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "Hd" => GaussianBarnesCanonicalHead.data

def neighborhood (z B m : PTm n) : Fm PTm n := bounded (scale two (translated z B m)) B

@[simp] theorem subst_neighborhood {l : ℕ} (σ : Fin n → PTm l) (z B m : PTm n) :
    (neighborhood z B m).subst σ = neighborhood (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [neighborhood,bounded,two,one]

private theorem recenter (z B m : PTm n) : Γ ⊢[PRAAx] equal (center (translated z B m) B m) z := by
  apply equal_of_values <;>
    simp only [center,translated,poleNumerator,re_add,im_add,re_neg,im_neg] <;> ring

theorem off_index_norm (z B m k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] neighborhood z B m) (hk : Γ ⊢[PRAAx] lt k m ⋎ lt m k) :
    Γ ⊢[PRAAx] le one (normSq (translated z B k)) := by
  let d := translated z B m
  have disk : Γ ⊢[PRAAx] bounded (scale two d) (one*B) :=
    ComplexLogarithmRemainder.bounded_mono h (le_congr (.eqRefl _) (one_mul B).eqSymm (le_refl B))
  have exactMargin : Γ ⊢[PRAAx] poleAt (center d B m) B one two k :=
    .orE hk (translated_pole_left d B one one two m k (by ipra_le 0) disk.wk Prf.hyp0)
      (translated_pole_right d B one one two m k (by ipra_le 0) disk.wk Prf.hyp0)
  have e : Γ ⊢[PRAAx] normSq (translated (center d B m) B k) ≐ normSq (translated z B k) :=
    normSq_equal (add_equal (recenter z B m) (equal_refl _))
  have hD : Γ ⊢[PRAAx] le one (one*B) := positive_product _ _ (le_refl one) hB
  have strict := le_trans (positive_product _ _ hD hD)
    (le_congr (.eqRefl _) (congrMul (.eqRefl (two*two)) e) exactMargin)
  exact GaussianDominantScalarOrder.factor_positive_left _ (two*two)
    (le_congr (.eqRefl _) (mul_comm _ _) strict)

private theorem displacement (z B m : PTm n) : Γ ⊢[PRAAx]
    equal (ComplexLogarithmRemainder.add (scale two z) (ComplexLogarithmRemainder.neg (scale two (translated z B m))))
      (ComplexLogarithmRemainder.neg (scale (two*(B*m)) oneCode)) := by
  apply equal_of_values <;>
    simp only [translated,re_add,im_add,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

theorem center_index_bound (z R B m : PTm n) (hs : Γ ⊢[PRAAx] source z R B m)
    (h : Γ ⊢[PRAAx] neighborhood z B m) : Γ ⊢[PRAAx] le m R := by
  let d := translated z B m
  let a := ComplexLogarithmRemainder.add (scale two z) (ComplexLogarithmRemainder.neg (scale two d))
  let W := two*(B*m)
  have dz : Γ ⊢[PRAAx] bounded a (two*(R*B)+B) :=
    ComplexLogarithmRemainder.bounded_add (ComplexLogarithmRemainder.bounded_scale two hs.andE₂.andE₂)
      (ComplexLogarithmRemainder.bounded_neg h)
  have norm : Γ ⊢[PRAAx] normSq a ≐ W*W :=
    (normSq_equal (displacement z B m)).eqTrans ((normSq_neg _).eqTrans ((normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) normSq_one).eqTrans (by dsimp only [W]; ipra_ring))))
  have near : Γ ⊢[PRAAx] le W (two*(R*B)+B) := nat_sqrt_mono (le_congr norm (.eqRefl _) dz)
  have clear : Γ ⊢[PRAAx] le (two*m) (two*R+one) :=
    RationalValueBounds.positive_cancel hs.andE₁ (le_congr (by dsimp only [W]; ipra_ring) (by ipra_ring) near)
  refine .orE (lt_or_le R m) ?_ Prf.hyp0
  have bad : lt R m :: Γ ⊢[PRAAx] le (succ (two*R+one)) (two*R+one) :=
    le_trans (le_congr (by ipra_ring) (mul_comm m two) (mul_le_mul_right two Prf.hyp0)) clear.wk
  exact not_succ_le_self _ _ bad

theorem before_nonzero (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] neighborhood z B m) :
    Γ ⊢[PRAAx] allNonzero z B zero (pred m) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let i : PTm (n+1) := var 0
  let Δ := lt i (pred (sh m)) :: Γ.map Fm.shift
  have hB' : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,one,sh,Δ] using hB.shift.wk
  have hm' : Δ ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,one,sh,Δ] using hm.shift.wk
  have h' : Δ ⊢[PRAAx] neighborhood (sh z) (sh B) (sh m) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have e : Δ ⊢[PRAAx] sh m ≐ succ (pred (sh m)) := AnalyticNumberTheory.PNTStageStep.pos_of_one_le hm'
  have index : Δ ⊢[PRAAx] lt (succ (zero+i)) (sh m) :=
    le_congr ((succ_eq_add_one (succ i)).eqSymm.eqTrans (congrSucc (congrSucc (zero_add i))).eqSymm)
      ((succ_eq_add_one (pred (sh m))).eqSymm.eqTrans e.eqSymm) (add_le_add_right one Prf.hyp0)
  simpa [sh,Δ,i,Syn.shift] using off_index_norm (sh z) (sh B) (sh m) (succ (zero+i)) hB' h' (.orI₁ index)

theorem after_nonzero (z B m r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] neighborhood z B m) :
    Γ ⊢[PRAAx] allNonzero z B m r := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh r) :: Γ.map Fm.shift
  have hB' : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,one,sh,Δ] using hB.shift.wk
  have h' : Δ ⊢[PRAAx] neighborhood (sh z) (sh B) (sh m) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have index : Δ ⊢[PRAAx] lt (sh m) (succ (sh m+i)) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
      (add_le_add_right one (le_add_right _ _))
  exact off_index_norm (sh z) (sh B) (sh m) (succ (sh m+i)) hB' h' (.orI₂ index)

def nameF : PR 2 := multiplyF H H
def data (z R B m r : PTm n) : PTm n := multiplyData H H (Hd z R B zero (pred m)) (Hd z R B m r)

def height (R B m r : PTm n) : PTm n := GaussianNamedProductApartness.height
  (GaussianBarnesCanonicalHeadApartness.clock R B zero (pred m)) (GaussianBarnesCanonicalHeadApartness.clock R B m r)

theorem regular (z R B m r : PTm n) (hs : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B m r) := by
  have h : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B := .andI hs.andE₁ hs.andE₂.andE₂
  exact multiply_fast H H _ _ (GaussianBarnesCanonicalHead.regular z R B zero (pred m) h)
    (GaussianBarnesCanonicalHead.regular z R B m r h)

theorem original_apart (z R B m r : PTm n) (hs : Γ ⊢[PRAAx] source z R B m) (hw : Γ ⊢[PRAAx] neighborhood z B m) :
    Γ ⊢[PRAAx] apart nameF (height R B m r) (data z R B m r) := by
  have h : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B := .andI hs.andE₁ hs.andE₂.andE₂
  exact GaussianNamedProductApartness.original_apart H H (Hd z R B zero (pred m)) (Hd z R B m r) _ _
    (GaussianBarnesCanonicalHead.regular z R B zero (pred m) h) (GaussianBarnesCanonicalHead.regular z R B m r h)
    (GaussianBarnesCanonicalHeadApartness.original_apart z R B zero (pred m) h (before_nonzero z B m hs.andE₁ hs.andE₂.andE₁ hw))
    (GaussianBarnesCanonicalHeadApartness.original_apart z R B m r h (after_nonzero z B m r hs.andE₁ hw))

theorem actual_Barnes_skipped_head_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let m := var 3
     let r := var 4
     (source z R B m ⋏ neighborhood z B m) ⟶ apart nameF (height R B m r) (data z R B m r)) :=
  closeUniv 5 (.impI (original_apart _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedHead
