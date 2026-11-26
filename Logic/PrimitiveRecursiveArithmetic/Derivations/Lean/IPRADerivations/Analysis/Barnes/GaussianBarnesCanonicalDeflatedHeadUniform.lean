import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDeflatedHead
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFactorApartness

/-!
# Denominator-independent separation of the deflated Barnes head

The native half-unit displacement at each retained index supplies a
rational lower bound 1/(2*k) for its base. Propagating the bound through
the original exponential, the internal power and the original product
clock makes the head apartness witness independent of the input's
rational denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedHeadUniform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDeflatedHead (neighborhood nameF data)
open GaussianBarnesCanonicalHead (factor_at parameters body)
open GaussianBarnesCanonicalFactorApartness (minimumClock denominator denominator_positive power_lower)
open GaussianGammaEulerHeadLower (translated poleAt)
open GaussianGammaLocalPoleGuards (center translated_pole_left translated_pole_right)
open GaussianGammaPoleZeros (poleNumerator)
open GaussianRootAlgebra (equal equal_of_values equal_refl add_equal normSq_equal re_add im_add re_neg im_neg)
open ComplexLogarithmRemainder (bounded normSq scale)
open GaussianGammaCanonicalExponent (constantF)
open GaussianCoefficientNameBounds (unit)
open GaussianCyclicExponentialSamples (inverseBudget sampleBound exponential_lower)
open GaussianRationalHorner (positive_product)
open GaussianRationalLowerBounds (lower_from_representation product_lower)
open GaussianNamedFiniteProductFamily (rowF)
open GaussianNamedFiniteProductApartness (rowLowerAt sample_lower apartClock clock_budget weaken_margin)
open GaussianNameReciprocal (lower apart anchor lower_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "rows" => rowF F body
local notation "factorSource" => GaussianBarnesCanonicalFactor.source
local notation "headSource" => GaussianBarnesCanonicalHead.source

def avoids (m N r : PTm n) : Fm PTm n := le (N+r) (pred m) ⋎ le m N

def rowDenominator (R N r : PTm n) : PTm n := denominator R (two*succ (N+r)) (N+r)
def rangeHeight (R N r : PTm n) : PTm n := minimumClock R+apartClock r (rowDenominator R N r)

def height (R m r : PTm n) : PTm n :=
  GaussianNamedProductApartness.height (rangeHeight R zero (pred m)) (rangeHeight R m r)

@[simp] theorem subst_avoids {l : ℕ} (σ : Fin n → PTm l) (m N r : PTm n) :
    (avoids m N r).subst σ = avoids (Syn.subst σ m) (Syn.subst σ N) (Syn.subst σ r) := by simp [avoids]

@[simp] theorem subst_rowDenominator {l : ℕ} (σ : Fin n → PTm l) (R N r : PTm n) :
    Syn.subst σ (rowDenominator R N r) = rowDenominator (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [rowDenominator,two,one]

theorem off_index_margin (z B m k : PTm n) (h : Γ ⊢[PRAAx] neighborhood z B m)
    (hk : Γ ⊢[PRAAx] lt k m ⋎ lt m k) : Γ ⊢[PRAAx] poleAt z B one two k := by
  let d := translated z B m
  have disk : Γ ⊢[PRAAx] bounded (scale two d) (one*B) :=
    ComplexLogarithmRemainder.bounded_mono h (le_congr (.eqRefl _) (one_mul B).eqSymm (le_refl B))
  have margin : Γ ⊢[PRAAx] poleAt (center d B m) B one two k :=
    .orE hk (translated_pole_left d B one one two m k (by ipra_le 0) disk.wk Prf.hyp0)
      (translated_pole_right d B one one two m k (by ipra_le 0) disk.wk Prf.hyp0)
  have recenter : Γ ⊢[PRAAx] equal (center d B m) z := by
    apply equal_of_values <;>
      simp only [d,center,translated,poleNumerator,re_add,im_add,re_neg,im_neg] <;> ring
  have e := normSq_equal (add_equal recenter (equal_refl (scale (B*k) ComplexLogarithmRemainder.oneCode)))
  exact le_congr (.eqRefl _) (congrMul (.eqRefl (two*two)) e) margin

theorem base_lower (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le one k) (hm : Γ ⊢[PRAAx] poleAt z B one two k) :
    Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (GaussianBarnesCanonicalFactor.base z B k) one (two*k) :=
  lower_from_representation _ _ _ _ _ (positive_product _ _ hB hk)
    (positive_product _ _ (le_succ_self one) hk) (GaussianBarnesCanonicalBase.base_represents z B k hB hk)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (k*k) hm))

theorem factor_lower (p z R B k : PTm n) (h : Γ ⊢[PRAAx] factorSource z R B k)
    (hm : Γ ⊢[PRAAx] poleAt z B one two k) (hp : Γ ⊢[PRAAx] le (minimumClock R) p) :
    Γ ⊢[PRAAx] lower (ap2 F p (GaussianBarnesCanonicalFactor.data z R B k)) (denominator R (two*k) k) := by
  let S := GaussianBarnesCanonicalFactor.exponentRadius R
  let t := GaussianBarnesCanonicalFactor.clock p z R B k
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have cap : Γ ⊢[PRAAx] le (two*inverseBudget S) (unit (minimumClock R)) :=
    (GaussianRootSchedule.binary_length_correct (two*inverseBudget S)).andE₁
  have ex := exponential_lower constantF S (GaussianBarnesCanonicalFactor.correction z B k) t
    (GaussianBarnesCanonicalFactor.exponential_input z R B k h)
    (le_trans cap (GaussianBalancedRadiusArithmetic.unit_monotone (minimumClock R) t (le_trans hp ht)))
  have hk := h.andE₂.andE₁
  have hd := positive_product _ _ (le_succ_self one) hk
  have pow := power_lower (GaussianBarnesCanonicalFactor.base z B k) (two*k) k hd (base_lower z B k h.andE₁ hk hm)
  have expDen := positive_product (Γ := Γ) two (sampleBound S) (le_succ_self one)
    (GaussianFactorBudget.power_positive (num 3) S (le_trans (le_succ_self one) (le_succ_self two)))
  exact GaussianRationalLowerBounds.lower_congr (GaussianBarnesCanonicalFactor.sample_at p z R B k).eqSymm
    (one_mul one) (.eqRefl _)
    (product_lower _ _ one _ one _ (GaussianFactorBudget.power_positive _ _ hd) expDen pow ex)

private theorem lt_succ_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a (succ b) :=
  le_congr (succ_eq_add_one a).eqSymm (succ_eq_add_one b).eqSymm (add_le_add_right one h)

private theorem range_row_lower (p z R B m N r i : PTm n) (h : Γ ⊢[PRAAx] factorSource z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) (he : Γ ⊢[PRAAx] avoids m N r)
    (hi : Γ ⊢[PRAAx] lt i r) (hp : Γ ⊢[PRAAx] le (minimumClock R) p) :
    Γ ⊢[PRAAx] lower (ap3 rows p i (parameters z R B N)) (rowDenominator R N r) := by
  let k := succ (N+i)
  let K := N+r
  have hK : Γ ⊢[PRAAx] le k K :=
    le_congr ((add_comm (succ i) N).eqTrans (add_succ N i)) (add_comm r N) (add_le_add_right N hi)
  have mPos : Γ ⊢[PRAAx] m ≐ succ (pred m) := AnalyticNumberTheory.PNTStageStep.pos_of_one_le h.andE₂.andE₁
  have index : Γ ⊢[PRAAx] lt k m ⋎ lt m k := by
    refine .orE he ?_ ?_
    · exact .orI₁ (lt_congr (.eqRefl _) mPos.eqSymm.wk (lt_succ_of_le (le_trans hK.wk Prf.hyp0)))
    · exact .orI₂ (lt_succ_of_le (le_trans Prf.hyp0 (le_add_right N i)))
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hd := positive_product _ _ (le_succ_self one) hk
  have hs : Γ ⊢[PRAAx] le one (two*succ K) := positive_product _ _ (le_succ_self one) (zero_lt_succ _)
  have hd' : Γ ⊢[PRAAx] le (two*k) (two*succ K) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two (le_trans hK (le_succ_self K)))
  have order : Γ ⊢[PRAAx] le (denominator R (two*k) k) (rowDenominator R N r) :=
    mul_le_mul_right (two*sampleBound (GaussianBarnesCanonicalFactor.exponentRadius R))
      (le_trans (pw_le_pw k hd') (GaussianFactorBudget.power_monotone_length _ _ _ hs hK))
  have native := factor_lower p z R B k (.andI h.andE₁ (.andI hk h.andE₂.andE₂))
    (off_index_margin z B m k hn index) hp
  exact lower_congr (factor_at p i z R B N).eqSymm (.eqRefl _)
    (weaken_margin _ _ _ (denominator_positive R (two*k) k hd) order native)

theorem range_sample_lower (p z R B m N r : PTm n) (h : Γ ⊢[PRAAx] factorSource z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) (he : Γ ⊢[PRAAx] avoids m N r)
    (hp : Γ ⊢[PRAAx] le (minimumClock R) p) :
    Γ ⊢[PRAAx] lower (ap2 GaussianBarnesCanonicalHead.nameF p (GaussianBarnesCanonicalHead.data z R B N r))
      (GaussianNamedFiniteProductApartness.denominator (rowDenominator R N r) r) := by
  let D := rowDenominator R N r
  let x := parameters z R B N
  let s := GaussianNamedFiniteProductName.clock r (GaussianNamedFiniteProductFamily.radius F body r x) one p
  have hD : Γ ⊢[PRAAx] le one D := denominator_positive _ _ _
    (positive_product _ _ (le_succ_self one) (zero_lt_succ _))
  have hclock : Γ ⊢[PRAAx] le (minimumClock R) s := le_trans hp (le_add_right _ _)
  have low : Γ ⊢[PRAAx] rowLowerAt rows s r D x := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
    have h' : Δ ⊢[PRAAx] factorSource (sh z) (sh R) (sh B) (sh m) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have hn' : Δ ⊢[PRAAx] neighborhood (sh z) (sh B) (sh m) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hn.shift.wk
    have he' : Δ ⊢[PRAAx] avoids (sh m) (sh N) (sh r) := by simpa [Fm.shift,Syn.shift,sh,Δ] using he.shift.wk
    have hp' : Δ ⊢[PRAAx] le (minimumClock (sh R)) (sh s) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hclock.shift.wk
    simpa only [Syn.shift,sh,Δ,x,D,subst_rowDenominator,GaussianBarnesCanonicalHead.subst_parameters] using
      range_row_lower (sh s) (sh z) (sh R) (sh B) (sh m) (sh N) (sh r) (var 0) h' hn' he' Prf.hyp0 hp'
  exact lower_congr (GaussianBarnesCanonicalHead.sample_at p z R B N r).eqSymm (.eqRefl _)
    (sample_lower rows s r D x hD low)

theorem range_apart (z R B m N r : PTm n) (h : Γ ⊢[PRAAx] factorSource z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) (he : Γ ⊢[PRAAx] avoids m N r) :
    Γ ⊢[PRAAx] apart GaussianBarnesCanonicalHead.nameF (rangeHeight R N r) (GaussianBarnesCanonicalHead.data z R B N r) := by
  let D := rowDenominator R N r
  let H := rangeHeight R N r
  let p := anchor H
  have hD : Γ ⊢[PRAAx] le one D := denominator_positive _ _ _
    (positive_product _ _ (le_succ_self one) (zero_lt_succ _))
  have hp : Γ ⊢[PRAAx] le (minimumClock R) p := le_trans (le_add_right _ _) (le_add_right _ _)
  have pay : Γ ⊢[PRAAx] le (GaussianNamedFiniteProductApartness.denominator D r) (unit H) :=
    le_trans (clock_budget r D) (GaussianBalancedRadiusArithmetic.unit_monotone (apartClock r D) H (le_add_left _ _))
  exact weaken_margin _ _ _ (GaussianNamedFiniteProductApartness.denominator_positive D r hD) pay
    (range_sample_lower p z R B m N r h hn he hp)

theorem original_apart (z R B m r : PTm n) (h : Γ ⊢[PRAAx] factorSource z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) : Γ ⊢[PRAAx] apart nameF (height R m r) (data z R B m r) := by
  let G := GaussianBarnesCanonicalHead.nameF
  let x := GaussianBarnesCanonicalHead.data z R B zero (pred m)
  let y := GaussianBarnesCanonicalHead.data z R B m r
  have hs : Γ ⊢[PRAAx] headSource z R B := .andI h.andE₁ h.andE₂.andE₂
  exact GaussianNamedProductApartness.original_apart G G x y _ _
    (GaussianBarnesCanonicalHead.regular z R B zero (pred m) hs) (GaussianBarnesCanonicalHead.regular z R B m r hs)
    (range_apart z R B m zero (pred m) h hn (.orI₁ (le_congr (zero_add _).eqSymm (.eqRefl _) (le_refl _))))
    (range_apart z R B m m r h hn (.orI₂ (le_refl _)))

theorem actual_Barnes_skipped_head_uniform_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let m := var 3
     let r := var 4
     (factorSource z R B m ⋏ neighborhood z B m) ⟶ apart nameF (height R m r) (data z R B m r)) :=
  closeUniv 5 (.impI (original_apart _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedHeadUniform
