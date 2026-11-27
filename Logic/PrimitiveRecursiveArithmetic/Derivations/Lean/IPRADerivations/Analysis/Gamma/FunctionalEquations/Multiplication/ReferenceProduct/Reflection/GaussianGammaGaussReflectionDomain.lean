import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReference
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionProduct
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap

/-!
# The original reflection domain for the positive Gauss reference rows

For `1 ≤ r < m` the original negative input `-r/m` stays at least
`1/m` from every relevant pole. Its original translated numerator
represents `(m-r)/m`. Native properness and radius overlap return the
translated Gamma name to the exact reference encoding.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionDomain

open_ipra
open ComplexLogarithmRemainder (scale normSq normSq_neg oneCode)
open GaussianGammaGaussReference (scaled_one_norm reference_source reference_pole_at)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianGammaReflectionProduct (complementarySource complementaryData gammaPairF)
open GaussianGammaInputProperness (pole_guard_equal gamma_source_equal original_Gamma_proper)
open GaussianGammaRadiusOverlap (original_Gamma_overlap)
open GaussianRootAlgebra (equal equal_of_values equal_symm normSq_equal re_add im_add re_neg im_neg re_scale im_scale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl)
open GaussianGammaAdjacentCutoff (multiply_cross)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "gneg" => ComplexLogarithmRemainder.neg

def source (r m : PTm n) : Fm PTm n := le one r ⋏ lt r m
def argument (r : PTm n) : PTm n := scale r oneCode
def complement (r m : PTm n) : PTm n := monus m r
def referenceData (r m : PTm n) : PTm n := gammaData (argument r) one m m
def pairData (r m : PTm n) : PTm n :=
  multiplyData gammaF gammaF (referenceData r m) (referenceData (complement r m) m)

ipra_subst source [one]
ipra_subst argument [oneCode]
ipra_subst complement
ipra_subst referenceData [gammaData, GaussianGammaReciprocalInverse.gammaHeight, one]
ipra_subst pairData

theorem modulus_positive (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) : Γ ⊢[PRAAx] le one m :=
  le_trans h.andE₁ (le_of_lt h.andE₂)

theorem complement_positive (r m : PTm n) (h : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] le one (complement r m) :=
  le_of_add_le_add_right (le_congr ((succ_eq_add_one r).eqTrans (add_comm _ _))
    ((eq_add_of_le (le_of_lt h)).eqTrans (add_comm _ _)) h)

theorem complement_le (r m : PTm n) : Γ ⊢[PRAAx] le (complement r m) m :=
  GaussianMonicResidualRadius.monus_le_left m r

theorem reference_at (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (argument r) one m one m :=
  reference_source r m h.andE₁ (le_of_lt h.andE₂)

theorem complementary_reference_at (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (argument (complement r m)) one m one m :=
  reference_source (complement r m) m (complement_positive r m h.andE₂) (complement_le r m)

private theorem norm_to_guard (z m j : PTm n) (h : Γ ⊢[PRAAx] le one (normSq (translated z m j))) :
    Γ ⊢[PRAAx] poleAt z m one m j :=
  le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (m*m)) h)

private theorem translated_difference (r m j k : PTm n) (h : Γ ⊢[PRAAx] m*j ≐ r+k) :
    Γ ⊢[PRAAx] equal (translated (gneg (argument r)) m j) (argument k) := by
  have q := natEq h
  simp only [IPRA.Q.mk_mul,IPRA.Q.mk_add,map_mul,map_add] at q
  apply equal_of_values
  · simp only [translated,argument,re_add,re_neg,re_scale,GaussianRootAlgebra.re_one,IPRA.Q.mk_mul,map_mul]
    linear_combination q
  · simp [translated,argument,im_add,im_neg,im_scale,GaussianRootAlgebra.im_one]

theorem negative_pole_at (r m j : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] poleAt (gneg (argument r)) m one m j := by
  refine .orE (lt_or_le zero j) ?_ ?_
  · let Δ := lt zero j :: Γ
    have hj : Δ ⊢[PRAAx] le one j := Prf.hyp0
    have grow : Δ ⊢[PRAAx] le m (m*j) :=
      le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl m) hj)
    have hr : Δ ⊢[PRAAx] lt r (m*j) := lt_of_lt_of_le h.andE₂.wk grow
    let k := complement r (m*j)
    have pol := translated_difference r m j k (eq_add_of_le (le_of_lt hr))
    have q := (normSq_equal pol).eqTrans (scaled_one_norm k)
    have hk := complement_positive r (m*j) hr
    exact norm_to_guard _ _ _ (le_congr (by ipra_ring) q.eqSymm (le_mul_mono hk hk))
  · let Δ := le j zero :: Γ
    have hj : Δ ⊢[PRAAx] j ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
    have e : Δ ⊢[PRAAx] equal (translated (gneg (argument r)) m j) (gneg (argument r)) := by
      apply equal_of_values
      · simp only [translated,re_add,re_scale,GaussianRootAlgebra.re_one,IPRA.Q.mk_mul,map_mul]
        rw [natEq hj]
        ipra_simps
        ring
      · simp [translated,im_add,im_scale,GaussianRootAlgebra.im_one]
    have q := (normSq_equal e).eqTrans ((normSq_neg (argument r)).eqTrans (scaled_one_norm r))
    exact norm_to_guard _ _ _ (le_congr (by ipra_ring) q.eqSymm (le_mul_mono h.andE₁.wk h.andE₁.wk))

theorem negative_source (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (gneg (argument r)) one m one m := by
  have hM := modulus_positive r m h
  have hs := (reference_at r m h).andE₁
  have radius : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (gneg (argument r)) (one*m) :=
    le_congr (normSq_neg (argument r)).eqSymm (.eqRefl _) hs.andE₂.andE₂
  refine .andI (.andI (le_refl one) (.andI hM radius)) (.andI (le_refl one) (.andI hM (.allI (.impI ?_))))
  let P := Syn.shift r
  let M := Syn.shift m
  let Δ := le (var 0) (two*one) :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source P M := by simpa [Fm.shift,Syn.shift,Δ,P,M] using h.shift.wk
  simpa [poleGuard,Δ,Syn.shift,P,M] using negative_pole_at P M (var 0) h'

theorem shifted_arg (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] equal (shifted (gneg (argument r)) m) (argument (complement r m)) :=
  translated_difference r m one _ ((by ipra_ring : Γ ⊢[PRAAx] m*one ≐ m).eqTrans (eq_add_of_le (le_of_lt h.andE₂)))

private theorem complement_guard (r m N : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] poleGuard (argument (complement r m)) m one m N := by
  refine .allI (.impI ?_)
  have hp := complement_positive r m h.andE₂
  let R := Syn.shift r
  let M := Syn.shift m
  let Δ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] le one (complement R M) := by simpa [Fm.shift,Syn.shift,Δ,R,M,one] using hp.shift.wk
  simpa [poleGuard,argument,Δ,Syn.shift,R,M,one] using (reference_pole_at (complement R M) M (var 0) hs)

theorem reflection_source (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] complementarySource (argument r) one m one m one m :=
  .andI (reference_at r m h) (.andI (negative_source r m h)
    (.andI (le_refl one) (.andI (modulus_positive r m h)
      (pole_guard_equal _ _ _ _ _ _ (complement_guard r m _ h) (equal_symm (shifted_arg r m h))))))

theorem reference_regular (r m : PTm n) (h : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] pointCN gammaF (referenceData r m) :=
  gamma_regular _ _ _ _ _ (reference_source r m h hm)

theorem pair_regular (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] pointCN gammaPairF (pairData r m) :=
  multiply_fast _ _ _ _ (gamma_regular _ _ _ _ _ (reference_at r m h))
    (gamma_regular _ _ _ _ _ (complementary_reference_at r m h))

theorem shifted_gamma_cross (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF
      (gammaData (shifted (gneg (argument r)) m) (one+one) m m) (referenceData (complement r m) m) := by
  let z := shifted (gneg (argument r)) m
  let d := argument (complement r m)
  have hs : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z (one+one) m one m :=
    GaussianGammaShift.shifted_source _ _ _ _ _ _ _ (reflection_source r m h).andE₂
  have eq := shifted_arg r m h
  exact cross_trans _ _ _ _ _ _ (original_Gamma_proper z d (one+one) m one m hs eq)
    (original_Gamma_overlap d (one+one) one m one m one m (gamma_source_equal z d (one+one) m one m hs eq)
      (complementary_reference_at r m h))

theorem gamma_pair_cross (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent gammaPairF gammaPairF
      (complementaryData (argument r) one m m m) (pairData r m) := by
  have hr := gamma_regular _ _ _ _ _ (reference_at r m h)
  have hs := GaussianGammaShift.shifted_source _ _ _ _ _ _ _ (reflection_source r m h).andE₂
  have ht := gamma_regular _ _ _ _ _ (complementary_reference_at r m h)
  exact multiply_cross gammaF gammaF gammaF gammaF (referenceData r m) (referenceData r m) _ _
    hr hr (gamma_regular _ _ _ _ _ hs) ht (cross_refl _ _ hr) (shifted_gamma_cross r m h)

theorem actual_Gauss_complementary_reflection_domain_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 1) (var 0) ⟶ complementarySource (argument (var 1)) one (var 0) one (var 0) one (var 0)) :=
  closeUniv 2 (.impI (reflection_source _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionDomain
