import IPRADerivations.Analysis.GaussianGammaLocalPoleFormula
import IPRADerivations.Analysis.GaussianGammaInputProperness
import IPRADerivations.Analysis.GaussianGammaNegativeCriticalCorrection
import IPRADerivations.Analysis.GaussianStirlingGammaLogarithm

/-!
# The original Gamma function on a negative pole interval

For the encoded argument `-N-1+a/b` with `1 ≤ a < b`, the local
pole certificates hold with denominator `b` and margin numerator one.
Multiplying the original Gamma name by its literal rising product yields
the original positive Gamma name at `1+a/b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (bounded normSq normSq_scale scale)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaLocalPoleGuards (center terminal localMargin)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaPoleMultiplier (multiplier actual_pole_multiplier_inverse)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular source)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianRationalHorner (qmul)
open GaussianRationalReciprocal (qone subst_qone)
open GaussianRootAlgebra (equal equal_of_values equal_trans re_add im_add re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (a b N : PTm n) : PTm n := center (arg a) b (succ N)
def product (a b N : PTm n) : PTm n := risingProduct (argument a b N) b (succ (succ N))
def data (a b N : PTm n) : PTm n := gammaData (argument a b N) (succ (succ N)) b b
def productF : PR 2 := multiplyF constantF gammaF
def productData (a b N : PTm n) : PTm n := multiplyData constantF gammaF (product a b N) (data a b N)

private theorem denominator_positive {a b : PTm n} (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx] le one b :=
  le_trans h.andE₁ (le_of_lt h.andE₂)

theorem local_margin (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx] localMargin (arg a) b one a b := by
  have ha := h.andE₁
  have hn : Γ ⊢[PRAAx] normSq (arg a) ≐ a*a := GaussianGammaGaussReference.scaled_one_norm a
  have hs : Γ ⊢[PRAAx] normSq (scale b (arg a)) ≐ (a*b)*(a*b) :=
    (normSq_scale b (arg a)).eqTrans ((congrMul (.eqRefl _) hn).eqTrans (by ipra_ring))
  have upper : Γ ⊢[PRAAx] bounded (scale b (arg a)) (a*b) :=
    le_congr hs.eqSymm (.eqRefl _) (le_refl _)
  have lower : Γ ⊢[PRAAx] le ((one*b)*(one*b)) (b*b*normSq (arg a)) :=
    le_congr (by ipra_ring) (congrMul (.eqRefl _) hn.eqSymm)
      (le_mul_mono (le_refl (b*b)) (le_mul_mono ha ha))
  exact .andI (le_congr (by ipra_ring) (.eqRefl _) (le_congr (succ_eq_add_one a) (.eqRefl _) h.andE₂))
    (.andI upper lower)

theorem negative_source (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    source (argument a b N) (succ (succ N)) b one b :=
  GaussianGammaLocalPoleGuards.center_Gamma_domain (arg a) b one a b (succ N)
    (denominator_positive h) (le_refl _) (denominator_positive h) (local_margin a b h)

theorem negative_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN gammaF (data a b N) :=
  gamma_regular _ _ _ _ _ (negative_source a b N h)

theorem terminal_argument (a b N : PTm n) : Γ ⊢[PRAAx]
    equal (terminal (arg a) b (succ N)) (arg (b+a)) := by
  apply equal_trans (GaussianGammaLocalPoleGuards.terminal_native (arg a) b (succ N))
  apply equal_of_values <;>
    simp only [GaussianGammaEulerHeadLower.translated,arg,re_add,im_add,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

private theorem constant_one (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,subst_qone] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) qone).eqTrans (one_at (var 0) (Syn.shift x)).eqSymm

theorem original_product (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    crossEquivalent productF gammaF (productData a b N) (GaussianStirlingGammaLogarithm.gammaData (b+a) b) := by
  let h₀ := arg a
  let j := succ N
  let c := product a b N
  let e := multiplier h₀ b j
  let v := gammaData (terminal h₀ b j) two b b
  let M := GaussianGammaLocalPoleFormula.resultData h₀ b j b
  have hb := denominator_positive h
  have margin := local_margin a b h
  have hr := GaussianGammaLocalPoleGuards.terminal_Gamma_domain h₀ b one a b j hb (le_refl _) hb
    margin.andE₁ margin.andE₂.andE₁
  have hv : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN gammaF v := gamma_regular _ _ _ _ _ hr
  have continuation := GaussianGammaLocalPoleFormula.original_C24_margin h₀ b one a b j hb (le_refl _) hb margin
  have lift := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF gammaF productF c c (data a b N) M
    (constant_regular _) (constant_regular _) (negative_regular a b N h)
    (multiply_fast constantF gammaF e v (constant_regular _) hv)
    (cross_refl _ _ (constant_regular _)) continuation
  have inverse : Γ ⊢[PRAAx] qmul c e ≐ qone :=
    actual_pole_multiplier_inverse h₀ b one a b j hb (le_refl _) hb margin
  have scaleOne := GaussianGammaAdjacentCutoff.multiply_cross constantF oneF gammaF gammaF (qmul c e) v v v
    (constant_regular _) (one_fast _) hv hv
    (cross_trans _ _ _ _ _ _
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ inverse) (constant_one v))
    (cross_refl _ _ hv)
  have terminalEq := terminal_argument (Γ := Γ) a b N
  have terminalCross := GaussianGammaInputProperness.original_Gamma_proper _ _ two b one b hr terminalEq
  have terminalSource := GaussianGammaInputProperness.gamma_source_equal _ _ two b one b hr terminalEq
  have positiveSource := GaussianStirlingGammaLogarithm.gamma_source (b+a) b
    (.andI (le_trans hb (le_add_right b a)) hb)
  have radiusCross := GaussianGammaRadiusOverlap.original_Gamma_overlap _ two (b+a) b one b one b
    terminalSource positiveSource
  exact cross_trans _ _ _ _ _ _ lift
    (cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.merge_head gammaF c e v hv)
      (cross_trans _ _ _ _ _ _ scaleOne
        (cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_one_left _ _ hv)
          (cross_trans _ _ _ _ _ _ terminalCross radiusCross))))

theorem actual_original_negative_interval_Gamma_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶
        crossEquivalent productF gammaF (productData (var 0) (var 1) (var 2))
          (GaussianStirlingGammaLogarithm.gammaData (var 1+var 0) (var 1))) :=
  closeUniv 3 (.impI (original_product _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNative
