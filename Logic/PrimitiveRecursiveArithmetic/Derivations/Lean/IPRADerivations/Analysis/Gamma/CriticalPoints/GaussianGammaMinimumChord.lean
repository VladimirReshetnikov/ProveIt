import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNativeStrongLogConvexity
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsLog

/-!
# A strong Gamma chord with one small weight

For positive rational endpoints with a common denominator, give the
base weight W−1 and the target weight 1. The original strong log-Gamma
chord retains a fixed squared-separation margin for every W≥2, whichever
endpoint comes first.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumChord

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (fraction_congr)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffSplit (add_data_congr)
open GaussianGammaEulerRationalHeadConvexity (barycenter weight)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaNativeLogConvexityCore (nativeCenterData nativeWeightedData)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianHarmonicWeightedQuadratic (gapNumerator squareDen)
open GaussianHarmonicWeightedQuadraticValue (gapCode comparison_denominator_positive)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_data_congr pred_positive scaled_regular)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open RationalArgmin (rationalLE rationalLE_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "C" => constantF
local notation "G" => logGammaF
local notation "lg" => logGammaData

abbrev scaledF : PR 2 := productF G

def centerNumerator (a c W : PTm n) : PTm n := pred W*a+c

def centerDenominator (b W : PTm n) : PTm n := W*b

def absDelta (a c : PTm n) : PTm n := monus c a+monus a c

def margin (a c b M : PTm n) : PTm n :=
  fraction (absDelta a c*absDelta a c) (num 4*(M*b)*(M*b))

def centerData (a c b W : PTm n) : PTm n := lg (centerNumerator a c W) (centerDenominator b W)

def lowerData (a c b M W : PTm n) : PTm n := addData (margin a c b M) (productData G W (centerData a c b W))

def weightedData (a c b W : PTm n) : PTm n := addData (productData G (pred W) (lg a b)) (lg c b)

@[simp] theorem subst_centerNumerator {m : ℕ} (σ : Fin n → PTm m) (a c W : PTm n) :
    Syn.subst σ (centerNumerator a c W) = centerNumerator (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ W) := by
  simp [centerNumerator]
@[simp] theorem subst_centerDenominator {m : ℕ} (σ : Fin n → PTm m) (b W : PTm n) :
    Syn.subst σ (centerDenominator b W) = centerDenominator (Syn.subst σ b) (Syn.subst σ W) := by
  simp [centerDenominator]
@[simp] theorem subst_absDelta {m : ℕ} (σ : Fin n → PTm m) (a c : PTm n) :
    Syn.subst σ (absDelta a c) = absDelta (Syn.subst σ a) (Syn.subst σ c) := by
  simp [absDelta]
@[simp] theorem subst_margin {m : ℕ} (σ : Fin n → PTm m) (a c b M : PTm n) :
    Syn.subst σ (margin a c b M) = margin (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ M) := by
  simp [margin]
@[simp] theorem subst_centerData {m : ℕ} (σ : Fin n → PTm m) (a c b W : PTm n) :
    Syn.subst σ (centerData a c b W) = centerData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ W) := by
  simp [centerData]
@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (a c b M W : PTm n) :
    Syn.subst σ (lowerData a c b M W) =
      lowerData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ M) (Syn.subst σ W) := by
  simp [lowerData]
@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (a c b W : PTm n) :
    Syn.subst σ (weightedData a c b W) = weightedData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ W) := by
  simp [weightedData]

theorem center_source (a c b W : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (centerNumerator a c W) (centerDenominator b W) :=
  .andI (le_trans hc (le_add_left _ _))
    (positive_product _ _ (le_trans RationalAlgebra.two_positive hW) hb)

theorem margin_symmetric (a c b M : PTm n) : Γ ⊢[PRAAx] margin a c b M ≐ margin c a b M :=
  fraction_congr _ _ _ _ (congrMul (add_comm _ _) (add_comm _ _)) (.eqRefl _)

private theorem scaled_data_congr {i j x y : PTm n} (hi : Γ ⊢[PRAAx] i ≐ j) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] productData G i x ≐ productData G j y := by
  simpa only [GaussianNaturalScaleProductName.subst_productData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (productData G (var 0) (var 1) : PTm 2) (σ := ![i,x]) (σ' := ![j,y])
      (fun k => by fin_cases k; exact hi; exact hx)

private theorem real_order_congr {F H : PR 2} {x x' y y' : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] realOrder F H x y) :
    Γ ⊢[PRAAx] realOrder F H x' y' := by
  simpa using Prf.eqSubst (realOrder F H (var 0) (var 1) : Fm PTm 2) ![x,y] ![x',y']
    (fun k => by fin_cases k; exact hx; exact hy) (by simpa using h)

private theorem scale_one_cross (x : PTm n) (hx : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN G x) :
    Γ ⊢[PRAAx] crossEquivalent scaledF G (productData G one x) x := by
  have e : Γ ⊢[PRAAx] crossEquivalent C oneF (naturalPoint one) x := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast _)
    refine .allI ?_
    simpa [Syn.shift] using ((GaussianGammaCanonicalExponent.constant_at (var 0) (naturalPoint (one : PTm (n+1)))).eqTrans
      (GaussianGammaEulerDenominator.natural_one.eqTrans (GaussianNameRingLaws.one_at (var 0) (Syn.shift x)).eqSymm))
  exact cross_trans _ _ _ _ _ _
    (GaussianGammaAdjacentCutoff.multiply_cross C oneF G G (naturalPoint one) x x x
      (constant_regular _) (one_fast _) hx hx e (cross_refl _ _ hx))
    (multiply_one_left G x hx)

private theorem gap_order (a d b M r s : PTm n) (had : Γ ⊢[PRAAx] le a d)
    (hB : Γ ⊢[PRAAx] le one (M*b)) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] rationalLE (fstT (margin a d b M)) (fstT (gapCode a d (M*b) r s)) := by
  let B := M*b
  let δ := monus d a
  let D := num 4*B*B
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ h4 hB) hB
  have balance : Γ ⊢[PRAAx] le (weight r s) (two*succ r*s) := by
    unfold weight
    ipra_le 𝔞 (succ r)*sl hs + 𝔞 s*sl (zero_lt_succ (Γ := Γ) r)
  have cleared : Γ ⊢[PRAAx] le (squareDen B r s*(δ*δ)) (gapNumerator a d r s*D) := by
    unfold squareDen gapNumerator D δ
    ipra_le (2*𝔞 B*𝔞 B*𝔞 (monus d a)*𝔞 (monus d a))*sl balance
  have read : Γ ⊢[PRAAx] absDelta a d ≐ δ := (congrAdd (.eqRefl δ) had).eqTrans (LeanProofs.IPRA.add_zero δ)
  have eg : Γ ⊢[PRAAx] margin a d b M ≐ fraction (δ*δ) D :=
    fraction_congr _ _ _ _ (congrMul read read) (.eqRefl _)
  exact rationalLE_congr (congrFst eg).eqSymm (.eqRefl _)
    (fractions_order _ _ _ _ hD (comparison_denominator_positive B r s hB) cleared)

private theorem ordered_chord (a d b M r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le d (M*b))
    (hs : Γ ⊢[PRAAx] le one s) : Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF scaledF)
      (addData (margin a d b M) (nativeCenterData a d b r s)) (nativeWeightedData a d b r s) := by
  let z := nativeCenterData a d b r s
  have ctr := log_gamma_regular (barycenter a d r s) (weight r s*b)
    (.andI (GaussianGammaEulerRationalLogConvexity.center_positive a d r s ha)
      (GaussianGammaEulerRationalLogConvexity.center_denominator_positive b r s hb))
  have bound := gap_order a d b M r s had (le_trans (le_trans ha had) hd) hs
  have left := add_order C C scaledF scaledF (margin a d b M) (gapCode a d (M*b) r s) z z
    (constant_order _ _ bound) (order_refl _ _ (scaled_regular _ _ ctr))
  exact order_trans _ _ _ _ _ _ left (GaussianGammaNativeStrongLogConvexity.strong_convexity a d b (M*b) r s ha had hb hd)

private theorem remove_target_scale (a c b W : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF scaledF scaledF) (addF scaledF G)
      (addData (productData G (pred W) (lg a b)) (productData G one (lg c b))) (weightedData a c b W) := by
  have base := scaled_regular (pred W) _ (log_gamma_regular a b (.andI ha hb))
  have target := log_gamma_regular c b (.andI hc hb)
  exact add_cross _ _ _ _ _ _ _ _ base base (scaled_regular one _ target) target
    (cross_refl _ _ base) (scale_one_cross _ target)

private theorem forward (a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hac : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le c (M*b)) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF G) (lowerData a c b M W) (weightedData a c b W) := by
  let r := pred (pred W)
  have ep : Γ ⊢[PRAAx] succ r ≐ pred W := (AnalyticNumberTheory.BinomialThree.pos_of_one_le (pred_positive W hW)).eqSymm
  have ew : Γ ⊢[PRAAx] weight r one ≐ W :=
    (show Γ ⊢[PRAAx] weight r one ≐ succ (succ r) by unfold weight; ipra_ring).eqTrans
      ((congrSucc ep).eqTrans
        (AnalyticNumberTheory.BinomialThree.pos_of_one_le (le_trans RationalAlgebra.two_positive hW)).eqSymm)
  have em : Γ ⊢[PRAAx] barycenter a c r one ≐ centerNumerator a c W :=
    congrAdd (congrMul ep (.eqRefl _)) (one_mul _)
  have ec := scaled_data_congr ew (gamma_data_congr _ _ _ _ em (congrMul ew (.eqRefl b)))
  have eo := add_data_congr _ _ _ _ (scaled_data_congr ep (.eqRefl (lg a b))) (.eqRefl (productData G one (lg c b)))
  have order := real_order_congr (add_data_congr _ _ _ _ (.eqRefl (margin a c b M)) ec) eo
    (ordered_chord a c b M r one ha hac hb hc (le_refl one))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianNameArithmetic.add_fast _ _ _ _ (constant_regular _)
      (scaled_regular W _ (log_gamma_regular _ _ (center_source a c b W (le_trans ha hac) hb hW)))))
    (remove_target_scale a c b W ha (le_trans ha hac) hb) order

private theorem backward (a c b M W : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hca : Γ ⊢[PRAAx] le c a) (hb : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] le a (M*b)) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF G) (lowerData a c b M W) (weightedData a c b W) := by
  let s := pred W
  have ew : Γ ⊢[PRAAx] weight zero s ≐ W := (congrSucc (zero_add s)).eqTrans
    (AnalyticNumberTheory.BinomialThree.pos_of_one_le (le_trans RationalAlgebra.two_positive hW)).eqSymm
  have em : Γ ⊢[PRAAx] barycenter c a zero s ≐ centerNumerator a c W := by
    unfold barycenter centerNumerator s
    ipra_ring
  have ec := scaled_data_congr ew (gamma_data_congr _ _ _ _ em (congrMul ew (.eqRefl b)))
  have order := real_order_congr (add_data_congr _ _ _ _ (margin_symmetric c a b M) ec) (.eqRefl _)
    (ordered_chord c a b M zero s hc hca hb ha (pred_positive W hW))
  have base := scaled_regular s _ (log_gamma_regular a b (.andI (le_trans hc hca) hb))
  have target := scaled_regular one _ (log_gamma_regular c b (.andI hc hb))
  have swapped := add_commutative scaledF scaledF (productData G one (lg c b)) (productData G s (lg a b)) target base
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianNameArithmetic.add_fast _ _ _ _ (constant_regular _)
      (scaled_regular W _ (log_gamma_regular _ _ (center_source a c b W hc hb hW)))))
    (cross_trans _ _ _ _ _ _ swapped (remove_target_scale a c b W (le_trans hc hca) hc hb)) order

theorem strong_chord (a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b))
    (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF G) (lowerData a c b M W) (weightedData a c b W) := by
  exact .orE (le_total a c)
    (forward a c b M W ha.wk Prf.hyp0 hb.wk hcM.wk hW.wk)
    (backward a c b M W hc.wk Prf.hyp0 hb.wk haM.wk hW.wk)

theorem actual_rational_Gamma_minimum_strong_chord_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ le one (var 1) ⟶ le one (var 2) ⟶
      le (var 0) (var 3*var 2) ⟶ le (var 1) (var 3*var 2) ⟶ le two (var 4) ⟶
      realOrder (addF C scaledF) (addF scaledF G) (lowerData (var 0) (var 1) (var 2) (var 3) (var 4))
        (weightedData (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (.impI (strong_chord _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumChord
