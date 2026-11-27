import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.Convexity.GaussianGammaNegativeIntervalLogStrongConvexity
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.Chords.GaussianGammaMinimumChord
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.Chords.GaussianGammaMinimumSignedStep

/-!
# The thin log-absolute chord in both orientations

The center places weight W−1 on the base and weight one on the target.
For W at least two, the retained margin is the squared rational gap
divided by sixteen. The center stays on the same negative interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogThinChord

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaCompactCutoffSplit (add_data_congr)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaMinimumChord (absDelta margin_symmetric)
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData name_regular)
open GaussianGammaNegativeIntervalLogStrongConvexity (scaledF strong_convexity)
open GaussianHarmonicWeightedQuadratic (gapNumerator squareDen)
open GaussianHarmonicWeightedQuadraticValue (gapCode comparison_denominator_positive)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast multiply_one_left add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingGammaFractionalIncrementConvexity (pred_positive)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => nameF
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev margin (a c b : PTm n) : PTm n := GaussianGammaMinimumChord.margin a c b two

def centerData (a c b N W : PTm n) : PTm n :=
  nameData (centerNumerator a c W) (centerDenominator b W) N

def lowerData (a c b N W : PTm n) : PTm n :=
  addData (margin a c b) (productData G W (centerData a c b N W))

def weightedData (a c b N W : PTm n) : PTm n :=
  addData (productData G (pred W) (nameData a b N)) (nameData c b N)

ipra_subst centerData

ipra_subst lowerData [two]

ipra_subst weightedData

theorem center_guard (a c b W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hW : Γ ⊢[PRAAx] le two W) : Γ ⊢[PRAAx] guard (centerNumerator a c W) (centerDenominator b W) := by
  let t := pred W
  refine .andI (le_trans hc.andE₁ (le_add_left _ _)) ?_
  have hw : Γ ⊢[PRAAx] W ≐ succ t :=
    GaussianOffDominantWeights.positive_succ_pred W (le_trans RationalAlgebra.two_positive hW)
  have ht : Γ ⊢[PRAAx] le (succ (t*a+c)) (succ t*b) := by
    ipra_le 𝔞 t*sl ha.andE₂+sl hc.andE₂+𝔞 t
  exact le_congr (.eqRefl _) (congrMul hw.eqSymm (.eqRefl b)) ht

private theorem scale_regular (w x : PTm n) (h : Γ ⊢[PRAAx] pointCN G x) :
    Γ ⊢[PRAAx] pointCN scaledF (productData G w x) :=
  multiply_fast C G (naturalPoint w) x (constant_regular _) h

theorem center_regular (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hW : Γ ⊢[PRAAx] le two W) : Γ ⊢[PRAAx] pointCN G (centerData a c b N W) :=
  name_regular _ _ N (center_guard a c b W ha hc hW)

private theorem log_data_congr {a a' b b' N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] nameData a b N ≐ nameData a' b' N := by
  simpa only [GaussianGammaNegativeIntervalLogAbsolute.subst_nameData,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (nameData (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a',b',N])
      (fun k => by fin_cases k; exact ha; exact hb; exact .eqRefl N)

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

private theorem scale_one_cross (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN G x) :
    Γ ⊢[PRAAx] crossEquivalent scaledF G (productData G one x) x := by
  have e : Γ ⊢[PRAAx] crossEquivalent C oneF (naturalPoint one) x :=
    GaussianNameEquivalence.cross_data_congr _ _ _ _ _ _
      (GaussianGammaEulerDenominator.natural_one (Γ := Γ)).eqSymm (.eqRefl _)
      (GaussianNameRingLaws.constant_one_cross x)
  exact cross_trans _ _ _ _ _ _
    (GaussianGammaAdjacentCutoff.multiply_cross C oneF G G (naturalPoint one) x x x
      (constant_regular _) (one_fast _) hx hx e (cross_refl _ _ hx))
    (multiply_one_left G x hx)

private theorem translated_gap (a d b : PTm n) (had : Γ ⊢[PRAAx] le a d) :
    Γ ⊢[PRAAx] monus (b+d) (b+a) ≐ monus d a := by
  have h : Γ ⊢[PRAAx] le (b+a) (b+d) :=
    add_le_add_left b had
  have e := natEq (eq_add_of_le h)
  have p := natEq (eq_add_of_le had)
  apply deriveNat
  ipra_simps
  linear_combination p-e

private theorem gap_order (a d b r s : PTm n) (had : Γ ⊢[PRAAx] le a d)
    (hb : Γ ⊢[PRAAx] le one b) (hs : Γ ⊢[PRAAx] le one s) : Γ ⊢[PRAAx]
    rationalLE (fstT (margin a d b)) (fstT (gapCode (b+a) (b+d) (two*b) r s)) := by
  let B := two*b
  let δ := monus d a
  let D := num 4*B*B
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ RationalAlgebra.two_positive hb
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ h4 hB) hB
  have balance : Γ ⊢[PRAAx] le (weight r s) (two*succ r*s) := by
    unfold weight
    ipra_le 𝔞 (succ r)*sl hs + 𝔞 s*sl (zero_lt_succ (Γ := Γ) r)
  have cleared : Γ ⊢[PRAAx] le (squareDen B r s*(δ*δ)) ((succ r*s*δ*δ)*D) := by
    unfold squareDen D δ
    ipra_le (2*𝔞 B*𝔞 B*𝔞 (monus d a)*𝔞 (monus d a))*sl balance
  have read : Γ ⊢[PRAAx] absDelta a d ≐ δ := (congrAdd (.eqRefl δ) had).eqTrans (LeanProofs.IPRA.add_zero δ)
  have eg : Γ ⊢[PRAAx] margin a d b ≐ fraction (δ*δ) D :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul read read) (.eqRefl _)
  have en : Γ ⊢[PRAAx] gapNumerator (b+a) (b+d) r s ≐ succ r*s*δ*δ :=
    congrMul (congrMul (.eqRefl _) (translated_gap a d b had)) (translated_gap a d b had)
  have er : Γ ⊢[PRAAx] gapCode (b+a) (b+d) B r s ≐ fraction (succ r*s*δ*δ) (squareDen B r s) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ en (.eqRefl _)
  exact rationalLE_congr (congrFst eg).eqSymm (congrFst er).eqSymm
    (fractions_order _ _ _ _ hD (comparison_denominator_positive B r s hB) cleared)

private theorem ordered_chord (a d b N r s : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hd : Γ ⊢[PRAAx] guard d b) (had : Γ ⊢[PRAAx] le a d) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF scaledF)
      (addData (margin a d b) (GaussianGammaNegativeIntervalLogStrongConvexity.centerData a b d N r s))
      (GaussianGammaNegativeIntervalLogStrongConvexity.weightedData a b d N r s) := by
  let z := GaussianGammaNegativeIntervalLogStrongConvexity.centerData a b d N r s
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hz := GaussianGammaNegativeIntervalProductConvexity.center_guard a b d r s ha.andE₁ hd.andE₁ ha.andE₂ hd.andE₂
  have c := name_regular (barycenter a d r s) (weight r s*b) N hz
  have left := add_order C C scaledF scaledF (margin a d b) (gapCode (b+a) (b+d) (two*b) r s) z z
    (constant_order _ _ (gap_order a d b r s had hb hs)) (order_refl _ _ (scale_regular _ _ c))
  exact GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ left (strong_convexity a b d N r s ha hd had)

private theorem remove_target_scale (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) : Γ ⊢[PRAAx] crossEquivalent (addF scaledF scaledF) (addF scaledF G)
      (addData (productData G (pred W) (nameData a b N)) (productData G one (nameData c b N)))
      (weightedData a c b N W) := by
  have base := scale_regular (pred W) _ (name_regular a b N ha)
  have target := name_regular c b N hc
  exact add_cross _ _ _ _ _ _ _ _ base base (scale_regular one _ target) target
    (cross_refl _ _ base) (scale_one_cross _ target)

private theorem forward (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hac : Γ ⊢[PRAAx] le a c) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF G) (lowerData a c b N W) (weightedData a c b N W) := by
  let r := pred (pred W)
  have ep : Γ ⊢[PRAAx] succ r ≐ pred W := (GaussianOffDominantWeights.positive_succ_pred _ (pred_positive W hW)).eqSymm
  have ew : Γ ⊢[PRAAx] weight r one ≐ W :=
    (show Γ ⊢[PRAAx] weight r one ≐ succ (succ r) by unfold weight; ipra_ring).eqTrans
      ((congrSucc ep).eqTrans ((GaussianOffDominantWeights.positive_succ_pred W
        (le_trans RationalAlgebra.two_positive hW)).eqSymm))
  have em : Γ ⊢[PRAAx] barycenter a c r one ≐ centerNumerator a c W :=
    congrAdd (congrMul ep (.eqRefl _)) (one_mul _)
  have ec := scaled_data_congr ew (log_data_congr (N := N) em (congrMul ew (.eqRefl b)))
  have eo := add_data_congr _ _ _ _ (scaled_data_congr ep (.eqRefl (nameData a b N)))
    (.eqRefl (productData G one (nameData c b N)))
  have order := real_order_congr (add_data_congr _ _ _ _ (.eqRefl (margin a c b)) ec) eo
    (ordered_chord a c b N r one ha hc hac (le_refl one))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (add_fast _ _ _ _ (constant_regular _) (scale_regular W _ (center_regular a c b N W ha hc hW))))
    (remove_target_scale a c b N W ha hc) order

private theorem backward (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hca : Γ ⊢[PRAAx] le c a) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF G) (lowerData a c b N W) (weightedData a c b N W) := by
  let s := pred W
  have ew : Γ ⊢[PRAAx] weight zero s ≐ W := (congrSucc (zero_add s)).eqTrans
    ((GaussianOffDominantWeights.positive_succ_pred W (le_trans RationalAlgebra.two_positive hW)).eqSymm)
  have em : Γ ⊢[PRAAx] barycenter c a zero s ≐ centerNumerator a c W := by
    unfold barycenter centerNumerator s
    ipra_ring
  have ec := scaled_data_congr ew (log_data_congr (N := N) em (congrMul ew (.eqRefl b)))
  have order := real_order_congr (add_data_congr _ _ _ _ (margin_symmetric c a b two) ec) (.eqRefl _)
    (ordered_chord c a b N zero s hc ha hca (pred_positive W hW))
  have base := scale_regular s _ (name_regular a b N ha)
  have target := scale_regular one _ (name_regular c b N hc)
  have swapped := add_commutative scaledF scaledF (productData G one (nameData c b N))
    (productData G s (nameData a b N)) target base
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (add_fast _ _ _ _ (constant_regular _) (scale_regular W _ (center_regular a c b N W ha hc hW))))
    (cross_trans _ _ _ _ _ _ swapped (remove_target_scale a c b N W ha hc)) order

theorem strong_chord (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF G) (lowerData a c b N W) (weightedData a c b N W) :=
  .orE (le_total a c) (forward a c b N W ha.wk hc.wk Prf.hyp0 hW.wk)
    (backward a c b N W ha.wk hc.wk Prf.hyp0 hW.wk)

theorem actual_negative_interval_log_absolute_thin_chord_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((guard (var 0) (var 2) ⋏ (guard (var 1) (var 2) ⋏ le two (var 4))) ⟶
        realOrder (addF C scaledF) (addF scaledF G) (lowerData (var 0) (var 1) (var 2) (var 3) (var 4))
          (weightedData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (strong_chord _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogThinChord
