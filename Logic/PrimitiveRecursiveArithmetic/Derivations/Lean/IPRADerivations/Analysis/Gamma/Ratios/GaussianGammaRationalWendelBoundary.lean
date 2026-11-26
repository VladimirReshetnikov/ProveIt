import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBinding

/-!
# Both endpoint equalities in the original rational Wendel names

At exponent zero or one the relative logarithm vanishes by the exact
Gamma recurrence. The actual lower comparison power and relative
quotient both have the same original name as one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelBoundary

open_ipra
open ComplexLogarithmRemainder (oneCode scale zeroCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaRationalFractionalChord (harmonicF)
open GaussianGammaRationalGautschi (powerF powerData)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular)
open GaussianGammaRationalLogGautschi (ratioExponentF ratioExponentData ratio_exponent_regular fractional_sum)
open GaussianGammaRationalLogWendel (relativeExponentF relativeExponentData relative_exponent_regular)
open GaussianGammaRationalWendelGautschi (relativeF relativeData wendel_order)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_at)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_equivalent add_negative add_zero oneF zeroF zero_fast zero_at)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedDifference (nameF data)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qmul_canonical qzero canonical_unique ofGaussian_canonical ofGaussian_represents represents_congr zero_represents)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left qzero_canonical)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_zero im_zero)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => harmonicF
local notation "G" => logGammaF
local notation "D" => ratioExponentF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

theorem difference_cross (F F' J J' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hf' : Γ ⊢[PRAAx] pointCN F' x')
    (hj : Γ ⊢[PRAAx] pointCN J y) (hj' : Γ ⊢[PRAAx] pointCN J' y')
    (hxx : Γ ⊢[PRAAx] crossEquivalent F F' x x') (hyy : Γ ⊢[PRAAx] crossEquivalent J J' y y') :
    Γ ⊢[PRAAx] crossEquivalent (nameF F J) (nameF F' J') (data x y) (data x' y') :=
  add_cross F F' (negativeF J) (negativeF J') x x' (negativeData y) (negativeData y')
    hf hf' (negative_fast _ _ hj) (negative_fast _ _ hj') hxx (negative_equivalent _ _ _ _ hj hj' (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ hyy))

theorem zero_data_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (zero_fast _)
  refine .allI ?_
  exact (zero_at _ (Syn.shift x)).eqTrans (zero_at _ (Syn.shift y)).eqSymm

theorem fraction_zero (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] fraction zero b ≐ qzero := by
  have num : Γ ⊢[PRAAx] GaussianRootAlgebra.equal zeroCode (scale (zero : PTm n) oneCode) := by
    apply equal_of_values <;>
      simp [re_scale,im_scale,re_zero,im_zero,IPRA.Q.mk_zero]
  exact (canonical_unique _ _ _ b qzero_canonical (ofGaussian_canonical _ _ hb) hb
    (represents_congr (.eqRefl _) num (.eqRefl _) (zero_represents b))
    (ofGaussian_represents _ _ hb)).eqSymm

theorem zero_product_at (f : PR 2) (p c x : PTm n) (hc : Γ ⊢[PRAAx] c ≐ qzero) :
    Γ ⊢[PRAAx] ap2 (multiplyF C f) p (multiplyData C f c x) ≐ qzero := by
  let s := GaussianFastValueCut.exponent (multiplyModulus C f c x) p
  have mid : Γ ⊢[PRAAx] ap2 (multiplyF C f) p (multiplyData C f c x) ≐ qmul (ap2 C s c) (ap2 f s x) :=
    (multiply_at C f c x p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  exact mid.eqTrans ((qmul_congr ((constant_at s c).eqTrans hc) (.eqRefl _)).eqTrans (qmul_zero_left _))

theorem fractional_zero (b a d x : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hs : Γ ⊢[PRAAx] source a d) : Γ ⊢[PRAAx] crossEquivalent L zeroF (fractionalData zero b a d) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (fractional_regular _ _ _ _ hs) (zero_fast _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  have hB : Δ ⊢[PRAAx] le one (Syn.shift b) := by simpa [Δ,Fm.shift,Syn.shift] using hb.shift
  have read := zero_product_at H (var 0) (fraction zero (Syn.shift b)) (hd (Syn.shift a) (Syn.shift d))
    (fraction_zero (Syn.shift b) hB)
  simpa [fractionalData,GaussianGammaRationalFractionalChord.harmonicF,GaussianNaturalScaleProductName.productF,Syn.shift,Δ] using read.eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm

theorem fractional_full (b a d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hs : Γ ⊢[PRAAx] source a d) : Γ ⊢[PRAAx] crossEquivalent L H (fractionalData b b a d) (hd a d) := by
  let x := fractionalData b b a d
  let y := fractionalData zero b a d
  have hx := fractional_regular b b a d hs
  have hy := fractional_regular zero b a d hs
  have change := add_cross L L L zeroF x x y x hx hx hy (zero_fast _)
    (cross_refl _ _ hx) (fractional_zero b a d x hb hs)
  have zero := cross_trans _ _ _ _ _ _ change (GaussianNameRingLaws.add_zero L x hx)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ zero)
    (fractional_sum a d b b ConciseIPRA.PTm.zero hb (add_zero b).eqSymm hs)

theorem harmonic_one (a x : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] crossEquivalent H zeroF (hd a a) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianHarmonicLogarithmName.name_regular a a (.andI ha ha)) (zero_fast _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let A := Syn.shift a
  let t : PTm (n+1) := var 0
  let Q := GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock t)
  have hA : Δ ⊢[PRAAx] le one A := by simpa [Δ,Fm.shift,Syn.shift,A] using ha.shift
  have raw := GaussianPositiveRationalLogarithmProperness.original_finite_difference A A Q hA hA
  have z := GaussianCoefficientNormOrder.qsub_self (Γ := Δ) (RationalGaussianEmbedding.embed (GammaMeshRobinLogBridge.harmonicLog A Q))
  have result := (GaussianHarmonicLogarithmName.sample_at t A A).eqTrans
    (raw.eqSymm.eqTrans (z.eqTrans (zero_at t (Syn.shift x)).eqSymm))
  simpa [GaussianHarmonicLogarithmName.sample,Syn.shift,Δ,A,t] using result

theorem ratio_zero_step (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent D H (ratioExponentData a b zero) (hd a b) := by
  let x := logGammaData a b
  let y := logGammaData (a+zero) b
  let z := logGammaData (a+b) b
  let u := hd a b
  have hs : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hx := log_gamma_regular a b hs
  have hy := log_gamma_regular (a+zero) b (.andI (le_trans ha (le_add_right _ _)) hb)
  have hz := log_gamma_regular (a+b) b (.andI (le_trans ha (le_add_right _ _)) hb)
  have hu := GaussianHarmonicLogarithmName.name_regular a b hs
  have change := GaussianGammaCompactCutoffAlignment.cross_data_congr G G x y x x
    (GaussianStirlingGammaFractionalIncrementConvexity.gamma_data_congr _ _ _ _ (add_zero a).eqSymm (.eqRefl _))
    (.eqRefl _) (cross_refl _ _ hx)
  have left := difference_cross G (addF H G) G G z (addData u x) y x hz (add_fast _ _ _ _ hu hx) hy hx
    (GaussianStirlingGammaLogShift.log_gamma_increment a b hs) change
  exact cross_trans _ _ _ _ _ _ left (GaussianNamedStrictOrderDifference.sum_sub_right H G u x hu hx)

theorem relative_zero_step (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent relativeExponentF zeroF (relativeExponentData a b zero b) (ratioExponentData a b zero) := by
  let y := ratioExponentData a b zero
  let z := hd a b
  have hs : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hz := GaussianHarmonicLogarithmName.name_regular a b hs
  have left := difference_cross L H D H (fractionalData b b a b) z y z
    (fractional_regular _ _ _ _ hs) hz (ratio_exponent_regular a b zero ha hb) hz
    (fractional_full b a b hb hs) (ratio_zero_step a b ha hb)
  exact cross_trans _ _ _ _ _ _ left
    (cross_trans _ _ _ _ _ _ (add_negative H z hz) (zero_data_cross z y))

theorem relative_full_step (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent relativeExponentF zeroF (relativeExponentData a b b zero) (ratioExponentData a b b) := by
  let x := logGammaData (a+b) b
  let y := ratioExponentData a b b
  have hx := log_gamma_regular (a+b) b (.andI (le_trans ha (le_add_right _ _)) hb)
  have left := difference_cross L zeroF D zeroF (fractionalData zero b a b) y y y
    (fractional_regular _ _ _ _ (.andI ha hb)) (zero_fast _) (ratio_exponent_regular a b b ha hb) (zero_fast _)
    (fractional_zero b a b y hb (.andI ha hb)) (cross_trans _ _ _ _ _ _ (add_negative G x hx) (zero_data_cross x y))
  exact cross_trans _ _ _ _ _ _ left (add_negative zeroF y (zero_fast _))

theorem lower_zero_step (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent L zeroF (fractionalData b b a (a+zero)) (ratioExponentData a b zero) := by
  have hD := le_trans ha (le_add_right a zero)
  have change := GaussianGammaCompactCutoffAlignment.cross_data_congr H zeroF
    (hd a a) (hd a (a+zero)) (ratioExponentData a b zero) (ratioExponentData a b zero)
    (congrPairT (.eqRefl a) (add_zero a).eqSymm) (.eqRefl _) (harmonic_one a (ratioExponentData a b zero) ha)
  exact cross_trans _ _ _ _ _ _ (fractional_full b a (a+zero) hb (.andI ha hD)) change

theorem exponential_zero_transport (F : PR 2) (x z : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN F x) (h : Γ ⊢[PRAAx] crossEquivalent F zeroF x z) :
    Γ ⊢[PRAAx] crossEquivalent (E F) oneF (ed F x) z := by
  have lift := GaussianExponentialRadiusIndependence.independent_radii_proper F zeroF (GaussianNameBounds.U F x)
    (GaussianNameBounds.U zeroF z) x z (exponential_input _ _ hF) (exponential_input _ _ (zero_fast _)) h
  exact cross_trans _ _ _ _ _ _ lift (GaussianExponentialInverse.zero_exponential_cross (GaussianNameBounds.U zeroF z) z)

def endpoint (a b r s : PTm n) : Fm PTm n :=
  crossEquivalent powerF oneF (powerData s b a (a+r)) (ratioExponentData a b r) ⋏
  crossEquivalent relativeF oneF (relativeData a b r s) (ratioExponentData a b r)

theorem at_zero (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] endpoint a b zero b :=
  .andI (exponential_zero_transport L _ _ (fractional_regular _ _ _ _ (.andI ha (le_trans ha (le_add_right _ _))))
    (lower_zero_step a b ha hb))
    (exponential_zero_transport relativeExponentF _ _ (relative_exponent_regular a b zero b ha hb) (relative_zero_step a b ha hb))

theorem at_one (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] endpoint a b b zero :=
  .andI (exponential_zero_transport L _ _ (fractional_regular _ _ _ _ (.andI ha (le_trans ha (le_add_right _ _))))
    (fractional_zero b a (a+b) (ratioExponentData a b b) hb (.andI ha (le_trans ha (le_add_right _ _)))))
    (exponential_zero_transport relativeExponentF _ _ (relative_exponent_regular a b b zero ha hb) (relative_full_step a b ha hb))

def weak (a b r s : PTm n) : Fm PTm n :=
  realOrder powerF relativeF (powerData s b a (a+r)) (relativeData a b r s) ⋏
    realOrder relativeF oneF (relativeData a b r s) (ratioExponentData a b r)

theorem weak_of_endpoint (a b r s : PTm n) (h : Γ ⊢[PRAAx] endpoint a b r s) :
    Γ ⊢[PRAAx] weak a b r s := by
  let z := ratioExponentData a b r
  have oneOrder := GaussianGammaEulerRationalLogOrder.order_refl oneF z (GaussianNameRingLaws.one_fast (Γ := Γ) z)
  exact .andI (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ h.andE₁
    (cross_symm _ _ _ _ h.andE₂) oneOrder)
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ h.andE₂
      (cross_refl _ _ (GaussianNameRingLaws.one_fast z)) oneOrder)

ipra_subst endpoint [powerData, relativeData, relativeExponentData, ratioExponentData, fractionalData, GaussianGammaFiniteApproximantName.exponentialInputData]

theorem endpoint_congr (a b r s r' s' : PTm n) (er : Γ ⊢[PRAAx] r ≐ r') (es : Γ ⊢[PRAAx] s ≐ s')
    (h : Γ ⊢[PRAAx] endpoint a b r s) : Γ ⊢[PRAAx] endpoint a b r' s' := by
  simpa using Prf.eqSubst (endpoint (var 0) (var 1) (var 2) (var 3) : Fm PTm 4) ![a,b,r,s] ![a,b,r',s']
    (fun i => by fin_cases i; exact .eqRefl a; exact .eqRefl b; exact er; exact es) (by simpa using h)

theorem weak_order (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hs : Γ ⊢[PRAAx] b ≐ r+s) : Γ ⊢[PRAAx] weak a b r s := by
  refine .orE (zero_or_succ r) ?_ ?_
  · have er : (r ≐ zero) :: Γ ⊢[PRAAx] r ≐ zero := Prf.hyp0
    have es := hs.wk.eqTrans ((congrAdd er (.eqRefl s)).eqTrans (zero_add s))
    exact weak_of_endpoint a b r s (endpoint_congr a b zero b r s er.eqSymm es (at_zero _ _ ha.wk hb.wk))
  · have hr := le_congr (.eqRefl _) (Prf.hyp0 : (r ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred r)) :: Γ ⊢[PRAAx]
      r ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred r)).eqSymm (zero_lt_succ _)
    refine .orE (zero_or_succ s) ?_ ?_
    · have es : (s ≐ zero) :: (r ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred r)) :: Γ ⊢[PRAAx] s ≐ zero := Prf.hyp0
      have er := hs.wk.wk.eqTrans ((congrAdd (.eqRefl r) es).eqTrans (add_zero r))
      exact weak_of_endpoint a b r s (endpoint_congr a b b zero r s er es.eqSymm (at_one _ _ ha.wk.wk hb.wk.wk))
    · have es : (s ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred s)) ::
          (r ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred r)) :: Γ ⊢[PRAAx]
            s ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred s) := Prf.hyp0
      have hp := le_congr (.eqRefl _) es.eqSymm (zero_lt_succ _)
      have h := wendel_order a b r s ha.wk.wk hb.wk.wk hr.wk hp hs.wk.wk
      exact .andI h.andE₁.andE₁ h.andE₂.andE₁

theorem actual_positive_rational_Wendel_boundary_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 0) ⋏ le one (var 1)) ⟶
      endpoint (var 0) (var 1) zero (var 1) ⋏ endpoint (var 0) (var 1) (var 1) zero) :=
  closeUniv 2 (.impI (.andI
    (at_zero _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂) (at_one _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_positive_rational_Wendel_weak_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 0) ⋏ (le one (var 1) ⋏ var 1 ≐ var 2+var 3)) ⟶ weak (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (weak_order _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelBoundary
