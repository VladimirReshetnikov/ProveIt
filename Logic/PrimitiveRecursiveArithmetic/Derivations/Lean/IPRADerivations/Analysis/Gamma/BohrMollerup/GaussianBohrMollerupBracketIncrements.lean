import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupSqueeze
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupDifferenceTransform
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupFiniteRecurrence
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupBlockLogBound

/-!
# The upper and lower increments for the literal Bohr–Mollerup brackets

The first chord gives x log(n-1). The general-B chord gives
(x/B) times the literal B-term logarithm sum, which is bounded above
by x log(n+B-1).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketIncrements

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianBohrMollerupBlockChord (source top complement)
open GaussianBohrMollerupChords (base translated argument_congr base_source translated_source scaled_regular scale_cross)
open GaussianBohrMollerupPresentation (Presentation argument scaledData scaledF laws observe_value)
open GaussianBohrMollerupBracketEndpoints (sumData sum_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaRationalFractionalChord (scale_sum)
open GaussianGammaStrongLogConvexityAlgebra (swap_first)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative negativeF negativeData negative_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (fractionData fractional_regular fractional_order scaled_fraction)
open GaussianNamedRealOrderTransport (transport)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "logData" => GaussianHarmonicLogarithmName.data
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "Sum" => GaussianBohrMollerupBracketEndpoints.sumF

abbrev incrementF (P : Presentation) : PR 2 := D P.nameF P.nameF
def incrementData (P : Presentation) (a b j : PTm n) : PTm n :=
  dd (argument P (translated a b j) b) (argument P (base b j) b)
abbrev averageF : PR 2 := productF Sum
def averageData (a b B j : PTm n) : PTm n :=
  fractionData Sum a (B*b) (sumData (base b j) b B)
def boundData (a b j : PTm n) : PTm n := fractionData H a b (logData j one)

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (a b j : PTm n) :
    Syn.subst σ (incrementData P a b j) = incrementData P (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [incrementData,translated,base]
@[simp] theorem subst_averageData {m : ℕ} (σ : Fin n → PTm m) (a b B j : PTm n) :
    Syn.subst σ (averageData a b B j) = averageData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [averageData,fractionData,base]
@[simp] theorem subst_boundData {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    Syn.subst σ (boundData a b j) = boundData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [boundData,fractionData,one]

theorem integer_log_rescale (b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent H H (logData (b*j) b) (logData j one) :=
  cross_data_congr H H (logData (b*j) (b*one)) (logData (b*j) b) (logData j one) (logData j one)
    (congrPairT (.eqRefl _) (by ipra_ring)) (.eqRefl _)
    (GaussianGammaStrongLogConvexityAlgebra.harmonic_rescale j one b (.andI hj (le_refl one)) hb)

theorem lower (P : Presentation) (a b j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (s : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] realOrder (productF H) (incrementF P) (boundData a b j) (incrementData P a b j) := by
  let F := P.nameF
  let x := argument P (translated a b j) b
  let y := argument P (base b j) b
  let u := logData j one
  let v := logData (b*j) b
  have hv := hp.andE₂.andE₁
  have hb := s.andE₂
  have hx := (observe_value P _ _ hv (translated_source a b j hb)).andE₁
  have hy := (observe_value P _ _ hv (base_source b j hb)).andE₁
  have hu := GaussianHarmonicLogarithmName.name_regular j one (.andI hj (le_refl one))
  have hv' := GaussianHarmonicLogarithmName.name_regular (b*j) b (.andI (positive_product _ _ hb hj) hb)
  have lhs := cross_trans _ _ _ _ _ _ (scaled_fraction H a b u hb hu)
    (scale_cross H a a u v (.eqRefl _) hu hv' (cross_symm _ _ _ _ (integer_log_rescale b j hb hj)))
  have rhs := GaussianBohrMollerupDifferenceTransform.scaled_difference F F b x y hx hy
  have raw := GaussianBohrMollerupSqueeze.lower_increment P a b j hv hp.andE₂.andE₂.andE₁
    hp.andE₂.andE₂.andE₂.andE₁ hp.andE₂.andE₂.andE₂.andE₂ s hj
  exact GaussianNamedNaturalScaleOrder.reflect_order _ _ b _ _ hb (fractional_regular H a b u hu)
    (GaussianNamedDifference.name_regular F F x y hx hy)
    (transport _ _ _ _ _ _ _ _ lhs rhs raw)

private theorem subtract_base_order (F G : PR 2) (x y z : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN F y) (hz : Γ ⊢[PRAAx] pointCN G z)
    (ord : Γ ⊢[PRAAx] realOrder F (addF F G) x (addData y z)) :
    Γ ⊢[PRAAx] realOrder (D F F) G (dd x y) z := by
  let N := negativeF F
  let w := negativeData y
  have hw := negative_fast F y hy
  have first := add_order F (addF F G) N N x (addData y z) w w ord (order_refl _ _ hw)
  have right := cross_trans _ _ _ _ _ _
    (add_commutative (addF F G) N (addData y z) w (add_fast F G y z hy hz) hw)
    (GaussianGammaStrongLogConvexityAlgebra.add_negative_front F G y z hy hz)
  exact transport _ _ _ _ _ _ _ _ (cross_refl _ _ (add_fast F N x w hx hw)) right first

private theorem collect_weighted_base (F G : PR 2) (a s V y z : PTm n)
    (eq : Γ ⊢[PRAAx] a+s ≐ V) (hy : Γ ⊢[PRAAx] pointCN F y) (hz : Γ ⊢[PRAAx] pointCN G z) :
    Γ ⊢[PRAAx] crossEquivalent (addF (addF (productF F) (productF G)) (productF F)) (addF (productF F) (productF G))
      (addData (addData (productData F a y) (productData G a z)) (productData F s y))
      (addData (productData F V y) (productData G a z)) := by
  let J := productF F
  let K := productF G
  let u := productData F a y
  let v := productData F s y
  let w := productData G a z
  have hu := scaled_regular F a y hy
  have hv := scaled_regular F s y hy
  have hw := scaled_regular G a z hz
  have first := add_associative J K J u w v hu hw hv
  have second := add_cross J J (addF K J) (addF J K) u u (addData w v) (addData v w)
    hu hu (add_fast _ _ _ _ hw hv) (add_fast _ _ _ _ hv hw) (cross_refl _ _ hu) (add_commutative K J w v hw hv)
  have third := (add_associative J J K u v w hu hv hw)
  have last := add_cross (addF J J) J K K (addData u v) (productData F V y) w w
    (add_fast _ _ _ _ hu hv) (scaled_regular _ _ _ hy) hw hw (scale_sum F a s V y eq hy) (cross_refl _ _ hw)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ third) last))

theorem upper_average (P : Presentation) (a b B j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder (incrementF P) averageF (incrementData P a b j) (averageData a b B j) := by
  let F := P.nameF
  let J := productF F
  let V := B*b
  let s := complement a b B
  let x := argument P (translated a b j) b
  let y := argument P (base b j) b
  let t := argument P (top b B j) b
  let z := sumData (base b j) b B
  let c := naturalPoint a
  let av := averageData a b B j
  have hv := hp.andE₂.andE₁
  have hb := hs.andE₁.andE₂
  have hV := positive_product _ _ hs.andE₂.andE₁ hb
  have hbase := base_source b j hb
  have hx := (observe_value P _ _ hv (translated_source a b j hb)).andE₁
  have hy := (observe_value P _ _ hv hbase).andE₁
  have ht := (observe_value P _ _ hv (GaussianBohrMollerupBlockChord.top_source b B j hb)).andE₁
  have hz := sum_regular (base b j) b B hbase
  have hc := constant_regular (Γ := Γ) c
  have base' := add_fast F Sum y z hy hz
  have stepEq : Γ ⊢[PRAAx] argument P (base b j+b*B) b ≐ t :=
    argument_congr P _ _ _ _ (by unfold top; ipra_ring) (.eqRefl _)
  have step := cross_data_congr F (addF F Sum) _ t _ _ stepEq (.eqRefl _)
    (GaussianBohrMollerupFiniteRecurrence.iterated_cross P (base b j) b B hv hp.andE₂.andE₂.andE₁ hbase)
  have lift := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF F (addF F Sum)
    c c t (addData y z) hc hc ht base' (cross_refl _ _ hc) step
  have split := cross_trans _ _ _ _ _ _ lift (GaussianNameRingLaws.distributive constantF F Sum c y z hc hy hz)
  have remain := scaled_regular F s y hy
  have spread := add_cross J (addF J (productF Sum)) J J (productData F a t)
    (addData (productData F a y) (productData Sum a z)) (productData F s y) (productData F s y)
    (scaled_regular F a t ht) (add_fast _ _ _ _ (scaled_regular F a y hy) (scaled_regular Sum a z hz))
    remain remain split (cross_refl _ _ remain)
  have collected := collect_weighted_base F Sum a s V y z (eq_add_of_le hs.andE₂.andE₂).eqSymm hy hz
  have both := cross_trans _ _ _ _ _ _ spread collected
  have hrX := scaled_regular F V x hx
  have hrY := scaled_regular F V y hy
  have hrZ := scaled_regular Sum a z hz
  have ord := transport _ _ _ _ _ _ _ _ (cross_refl _ _ hrX) both
    (GaussianBohrMollerupBlockChord.scaled_chord P a b B j hp hs)
  have cleaned := subtract_base_order J (productF Sum) (productData F V x) (productData F V y) (productData Sum a z)
    hrX hrY hrZ ord
  have scaleL := GaussianBohrMollerupDifferenceTransform.scaled_difference F F V x y hx hy
  have scaleR := scaled_fraction Sum a V z hV hz
  exact GaussianNamedNaturalScaleOrder.reflect_order _ _ V (incrementData P a b j) av hV
    (GaussianNamedDifference.name_regular F F x y hx hy) (fractional_regular Sum a V z hz)
    (transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ scaleL) (cross_symm _ _ _ _ scaleR) cleaned)

private theorem coefficient_recover (a b B : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRationalHorner.qmul (fraction a (B*b)) (naturalPoint B) ≐ fraction a b := by
  have e : Γ ⊢[PRAAx] naturalPoint B ≐ fraction B one := .eqRefl _
  have hV := positive_product _ _ hB hb
  have read := GaussianEulerDampedTimeRate.fraction_product a (B*b) B one hV (le_refl one)
  have code : Γ ⊢[PRAAx] fraction (a*B) ((B*b)*one) ≐ fraction (B*a) (B*b) :=
    GaussianGammaEulerMidpointLogHeadGap.fraction_congr (mul_comm _ _) (by ipra_ring)
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) e).eqTrans
    (read.eqTrans (code.eqTrans (GaussianCompactRiemannSplit.fraction_cancel B a b hB hb)))

theorem average_cap (a b B j : PTm n) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder averageF (productF H) (averageData a b B j) (boundData a b (j+B)) := by
  let V := B*b
  let x := sumData (base b j) b B
  let k := GaussianBohrMollerupBlockLogBound.cap (base b j) b B
  let w := logData k b
  let u := logData (j+B) one
  let f := fraction a V
  let g := fraction a b
  let c := naturalPoint B
  have hb := hs.andE₁.andE₂
  have hB := hs.andE₂.andE₁
  have hV := positive_product _ _ hB hb
  have hJ : Γ ⊢[PRAAx] le one (j+B) :=
    le_trans (zero_lt_succ j) (le_congr (succ_eq_add_one j).eqSymm (.eqRefl _) (add_le_add₂ (le_refl j) hB))
  have hX := sum_regular (base b j) b B (base_source b j hb)
  have hW := GaussianHarmonicLogarithmName.name_regular k b
    (GaussianBohrMollerupBlockLogBound.cap_source _ _ _ (base_source b j hb))
  have hU := GaussianHarmonicLogarithmName.name_regular (j+B) one (.andI hJ (le_refl one))
  have capEq : Γ ⊢[PRAAx] k ≐ b*(j+B) := by
    have e := natEq (pos_of_one_le hB)
    apply deriveNat
    unfold k GaussianBohrMollerupBlockLogBound.cap base
    ipra_simps
    linear_combination -Groth.ι (IPRA.Q.mk Γ b)*e
  have hZ := cross_data_congr H H (logData (b*(j+B)) b) w u u (congrPairT capEq.eqSymm (.eqRefl _)) (.eqRefl _)
    (integer_log_rescale b (j+B) hb hJ)
  have hC := constant_regular (Γ := Γ) c
  have hF := constant_regular (Γ := Γ) f
  have hG := constant_regular (Γ := Γ) g
  have prod := GaussianNameRingLaws.multiply_associative constantF constantF H f c w hF hC hW
  have exactConstant := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross f c)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (coefficient_recover a b B hb hB))
  have wrap := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF constantF) constantF H H
    (multiplyData constantF constantF f c) g w u (multiply_fast _ _ _ _ hF hC) hG hW hU exactConstant hZ
  have whole := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ prod) wrap
  have cap := GaussianBohrMollerupBlockLogBound.sum_order (base b j) b B (base_source b j hb) hB
  exact transport _ _ _ _ _ _ _ _ (cross_refl _ _ (fractional_regular Sum a V x hX)) whole
    (fractional_order Sum (productF H) a V x (productData H B w) hV hX (scaled_regular H B w hW) cap)

theorem upper (P : Presentation) (a b B j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder (incrementF P) (productF H) (incrementData P a b j) (boundData a b (j+B)) :=
  GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ (upper_average P a b B j hp hs) (average_cap a b B j hs)

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketIncrements
