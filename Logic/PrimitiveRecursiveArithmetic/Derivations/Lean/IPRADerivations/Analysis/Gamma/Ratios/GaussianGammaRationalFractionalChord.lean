import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeStrictLogConvexity
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsStrictOrder
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaStrongLogConvexityAlgebra
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartTimeOrder

/-!
# The strict log-Gamma chord for a fractional step

For positive natural weights `r+s=b`, the weighted center between
`a/b` and `(a+b)/b` is `(a+r)/b`. The logarithmic recurrence
replaces the right endpoint by the original logarithm of `a/b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalFractionalChord

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogConvexity (center_positive center_denominator_positive)
open GaussianGammaNativeStrictLogConvexity (strict_order)
open GaussianGammaStrongLogConvexityAlgebra (swap_first weighted_recurrence)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical positive_product qadd qadd_canonical
  qadd_represents represents_congr)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRootAlgebra (equal_of_values re_add im_add re_scale im_scale re_one im_one)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_rescale_from scale_cross scaled_regular)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular source_shift)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "C" => constantF
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev gammaF : PR 2 := productF logGammaF
abbrev harmonicF : PR 2 := productF H
def gammaData (w a b : PTm n) : PTm n := productData logGammaF w (logGammaData a b)
def harmonicData (w a b : PTm n) : PTm n := productData H w (GaussianHarmonicLogarithmName.data a b)

theorem harmonic_regular (w a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN harmonicF (harmonicData w a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianHarmonicLogarithmName.name_regular a b hs)

theorem natural_point_sum (r s w : PTm n) (e : Γ ⊢[PRAAx] r+s ≐ w) :
    Γ ⊢[PRAAx] qadd (naturalPoint r) (naturalPoint s) ≐ naturalPoint w := by
  apply canonical_unique _ _ (scale w oneCode) one (qadd_canonical _ _) (ofGaussian_canonical _ _ (le_refl _))
    (le_refl _) _ (natural_point_represents _)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (qadd_represents _ _ _ _ _ (le_refl _) (natural_point_represents r) (natural_point_represents s))
  have ei := natEq e
  apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale,re_one,im_one] <;> ipra_simps
  · linear_combination ei
  · ring

theorem scale_sum (f : PR 2) (r s w x : PTm n) (e : Γ ⊢[PRAAx] r+s ≐ w) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (addF (productF f) (productF f)) (productF f)
      (addData (productData f r x) (productData f s x)) (productData f w x) := by
  let R := naturalPoint r
  let S := naturalPoint s
  let W := naturalPoint w
  have hr := constant_regular (Γ := Γ) R
  have hs := constant_regular (Γ := Γ) S
  have hw := constant_regular (Γ := Γ) W
  have hsum := constant_sum R S W (natural_point_sum r s w e)
  have affine := GaussianNameRingLaws.right_distributive C C f R S x hr hs hf
  have eq := GaussianGammaAdjacentCutoff.multiply_cross (addF C C) C f f (addData R S) W x x
    (add_fast _ _ _ _ hr hs) hw hf hf hsum (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ affine) eq

theorem chord (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder gammaF (addF harmonicF gammaF)
      (gammaData b (a+r) b) (addData (harmonicData r a b) (gammaData b a b)) := by
  let p := pred s
  let q := pred r
  let W := weight p (succ q)
  let A := a+b
  let t := barycenter a A p (succ q)
  let j := a+r
  let X := logGammaData a b
  let Y := logGammaData A b
  let Z := logGammaData t (W*b)
  let X' := gammaData s a b
  let Y' := gammaData r A b
  have hBase : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hShift := source_shift a b hBase
  have hj : Γ ⊢[PRAAx] le one j := le_trans ha (le_add_right _ _)
  have ltA : Γ ⊢[PRAAx] lt a A := by
    unfold lt A
    ipra_le sl hb
  have er : Γ ⊢[PRAAx] succ q ≐ r := (pos_of_one_le hr).eqSymm
  have es : Γ ⊢[PRAAx] succ p ≐ s := (pos_of_one_le hs).eqSymm
  have eW : Γ ⊢[PRAAx] W ≐ b := by
    have x := natEq er
    have y := natEq es
    have e := natEq he
    dsimp [W,weight]
    apply deriveNat
    ipra_simps
    linear_combination x+y-e
  have eT : Γ ⊢[PRAAx] t ≐ b*j := by
    have x := natEq er
    have y := natEq es
    have e := natEq he
    dsimp [t,A,j,barycenter]
    apply deriveNat
    ipra_simps
    linear_combination (𝔞 a+𝔞 b)*x+𝔞 a*y-𝔞 a*e
  have ez := gamma_rescale_from t (W*b) j b b (.andI hj hb) hb eT (congrMul eW (.eqRefl _))
  have hx := log_gamma_regular a b hBase
  have hy := log_gamma_regular A b hShift
  have hz := log_gamma_regular t (W*b) (.andI (center_positive a A p (succ q) ha)
    (center_denominator_positive b p (succ q) hb))
  have hj' := log_gamma_regular j b (.andI hj hb)
  have lhs := cross_symm _ _ _ _ (scale_cross W b Z (logGammaData j b) eW hz hj' ez)
  have first := add_cross gammaF gammaF gammaF gammaF (productData logGammaF (succ p) X) X'
    (productData logGammaF (succ q) Y) Y' (scaled_regular _ _ hx) (scaled_regular _ _ hx)
    (scaled_regular _ _ hy) (scaled_regular _ _ hy)
    (scale_cross _ _ _ _ es hx hx (cross_refl _ _ hx)) (scale_cross _ _ _ _ er hy hy (cross_refl _ _ hy))
  have recurrence := weighted_recurrence a b r hBase
  let V := harmonicData r a b
  let U := gammaData r a b
  have hU := scaled_regular r X hx
  have hV := harmonic_regular r a b hBase
  have hX := scaled_regular s X hx
  have second := add_cross gammaF gammaF gammaF (addF harmonicF gammaF) X' X' Y' (addData V U)
    hX hX (scaled_regular r Y hy) (add_fast _ _ _ _ hV hU) (cross_refl _ _ hX) recurrence
  have third := swap_first gammaF harmonicF gammaF X' V U hX hV hU
  have hw := scaled_regular b X hx
  have eSum : Γ ⊢[PRAAx] s+r ≐ b := (add_comm s r).eqTrans he.eqSymm
  have fourth := add_cross harmonicF harmonicF (addF gammaF gammaF) gammaF V V (addData X' U) (gammaData b a b)
    hV hV (add_fast _ _ _ _ hX hU) hw (cross_refl _ _ hV) (scale_sum logGammaF s r b X eSum hx)
  exact strict_transport _ _ _ _ _ _ _ _ lhs
    (cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second (cross_trans _ _ _ _ _ _ third fourth)))
    (strict_order a A b p q ha hb ltA)

theorem complementary_chord (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder gammaF (addF harmonicF gammaF)
      (gammaData b (a+b) b) (addData (harmonicData s (a+r) b) (gammaData b (a+r) b)) := by
  let j := a+r
  have hj : Γ ⊢[PRAAx] le one j := le_trans ha (le_add_right _ _)
  have he' := he.eqTrans (add_comm r s)
  have e := (congrAdd (.eqRefl a) he).eqTrans (by dsimp [j]; ipra_ring : Γ ⊢[PRAAx] a+(r+s) ≐ j+s)
  have base := log_gamma_regular (a+b) b (.andI (le_trans ha (le_add_right _ _)) hb)
  have target := log_gamma_regular (j+s) b (.andI (le_trans hj (le_add_right _ _)) hb)
  have comp := GaussianGammaCompactCutoffAlignment.cross_data_congr logGammaF logGammaF _ _ _ _
    (.eqRefl (logGammaData (a+b) b)) (GaussianStirlingGammaFractionalIncrementConvexity.gamma_data_congr _ _ _ _ e (.eqRefl _))
    (cross_refl _ _ base)
  exact strict_transport _ _ _ _ _ _ _ _
    (scale_cross b b (logGammaData (a+b) b) (logGammaData (j+s) b) (.eqRefl _) base target comp)
    (cross_refl _ _ (add_fast _ _ _ _ (harmonic_regular s j b (.andI hj hb))
      (scaled_regular b (logGammaData j b) (log_gamma_regular j b (.andI hj hb)))))
    (chord j b s r hj hb hs hr he')

end LeanProofs.IPRA.Analysis.GaussianGammaRationalFractionalChord
