import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeLogConvexity
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogRescale
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingGlobalBoundsShiftArguments

/-!
# The two neighboring-integer log-gamma convexity inequalities

The native weighted center and endpoints are rescaled to their original
log-gamma names. The upper chord uses the next integer, and the lower
chord uses the previous integer and the fractional argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementConvexity

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaNativeLogConvexityCore (nativeCenterData nativeWeightedData)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (addF addData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGlobalBoundsShiftArguments (shiftedNumerator shifted_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "G" => productF logGammaF
local notation "gd" => productData logGammaF

theorem gamma_data_congr (a b c d : PTm n) (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] logGammaData a b ≐ logGammaData c d := by
  simpa only [GaussianStirlingGammaLogarithm.subst_logGammaData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (logGammaData (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

theorem gamma_rescale_from (c d a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k)
    (ec : Γ ⊢[PRAAx] c ≐ k*a) (ed : Γ ⊢[PRAAx] d ≐ k*b) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF logGammaF (logGammaData c d) (logGammaData a b) := by
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr logGammaF logGammaF _ _ _ _
    (gamma_data_congr _ _ _ _ ec ed).eqSymm (.eqRefl _)
    (GaussianStirlingGammaLogRescale.log_gamma_rescale a b k hs hk)

theorem scaled_regular (k x : PTm n) (hx : Γ ⊢[PRAAx] pointCN logGammaF x) : Γ ⊢[PRAAx] pointCN G (gd k x) :=
  multiply_fast _ _ _ _ (constant_regular _) hx

theorem scale_cross (i j x y : PTm n) (eq : Γ ⊢[PRAAx] i ≐ j)
    (hx : Γ ⊢[PRAAx] pointCN logGammaF x) (hy : Γ ⊢[PRAAx] pointCN logGammaF y)
    (hxy : Γ ⊢[PRAAx] crossEquivalent logGammaF logGammaF x y) :
    Γ ⊢[PRAAx] crossEquivalent G G (gd i x) (gd j y) := by
  have e : Γ ⊢[PRAAx] naturalPoint i ≐ naturalPoint j := by
    simpa only [GaussianRationalNaturalScale.subst_naturalPoint,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (naturalPoint (var 0) : PTm 1)
        (σ := ![i]) (σ' := ![j]) (fun k => by fin_cases k; exact eq)
  exact GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _
    (constant_regular _) (constant_regular _) hx hy (constant_data_cross _ _ e) hxy

theorem pred_positive (i : PTm n) (hi : Γ ⊢[PRAAx] le two i) : Γ ⊢[PRAAx] le one (pred i) := by
  have j : Γ ⊢[PRAAx] le one i := le_trans RationalAlgebra.two_positive hi
  have e := natEq (pos_of_one_le j)
  ipra_le sl hi using linear_combination -e

def upperScaled (i r b : PTm n) : Fm PTm n :=
  realOrder G (addF G G) (gd b (logGammaData (shiftedNumerator i r b) b))
    (addData (gd r (logGammaData (succ i) one)) (gd (monus b r) (logGammaData i one)))
def lowerScaled (i r b : PTm n) : Fm PTm n :=
  realOrder G (addF G G) (gd (r+b) (logGammaData i one))
    (addData (gd r (logGammaData (pred i) one)) (gd b (logGammaData (shiftedNumerator i r b) b)))

theorem weighted_upper (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i)
    (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] upperScaled i r b := by
  let k := pred r
  let s := monus b r
  let a := b*succ i
  let d := b*i
  let j := shiftedNumerator i r b
  let t := barycenter a d k s
  let w := weight k s
  let X := logGammaData a b
  let Y := logGammaData d b
  let Z := logGammaData t (w*b)
  let target := logGammaData j b
  have ha : Γ ⊢[PRAAx] le one a := positive_product _ _ hb (zero_lt_succ _)
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hb hi
  have hj := shifted_positive i r b hi hb
  have ht : Γ ⊢[PRAAx] le one t :=
    le_trans (positive_product _ _ (zero_lt_succ _) ha) (le_add_right _ _)
  have hwb : Γ ⊢[PRAAx] le one (w*b) := positive_product _ _ (zero_lt_succ _) hb
  have eqR : Γ ⊢[PRAAx] succ k ≐ r := (pos_of_one_le hr).eqSymm
  have eqB : Γ ⊢[PRAAx] b ≐ r+s := eq_add_of_le hrb
  have eqW : Γ ⊢[PRAAx] w ≐ b := by
    have x := natEq eqR
    have y := natEq eqB
    dsimp [w,weight]
    apply deriveNat
    ipra_simps
    linear_combination x-y
  have et : Γ ⊢[PRAAx] t ≐ b*j := by
    have x := natEq eqR
    have y := natEq eqB
    dsimp [t,barycenter,a,d,j,shiftedNumerator]
    apply deriveNat
    ipra_simps
    linear_combination (𝔞 b*(𝔞 i+1))*x-𝔞 b*𝔞 i*y
  have ez := gamma_rescale_from t (w*b) j b b (.andI hj hb) hb et (congrMul eqW (.eqRefl _))
  have ex := gamma_rescale_from a b (succ i) one b (.andI (zero_lt_succ _) (le_refl one)) hb
    (.eqRefl _) (by ipra_ring)
  have ey := gamma_rescale_from d b i one b (.andI hi (le_refl one)) hb (.eqRefl _) (by ipra_ring)
  have rx := log_gamma_regular a b (.andI ha hb)
  have ry := log_gamma_regular d b (.andI hd hb)
  have rz := log_gamma_regular t (w*b) (.andI ht hwb)
  have rb' := log_gamma_regular j b (.andI hj hb)
  have ri := log_gamma_regular i one (.andI hi (le_refl one))
  have ri' : Γ ⊢[PRAAx] pointCN logGammaF (logGammaData (succ i) one) := log_gamma_regular (succ i) one (.andI (zero_lt_succ _) (le_refl one))
  have left := scale_cross w b Z target eqW rz rb' ez
  have right := add_cross G G G G (gd (succ k) X) (gd r (logGammaData (succ i) one))
    (gd s Y) (gd s (logGammaData i one))
    (scaled_regular _ _ rx) (scaled_regular _ _ ri') (scaled_regular _ _ ry) (scaled_regular _ _ ri)
    (scale_cross _ _ _ _ eqR rx ri' ex) (scale_cross _ _ _ _ (.eqRefl _) ry ri ey)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right
    (GaussianGammaNativeLogConvexity.weighted_convexity a d b k s ha hd hb)

theorem weighted_lower (i r b : PTm n) (hi : Γ ⊢[PRAAx] le two i)
    (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] lowerScaled i r b := by
  let k := pred r
  let a := b*pred i
  let d := shiftedNumerator i r b
  let t := barycenter a d k b
  let w := weight k b
  let X := logGammaData a b
  let Y := logGammaData d b
  let Z := logGammaData t (w*b)
  have iP := pred_positive i hi
  have i' : Γ ⊢[PRAAx] le one i := le_trans RationalAlgebra.two_positive hi
  have ha : Γ ⊢[PRAAx] le one a := positive_product _ _ hb iP
  have hd : Γ ⊢[PRAAx] le one d := shifted_positive i r b i' hb
  have ht : Γ ⊢[PRAAx] le one t :=
    le_trans (positive_product _ _ (zero_lt_succ _) ha) (le_add_right _ _)
  have hwb : Γ ⊢[PRAAx] le one (w*b) := positive_product _ _ (zero_lt_succ _) hb
  have eqR : Γ ⊢[PRAAx] succ k ≐ r := (pos_of_one_le hr).eqSymm
  have eqW : Γ ⊢[PRAAx] w ≐ r+b := by
    have x := natEq eqR
    dsimp [w,weight]
    apply deriveNat
    ipra_simps
    linear_combination x
  have et : Γ ⊢[PRAAx] t ≐ (w*b)*i := by
    have x := natEq eqR
    have y := natEq eqW
    have z := natEq (pos_of_one_le i')
    dsimp only [t,barycenter,a,d,shiftedNumerator]
    apply deriveNat
    ipra_simps
    linear_combination 𝔞 b*𝔞 (pred i)*x-𝔞 b*𝔞 i*y-𝔞 b*𝔞 r*z
  have ez := gamma_rescale_from t (w*b) i one (w*b) (.andI i' (le_refl one)) hwb et (by ipra_ring)
  have ex := gamma_rescale_from a b (pred i) one b (.andI iP (le_refl one)) hb (.eqRefl _) (by ipra_ring)
  have rx := log_gamma_regular a b (.andI ha hb)
  have ry := log_gamma_regular d b (.andI hd hb)
  have rz := log_gamma_regular t (w*b) (.andI ht hwb)
  have ri := log_gamma_regular i one (.andI i' (le_refl one))
  have rp := log_gamma_regular (pred i) one (.andI iP (le_refl one))
  have left := scale_cross w (r+b) Z (logGammaData i one) eqW rz ri ez
  have right := add_cross G G G G (gd (succ k) X) (gd r (logGammaData (pred i) one)) (gd b Y) (gd b Y)
    (scaled_regular _ _ rx) (scaled_regular _ _ rp) (scaled_regular _ _ ry) (scaled_regular _ _ ry)
    (scale_cross _ _ _ _ eqR rx rp ex) (cross_refl _ _ (scaled_regular _ _ ry))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right
    (GaussianGammaNativeLogConvexity.weighted_convexity a d b k b ha hd hb)

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementConvexity
