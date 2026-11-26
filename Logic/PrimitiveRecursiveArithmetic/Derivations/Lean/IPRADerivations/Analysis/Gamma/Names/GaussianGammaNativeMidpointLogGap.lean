import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerMidpointLogGap
import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNativeLogConvexity
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrementObservations

/-!
# A uniform midpoint margin for the original positive rational log-Gamma names

The finite log-Euler names have the same explicit margin at every
cutoff. The three certified cofinal rates transfer the strengthened
order with the margin unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeMidpointLogGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerMidpointLogHeadGap (margin)
open GaussianGammaEulerRationalLogConvergence (rateCoefficient)
open GaussianGammaNativeLogConvexity (family_rate)
open GaussianGammaNativeLogConvexityCore (familyRate cutoff)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameRingLaws (add_sample_error)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNaturalScaleProductName (productF productData)
open GaussianNaturalScaleProductRate (scaled_sample_error)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGlobalBounds (small_join)
open RationalValueBounds (upper upper_mono upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianGammaEulerRationalLog.nameF
local notation "ed" => GaussianGammaEulerRationalLog.data
local notation "P" => productF E
local notation "G" => productF logGammaF
local notation "C" => constantF
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def centerData (a d b : PTm n) : PTm n :=
  addData (margin a d) (productData logGammaF two (logGammaData (a+d) (two*b)))
def weightedData (a d b : PTm n) : PTm n := addData (logGammaData a b) (logGammaData d b)

@[simp] theorem subst_centerData {m : ℕ} (σ : Fin n → PTm m) (a d b : PTm n) :
    Syn.subst σ (centerData a d b) = centerData (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) := by
  simp [centerData]
@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (a d b : PTm n) :
    Syn.subst σ (weightedData a d b) = weightedData (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) := by
  simp [weightedData]

theorem cutoff_rate (a b K A p : PTm n) (h : Γ ⊢[PRAAx] familyRate a b K A) :
    Γ ⊢[PRAAx] independentRate E logGammaF (ed (cutoff K A p) a b)
      (logGammaData a b) A (cutoff K A p) := by
  have e : Γ ⊢[PRAAx] (le K (cutoff K A p) ⟶ independentRate E logGammaF (ed (cutoff K A p) a b)
      (logGammaData a b) A (cutoff K A p)) := by simpa [familyRate] using h.allE (cutoff K A p)
  apply e.impE
  have u := mul_le_mul_right K (unit_positive (Γ := Γ) p)
  unfold cutoff
  ipra_le 𝔞 A*𝔞 (unit p)+1+sl u

theorem cutoff_cover (K A p : PTm n) : Γ ⊢[PRAAx] le (A*unit p) (cutoff K A p) := by
  unfold cutoff
  ipra_le 𝔞 K*𝔞 (unit p)+1

theorem base_sample_error (a b K A p : PTm n) (h : Γ ⊢[PRAAx] familyRate a b K A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 E p (ed (cutoff K A p) a b)) (ap2 logGammaF p (logGammaData a b))
      (num 3) (unit p) := by
  let N := cutoff K A p
  have hp := unit_positive (Γ := Γ) p
  have hn : Γ ⊢[PRAAx] le one N := zero_lt_succ _
  have rho := rate_at E logGammaF (ed N a b) (logGammaData a b) A N p p (cutoff_rate a b K A p h)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hn hp) hp) hp _ rho
  dsimp only [GaussianNamedInverseRate.rateNumerator,GaussianNamedInverseRate.rateDenominator,N]
  ipra_le 𝔞 (unit p)*𝔞 (unit p)*sl (cutoff_cover K A p)

theorem add_convergence (f g u v : PR 2) (x y s t A B p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] pointCN u s) (ht : Γ ⊢[PRAAx] pointCN v t)
    (l : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 u p s) A (unit p))
    (r : Γ ⊢[PRAAx] distanceBounded (ap2 g p y) (ap2 v p t) B (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (addF f g) p (addData x y)) (ap2 (addF u v) p (addData s t))
      (GaussianNameRingLaws.three+(A+B)+GaussianNameRingLaws.three) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have left := add_sample_error f g x y p hx hy
  have middle := sum_distance _ _ _ _ _ _ _ hp l r
  have right := distance_symmetric _ _ _ _ hp (add_sample_error u v s t p hs ht)
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp left middle) right

theorem observation (a d b K A p : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b)
    (hx : Γ ⊢[PRAAx] familyRate a b K A) (hy : Γ ⊢[PRAAx] familyRate d b K A)
    (hz : Γ ⊢[PRAAx] familyRate (a+d) (two*b) K A) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (addF C G) p (centerData a d b)))
      (fstT (ap2 (addF logGammaF logGammaF) p (weightedData a d b))) (num 26) (unit p) := by
  let N := cutoff K A p
  let z := a+d
  let w := two*b
  let c := margin a d
  let e := GaussianGammaEulerMidpointLogGap.centerData N a d b
  let f := GaussianGammaEulerMidpointLogGap.weightedData N a d b
  have hN : Γ ⊢[PRAAx] le one N := zero_lt_succ _
  have hp := unit_positive (Γ := Γ) p
  have zz := le_trans ha (le_add_right a d)
  have ww := positive_product _ _ RationalAlgebra.two_positive hb
  have ex := GaussianGammaEulerRationalLog.name_regular N a b hN ha hb
  have ey := GaussianGammaEulerRationalLog.name_regular N d b hN hd hb
  have ez := GaussianGammaEulerRationalLog.name_regular N z w hN zz ww
  have gx := log_gamma_regular a b (.andI ha hb)
  have gy := log_gamma_regular d b (.andI hd hb)
  have gz := log_gamma_regular z w (.andI zz ww)
  have cc := constant_regular (Γ := Γ) c
  have zeroDist := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ap2 C p c) (unit p) hp
  have zDist := scaled_sample_error E logGammaF p two (ed N z w) (logGammaData z w) A N gz hN
    (cutoff_cover K A p) (cutoff_rate z w K A p hz)
  have centerDist := add_convergence C P C G c (productData E two (ed N z w))
    c (productData logGammaF two (logGammaData z w)) zero (num 3*two) p cc
    (GaussianGammaEulerRationalLogConvexity.scaled_regular E two _ ez) cc
    (GaussianGammaEulerRationalLogConvexity.scaled_regular logGammaF two _ gz) zeroDist zDist
  have endDist := add_convergence E E logGammaF logGammaF (ed N a b) (ed N d b)
    (logGammaData a b) (logGammaData d b) (num 3) (num 3) p ex ey gx gy
    (base_sample_error a b K A p hx) (base_sample_error d b K A p hy)
  have middle := real_order_at (addF C P) (addF E E) e f p p
    (GaussianGammaEulerMidpointLogGap.midpoint_order N a d b hN ha hd hb)
  have mid := upper_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) middle
    (le_of_eq_add (d := zero) (by ipra_ring))
  have left := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp centerDist)
  have right := scalar_upper _ _ _ _ hp endDist
  have answer := small_join _ _ _ _ _ p (small_join _ _ _ _ _ p left mid) right
  exact upper_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) answer

theorem order_from_rates (a d b K A : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b)
    (hx : Γ ⊢[PRAAx] familyRate a b K A) (hy : Γ ⊢[PRAAx] familyRate d b K A)
    (hz : Γ ⊢[PRAAx] familyRate (a+d) (two*b) K A) :
    Γ ⊢[PRAAx] realOrder (addF C G) (addF logGammaF logGammaF) (centerData a d b) (weightedData a d b) := by
  have ha' := le_trans ha (le_add_right a d)
  have hb' := positive_product _ _ RationalAlgebra.two_positive hb
  have gx := log_gamma_regular a b (.andI ha hb)
  have gy := log_gamma_regular d b (.andI hd hb)
  have gz := log_gamma_regular (a+d) (two*b) (.andI ha' hb')
  have cc := constant_regular (Γ := Γ) (margin a d)
  apply GaussianNamedRealOrderEnvelope.order_from_envelope (addF C G) (addF logGammaF logGammaF) _ _ (num 26)
    (add_fast _ _ _ _ cc (GaussianGammaEulerRationalLogConvexity.scaled_regular logGammaF two _ gz))
    (add_fast _ _ _ _ gx gy)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hA : Δ ⊢[PRAAx] le one (sh a) := by simpa [Fm.shift,Syn.shift,sh,Δ] using ha.shift
  have hD : Δ ⊢[PRAAx] le one (sh d) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hd.shift
  have hB : Δ ⊢[PRAAx] le one (sh b) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hb.shift
  have hX : Δ ⊢[PRAAx] familyRate (sh a) (sh b) (sh K) (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hx.shift
  have hY : Δ ⊢[PRAAx] familyRate (sh d) (sh b) (sh K) (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hy.shift
  have hZ : Δ ⊢[PRAAx] familyRate (sh a+sh d) (two*sh b) (sh K) (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
  simpa [GaussianNamedRealOrderEnvelope.envelope,Syn.shift,sh,Δ,centerData,weightedData] using
    observation (sh a) (sh d) (sh b) (sh K) (sh A) (var 0) hA hD hB hX hY hZ

theorem midpoint_order (a d b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder (addF C G) (addF logGammaF logGammaF) (centerData a d b) (weightedData a d b) := by
  let z := a+d
  let w := two*b
  let cut (x y : PTm n) := GaussianGammaEulerRationalLogMargin.cutoff x y
  let K := cut a b+cut d b+cut z w
  let A := rateCoefficient a b+rateCoefficient d b+rateCoefficient z w
  have hz : Γ ⊢[PRAAx] source z w :=
    .andI (le_trans ha (le_add_right a d)) (positive_product _ _ RationalAlgebra.two_positive hb)
  exact order_from_rates a d b K A ha hd hb
    (family_rate a b K A (.andI ha hb)
      (le_trans (le_add_right _ _) (le_add_right _ _)) (le_trans (le_add_right _ _) (le_add_right _ _)))
    (family_rate d b K A (.andI hd hb)
      (le_trans (le_add_left _ _) (le_add_right _ _)) (le_trans (le_add_left _ _) (le_add_right _ _)))
    (family_rate z w K A hz (le_add_left _ _) (le_add_left _ _))

theorem actual_positive_rational_log_Gamma_midpoint_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶ realOrder (addF C G) (addF logGammaF logGammaF)
      (centerData (var 0) (var 1) (var 2)) (weightedData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (midpoint_order _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeMidpointLogGap
