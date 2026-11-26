import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogConvexity
import IPRADerivations.Analysis.Names.Rates.GaussianNaturalScaleProductRate
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderEnvelope

/-!
# Cofinal transfer of Euler log convexity to the original Gamma names

A common explicit cutoff covers the three inverse Euler approximants.
The known weighted convexity gives a diagonal order envelope between
the native names. Independent-clock order follows by slack removal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeLogConvexityCore

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogConvexity (centerData weightedData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiply_fast sum_distance)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNaturalScaleProductName (productF productData)
open GaussianNaturalScaleProductRate (scaled_sample_error)
open GaussianRationalDistanceOrder (distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open RationalValueBounds (upper upper_of_radius upper_mono upper_triangle)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianGammaEulerRationalLog.nameF
local notation "ed" => GaussianGammaEulerRationalLog.data
local notation "P" => productF E
local notation "G" => productF logGammaF
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def nativeCenterData (a d b r s : PTm n) : PTm n :=
  productData logGammaF (weight r s) (logGammaData (barycenter a d r s) (weight r s*b))
def nativeWeightedData (a d b r s : PTm n) : PTm n :=
  addData (productData logGammaF (succ r) (logGammaData a b)) (productData logGammaF s (logGammaData d b))

def familyRate (a b K C : PTm n) : Fm PTm n :=
  .all (le (Syn.shift K) (var 0) ⟶ independentRate E logGammaF
    (ed (var 0) (Syn.shift a) (Syn.shift b)) (logGammaData (Syn.shift a) (Syn.shift b)) (Syn.shift C) (var 0))

def cutoff (K C p : PTm n) : PTm n := succ ((K+C)*unit p)

private theorem scaled_regular (f : PR 2) (i x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (productF f) (productData f i x) :=
  multiply_fast constantF f _ _ (constant_regular (naturalPoint i)) h

private theorem positive_center (a d r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (barycenter a d r s) :=
  le_trans (positive_product _ _ (zero_lt_succ r) ha) (le_add_right _ _)

private theorem positive_denominator (b r s : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (weight r s*b) := positive_product _ _ (zero_lt_succ (r+s)) hb

private theorem coordinate_upper (z w A p : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded z w A (unit p)) :
    Γ ⊢[PRAAx] upper (fstT z) (fstT w) A (unit p) :=
  upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive p) h)

private theorem join (z w v A B p : PTm n)
    (h : Γ ⊢[PRAAx] upper z w A (unit p)) (j : Γ ⊢[PRAAx] upper w v B (unit p)) :
    Γ ⊢[PRAAx] upper z v (A+B) (unit p) :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
    (upper_triangle _ _ _ _ _ _ _ h j) (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))

theorem observation (a d b r s K C p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b)
    (rateX : Γ ⊢[PRAAx] familyRate a b K C) (rateY : Γ ⊢[PRAAx] familyRate d b K C)
    (rateZ : Γ ⊢[PRAAx] familyRate (barycenter a d r s) (weight r s*b) K C) :
    Γ ⊢[PRAAx] upper (fstT (ap2 G p (nativeCenterData a d b r s)))
      (fstT (ap2 (addF G G) p (nativeWeightedData a d b r s)))
      (num 3*weight r s+two+(num 3+ (num 3*succ r+num 3*s)+num 3)) (unit p) := by
  let N := cutoff K C p
  let M := weight r s
  let Z := barycenter a d r s
  let W := M*b
  have pos : Γ ⊢[PRAAx] le one N := zero_lt_succ _
  have Upos := unit_positive (Γ := Γ) p
  have large : Γ ⊢[PRAAx] le K N := by
    have h := mul_le_mul_right K Upos
    unfold N cutoff
    ipra_le 𝔞 C*𝔞 (unit p)+1+sl h
  have cover : Γ ⊢[PRAAx] le (C*unit p) N := by
    unfold N cutoff
    ipra_le 𝔞 K*𝔞 (unit p)+1
  have hZ := positive_center a d r s ha
  have hW := positive_denominator b r s hb
  have atRate (a b : PTm n) (hr : Γ ⊢[PRAAx] familyRate a b K C) :
      Γ ⊢[PRAAx] independentRate E logGammaF (ed N a b) (logGammaData a b) C N := by
    have h : Γ ⊢[PRAAx] (le K N ⟶ independentRate E logGammaF (ed N a b) (logGammaData a b) C N) := by
      simpa [familyRate] using hr.allE N
    exact h.impE large
  have GX := log_gamma_regular a b (.andI ha hb)
  have GY := log_gamma_regular d b (.andI hd hb)
  have GZ := log_gamma_regular Z W (.andI hZ hW)
  have EX := GaussianGammaEulerRationalLog.name_regular N a b pos ha hb
  have EY := GaussianGammaEulerRationalLog.name_regular N d b pos hd hb
  have center := scaled_sample_error E logGammaF p M (ed N Z W) (logGammaData Z W) C N GZ pos cover
    (atRate Z W rateZ)
  have endpointX := scaled_sample_error E logGammaF p (succ r) (ed N a b) (logGammaData a b) C N GX pos cover
    (atRate a b rateX)
  have endpointY := scaled_sample_error E logGammaF p s (ed N d b) (logGammaData d b) C N GY pos cover
    (atRate d b rateY)
  let ex := productData E (succ r) (ed N a b)
  let ey := productData E s (ed N d b)
  let gx := productData logGammaF (succ r) (logGammaData a b)
  let gy := productData logGammaF s (logGammaData d b)
  have eadd := GaussianNameRingLaws.add_sample_error P P ex ey p
    (scaled_regular E (succ r) (ed N a b) EX) (scaled_regular E s (ed N d b) EY)
  have gadd := GaussianNameRingLaws.add_sample_error G G gx gy p
    (scaled_regular logGammaF (succ r) (logGammaData a b) GX) (scaled_regular logGammaF s (logGammaData d b) GY)
  have sc := sum_distance (ap2 P p ex) (ap2 G p gx) (ap2 P p ey) (ap2 G p gy)
    (num 3*succ r) (num 3*s) (unit p) Upos endpointX endpointY
  have sum := distance_triangle_same _ _ _ _ _ _ Upos eadd
    (distance_triangle_same _ _ _ _ _ _ Upos sc (distance_symmetric _ _ _ _ Upos gadd))
  have mid := real_order_at P (addF P P) (centerData N a d b r s) (weightedData N a d b r s) p p
    (GaussianGammaEulerRationalLogConvexity.weighted_convexity N a d b r s pos ha hd hb)
  have normalized := upper_mono _ _ _ _ two (unit p) (positive_product _ _ Upos Upos) mid
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
  have l := coordinate_upper _ _ _ p (distance_symmetric _ _ _ _ Upos center)
  have e := coordinate_upper _ _ _ p sum
  have aligned := join _ _ _ _ _ p (join _ _ _ _ _ p l normalized) e
  exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) aligned

@[simp] theorem subst_familyRate {m : ℕ} (σ : Fin n → PTm m) (a b K C : PTm n) :
    (familyRate a b K C).subst σ = familyRate (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) (Syn.subst σ C) := by
  simp [familyRate,Syn.subst_shift,Syn.shift_subst]

theorem weighted_convexity_of_family_rates (a d b r s K C : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b)
    (rateX : Γ ⊢[PRAAx] familyRate a b K C) (rateY : Γ ⊢[PRAAx] familyRate d b K C)
    (rateZ : Γ ⊢[PRAAx] familyRate (barycenter a d r s) (weight r s*b) K C) :
    Γ ⊢[PRAAx] realOrder G (addF G G) (nativeCenterData a d b r s) (nativeWeightedData a d b r s) := by
  have hZ := positive_center a d r s ha
  have hW := positive_denominator b r s hb
  have GX := log_gamma_regular a b (.andI ha hb)
  have GY := log_gamma_regular d b (.andI hd hb)
  have GZ := log_gamma_regular (barycenter a d r s) (weight r s*b) (.andI hZ hW)
  apply GaussianNamedRealOrderEnvelope.order_from_envelope G (addF G G) _ _
    (num 3*weight r s+two+(num 3+(num 3*succ r+num 3*s)+num 3))
    (scaled_regular _ _ _ GZ) (add_fast _ _ _ _ (scaled_regular _ _ _ GX) (scaled_regular _ _ _ GY))
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hA : Γ.map Fm.shift ⊢[PRAAx] le one (sh a) := by simpa [Fm.shift,Syn.shift,sh,one] using ha.shift
  have hD : Γ.map Fm.shift ⊢[PRAAx] le one (sh d) := by simpa [Fm.shift,Syn.shift,sh,one] using hd.shift
  have hB : Γ.map Fm.shift ⊢[PRAAx] le one (sh b) := by simpa [Fm.shift,Syn.shift,sh,one] using hb.shift
  have hX : Γ.map Fm.shift ⊢[PRAAx] familyRate (sh a) (sh b) (sh K) (sh C) := by
    simpa [Fm.shift,Syn.shift,sh] using rateX.shift
  have hY : Γ.map Fm.shift ⊢[PRAAx] familyRate (sh d) (sh b) (sh K) (sh C) := by
    simpa [Fm.shift,Syn.shift,sh] using rateY.shift
  have hRateZ : Γ.map Fm.shift ⊢[PRAAx] familyRate (barycenter (sh a) (sh d) (sh r) (sh s))
      (weight (sh r) (sh s)*sh b) (sh K) (sh C) := by
    simpa [Fm.shift,Syn.shift,sh,weight,barycenter] using rateZ.shift
  simpa [GaussianNamedRealOrderEnvelope.envelope,Syn.shift,sh,weight,barycenter,nativeCenterData,nativeWeightedData]
    using observation (sh a) (sh d) (sh b) (sh r) (sh s) (sh K) (sh C) (var 0) hA hD hB hX hY hRateZ

end LeanProofs.IPRA.Analysis.GaussianGammaNativeLogConvexityCore
