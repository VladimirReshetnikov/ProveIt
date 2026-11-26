import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingGlobalBounds
import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingRobbinsFinite
import IPRADerivations.Analysis.Stirling.GaussianStirlingConstantIdentification

/-!
# Sharp Robbins bounds at the original integer Stirling remainder

The finite lower telescoper retains the first positive margin. Its last
rational endpoint tends to zero at the same integer cutoff used by the
original Stirling limit. The resulting lower bound and the first sharp
upper margin apply to the original logarithmic remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingRobbins

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianStirlingGlobalBounds
  (limitRemainderF limitRemainderData remainderF remainderData finalUpper steps translatedPoint translatedRate
    endpoint_close rate_at integer_rate small_join limit_remainder_regular remainder_cross limit_bounds first_order_bounds)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (lowerValue lowerMargin lowerDifference lower_telescope lower_den_positive)
open GaussianStirlingRobbinsFinite (lowerCap lower_endpoint)
open GaussianStirlingTailComparison (point_add_upper_same point_order_refl)
open GaussianStirlingTelescope (shifted shifted_source)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius upper_of_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "A" => GaussianStirlingNames.nameF
local notation "I" => GaussianStirlingIntegerLimit.nameF
local notation "C" => GaussianStirlingConstant.nameF
local notation "G" => GaussianNamedDifference.nameF A A

def finalLower (a b : PTm n) : PTm n := qadd (lowerValue a b) (lowerMargin a b)
def bounds (f : PR 2) (a b x : PTm n) : Fm PTm n :=
  realOrder constantF f (finalLower a b) x ⋏ realOrder f constantF x (finalUpper a b)

@[simp] theorem subst_finalLower {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) :
    Syn.subst σ (finalLower a b) = finalLower (Syn.subst σ a) (Syn.subst σ b) := by simp [finalLower]

theorem add_last_lower_value (N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (lowerCap N a b) (lowerValue (shifted a b (succ N)) b) ≐ finalLower a b := by
  let x := lowerDifference a b (succ N)
  let y := lowerValue (shifted a b (succ N)) b
  let m := lowerMargin a b
  exact (GaussianStirlingGlobalBoundsFinite.swap_suffix x m y).eqTrans
    (qadd_congr ((GaussianRationalLinearProduct.qadd_commutative x y).eqTrans (lower_telescope a b (succ N) ha)) (.eqRefl _))

private theorem last_small (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (lowerValue (shifted a b (steps p)) b)) (fstT qzero) one (unit p) := by
  let c := shifted a b (steps p)
  let Q := num 12*c+b
  let P := unit p
  let q := lowerValue c b
  have cp := (shifted_source a b (steps p) hs).andE₁
  have hQ := lower_den_positive c b cp
  have hP := unit_positive (Γ := Γ) p
  have idx := GaussianStirlingIntegerLimit.index_dominates_unit (Γ := Γ) p
  have hstep : Γ ⊢[PRAAx] le P (steps p) := le_trans idx (le_succ_self _)
  have cap : Γ ⊢[PRAAx] le (b*P) (one*Q) := by
    have h : Γ ⊢[PRAAx] le (b*P) (b*(steps p)) := by ipra_le 𝔞 b*sl hstep
    dsimp only [Q,c,shifted]
    ipra_le sl h+𝔞 b+12*𝔞 a+11*𝔞 b*𝔞 (steps p)
  have raw := GaussianDominantPairAlgebra.radius_bounded b Q hQ
  have bound := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point b Q hQ).eqSymm (.eqRefl _) (.eqRefl _) raw
  have near := bounded_radius_mono q b Q one P hQ hP cap bound
  have z := GaussianRationalReconstruction.qsub_zero_right q (GaussianRationalHorner.ofGaussian_canonical _ _ hQ)
  have d : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded q qzero one P :=
    GaussianRationalReciprocal.bound_congr z.eqSymm (.eqRefl _) (.eqRefl _) near
  exact upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP d)

private theorem return_lower (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (finalLower a b)) (fstT (lowerCap (GaussianStirlingIntegerLimit.index p) a b)) one (unit p) := by
  let N := GaussianStirlingIntegerLimit.index p
  let L := lowerCap N a b
  let R := lowerValue (shifted a b (steps p)) b
  have e := add_last_lower_value N a b hs.andE₁
  have z := last_small a b p hs
  have o := upper_of_order (Γ := Γ) _ _ zero (unit p) (point_order_refl L)
  have both := point_add_upper_same L L R qzero zero one (unit p) (unit_positive p) o z
  exact upper_congr (congrFst e) (congrFst (GaussianReciprocalHorner.qadd_zero_right L (GaussianRationalHorner.qadd_canonical _ _)))
    (by ipra_ring) (.eqRefl _) both

private theorem observed_lower (a b x K p : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a)
    (h : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (translatedPoint a b p) (ap2 I p x) K (unit p)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (finalLower a b)))
      (fstT (ap2 limitRemainderF p (limitRemainderData a b x))) (K+num 15) (unit p) := by
  let N := GaussianStirlingIntegerLimit.index p
  let F := finalLower a b
  let M := lowerCap N a b
  let X := GaussianStirlingTelescopeName.endpointData (steps p) a b
  let Y := limitRemainderData a b x
  let P := unit p
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hp hp
  have a0 := return_lower a b p hs
  have a1 := upper_congr (congrFst (constant_at p F)).eqSymm (congrFst (constant_at p M)).eqSymm
    (.eqRefl _) (.eqRefl _) a0
  have f := real_order_at constantF G M X p p (lower_endpoint N a b hs hba)
  have f' : Γ ⊢[PRAAx] upper (fstT (ap2 constantF p M)) (fstT (ap2 G p X)) two P :=
    upper_mono _ _ _ _ _ _ den f (le_of_eq_add (d := zero) (by ipra_ring))
  have d := scalar_coordinate_distance _ _ _ _ hp (endpoint_close a b x K p hs h)
  have u := upper_of_radius _ _ _ _ d
  exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (small_join _ _ _ _ _ p (small_join _ _ _ _ _ p a1 f') u)

theorem limit_bounds (a b x K : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) (h : Γ ⊢[PRAAx] translatedRate a b x K) :
    Γ ⊢[PRAAx] bounds limitRemainderF a b (limitRemainderData a b x) := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let Y := limitRemainderData a b x
  have hs' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have hba' : Δ ⊢[PRAAx] le (sh b) (sh a) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hba.shift
  have h' : Δ ⊢[PRAAx] translatedRate (sh a) (sh b) (sh x) (sh K) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have lower : Γ ⊢[PRAAx] envelope constantF limitRemainderF (finalLower a b) Y (K+num 15) := by
    refine .allI ?_
    simpa [Δ,sh,Y,Syn.shift,envelope] using observed_lower _ _ _ _ (var 0) hs' hba' (rate_at _ _ _ _ (var 0) h')
  have hi := GaussianStirlingGlobalBounds.limit_bounds a b x K hs h
  exact .andI (order_from_envelope _ _ _ _ _ (constant_regular _) (limit_remainder_regular a b x hs) lower) hi.andE₂

theorem rational_bounds_from_rate (a b x K : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (h : Γ ⊢[PRAAx] translatedRate a b x K) : Γ ⊢[PRAAx] bounds remainderF a b (remainderData a b x) := by
  have lim := limit_bounds a b x K hs hba h
  have e := remainder_cross a b x hs (GaussianStirlingConstantIdentification.identification x x)
  exact .andI
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_refl _ _ (constant_regular _)) e lim.andE₁)
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ e) (cross_refl _ _ (constant_regular _)) lim.andE₂)

theorem integer_limit_bounds (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] bounds limitRemainderF i one (limitRemainderData i one x) :=
  limit_bounds i one x two (.andI hi (le_refl one)) hi (integer_rate i x)

theorem integer_bounds (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] bounds remainderF i one (remainderData i one x) :=
  rational_bounds_from_rate i one x two (.andI hi (le_refl one)) hi (integer_rate i x)

theorem actual_integer_Robbins_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ bounds remainderF (var 0) one (remainderData (var 0) one (var 1))) :=
  closeUniv 2 (.impI (integer_bounds _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingRobbins
