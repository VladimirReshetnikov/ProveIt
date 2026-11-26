import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingGlobalBoundsFinite
import IPRADerivations.Analysis.Stirling.GaussianStirlingOriginalIntegerLimit
import IPRADerivations.Analysis.Stirling.GaussianStirlingConstant
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Cofinal sharp Stirling remainder bounds

Finite endpoint differences pass to the original integer limit whenever
the translated Stirling samples have a cofinal dyadic error bound.
The integer translated bound is supplied by the actual integer sampler.
The comparison with the logarithm of (2pi) uses the named constant
identity and preserves the finite margins.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBounds

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianRationalHorner (positive_product qadd qzero)
open GaussianRationalMetric (distanceBounded qsub qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianStirlingGlobalBoundsFinite (upperCap endpoint_bounds)
open GaussianStirlingNames (nameData source name_regular)
open GaussianStirlingRationalTelescopers (firstTerm upperDifference upperMargin upperValue upper_telescope upper_den_positive)
open GaussianStirlingTelescope (shifted shifted_source)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius radius_symmetric upper_order_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "A" => GaussianStirlingNames.nameF
local notation "I" => GaussianStirlingIntegerLimit.nameF
local notation "C" => GaussianStirlingConstant.nameF
local notation "G" => GaussianNamedDifference.nameF A A

def limitRemainderF : PR 2 := GaussianNamedDifference.nameF A I
def limitRemainderData (a b x : PTm n) : PTm n := GaussianNamedDifference.data (nameData a b) x
def remainderF : PR 2 := GaussianNamedDifference.nameF A C
def remainderData (a b x : PTm n) : PTm n := GaussianNamedDifference.data (nameData a b) (GaussianStirlingConstant.nameData x)
def finalUpper (a b : PTm n) : PTm n := qsub (upperValue a b) (upperMargin a b)
def steps (p : PTm n) : PTm n := succ (GaussianStirlingIntegerLimit.index p)
def translatedPoint (a b p : PTm n) : PTm n := ap2 A p (nameData (shifted a b (steps p)) b)

def translatedRate (a b x K : PTm n) : Fm PTm n :=
  .all (distanceBounded (translatedPoint (Syn.shift a) (Syn.shift b) (var 0))
    (ap2 I (var 0) (Syn.shift x)) (Syn.shift K) (unit (var 0)))

ipra_subst limitRemainderData
ipra_subst remainderData
ipra_subst finalUpper
ipra_subst steps
ipra_subst translatedPoint
ipra_subst translatedRate [Syn.subst_shift, Syn.shift_subst]

theorem rate_at (a b x K p : PTm n) (h : Γ ⊢[PRAAx] translatedRate a b x K) :
    Γ ⊢[PRAAx] distanceBounded (translatedPoint a b p) (ap2 I p x) K (unit p) := by
  simpa only [translatedRate,GaussianRationalMetric.subst_distanceBounded,subst_translatedPoint,subst_ap2,
    GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem integer_rate_at (i x p : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (translatedPoint i one p) (ap2 I p x) two (unit p) := by
  let j := shifted i one (steps p)
  let W := unit p
  have late : Γ ⊢[PRAAx] le (GaussianStirlingIntegerLimit.index p) j := by
    dsimp [j,shifted,steps]
    ipra_le 𝔞 i+1
  have d := GaussianStirlingIntegerLimit.later_integer_distance p p j late
    GaussianStirlingOriginalIntegerLimit.integer_tail_contract
  have hp := unit_positive (Γ := Γ) p
  have e := distance_congr (GaussianStirlingIntegerLimit.name_at p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) d
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (distance_symmetric _ _ _ _ (positive_product _ _ hp hp) e)

theorem integer_rate (i x : PTm n) : Γ ⊢[PRAAx] translatedRate i one x two := by
  refine .allI ?_
  simpa [translatedRate,Syn.shift] using integer_rate_at (Γ := Γ.map Fm.shift) (Syn.shift i) (Syn.shift x) (var 0)

theorem limit_remainder_regular (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN limitRemainderF (limitRemainderData a b x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (name_regular a b hs) (GaussianStirlingOriginalIntegerLimit.limit_regular x)

theorem remainder_regular (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN remainderF (remainderData a b x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (name_regular a b hs) (GaussianStirlingConstant.name_regular x)

theorem remainder_cross (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] crossEquivalent I C x (GaussianStirlingConstant.nameData x)) :
    Γ ⊢[PRAAx] crossEquivalent limitRemainderF remainderF (limitRemainderData a b x) (remainderData a b x) :=
  GaussianNamedDifferenceQuotientProperness.difference_proper A A I C (nameData a b) (nameData a b)
    x (GaussianStirlingConstant.nameData x) (name_regular a b hs) (name_regular a b hs)
    (GaussianStirlingOriginalIntegerLimit.limit_regular x) (GaussianStirlingConstant.name_regular x)
    (cross_refl _ _ (name_regular a b hs)) hc

theorem endpoint_close (a b x K p : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] distanceBounded (translatedPoint a b p) (ap2 I p x) K (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (GaussianStirlingTelescopeName.endpointData (steps p) a b))
      (ap2 limitRemainderF p (limitRemainderData a b x)) (K+num 12) (unit p) := by
  let y := nameData a b
  let z := nameData (shifted a b (steps p)) b
  let u := ap2 A p y
  let v := ap2 A p z
  let w := ap2 I p x
  let P := unit p
  have pos := unit_positive (Γ := Γ) p
  have ha := name_regular a b hs
  have hb := name_regular (shifted a b (steps p)) b (shifted_source a b (steps p) hs)
  have l := GaussianNamedDifference.sample_error A A y z p ha hb
  have r := GaussianNamedDifference.sample_error A I y x p ha (GaussianStirlingOriginalIntegerLimit.limit_regular x)
  have mid := GaussianNamedDifference.difference_distance u u v w zero K P pos
    (GaussianRationalPowerDifference.distance_refl_zero u P pos) h
  have d := distance_triangle_same _ _ _ _ _ _ pos
    (distance_triangle_same _ _ _ _ _ _ pos l mid) (distance_symmetric _ _ _ _ pos r)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) d

theorem small_join (x y z M N p : PTm n) (a : Γ ⊢[PRAAx] upper x y M (unit p))
    (b : Γ ⊢[PRAAx] upper y z N (unit p)) : Γ ⊢[PRAAx] upper x z (M+N) (unit p) :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
    (upper_triangle _ _ _ _ _ _ _ a b) (le_of_eq_add (d := zero) (by ipra_ring))

theorem upper_cap_le (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] rationalLE (fstT (upperCap N a b)) (fstT (finalUpper a b)) := by
  let t := succ N
  let c := shifted a b t
  let u := upperValue c b
  let d := upperDifference a b t
  let r := qnegative (upperMargin a b)
  let z : PTm n := qzero
  have hc := (shifted_source a b t hs).andE₁
  have nz := (GaussianRationalNonnegativeFractions.fraction_nonnegative b (num 12*c) (upper_den_positive c hc)).andE₁
  have m := point_add_order z u d d (rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _) nz) (point_order_refl d)
  have den := positive_product _ _ (upper_den_positive a hs.andE₁) hc
  have cd : Γ ⊢[PRAAx] GaussianRationalHorner.canonical d := GaussianRationalHorner.ofGaussian_canonical _ _ den
  have q := rationalLE_congr (congrFst (GaussianRationalSyntheticDivision.qzero_add d cd))
    (congrFst (upper_telescope a b t hs.andE₁)) m
  exact point_add_order _ _ r r q (point_order_refl r)

def firstOrderBounds (f : PR 2) (a b x : PTm n) : Fm PTm n :=
  realOrder constantF f (firstTerm a b) x ⋏ realOrder f constantF x (finalUpper a b)

private theorem observations (a b x K p : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] distanceBounded (translatedPoint a b p) (ap2 I p x) K (unit p)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (firstTerm a b)))
        (fstT (ap2 limitRemainderF p (limitRemainderData a b x))) (K+num 14) (unit p) ⋏
      upper (fstT (ap2 limitRemainderF p (limitRemainderData a b x)))
        (fstT (ap2 constantF p (finalUpper a b))) (K+num 14) (unit p) := by
  let N := GaussianStirlingIntegerLimit.index p
  let X := GaussianStirlingTelescopeName.endpointData (steps p) a b
  let Y := limitRemainderData a b x
  let L := firstTerm a b
  let U := upperCap N a b
  let F := finalUpper a b
  have he := endpoint_bounds N a b hs
  have lo := real_order_at constantF G L X p p he.andE₁
  have hi := real_order_at G constantF X U p p he.andE₂
  have pos := unit_positive (Γ := Γ) p
  have den := positive_product _ _ pos pos
  have left : Γ ⊢[PRAAx] upper (fstT (ap2 constantF p L)) (fstT (ap2 G p X)) two (unit p) :=
    upper_mono _ _ _ _ _ _ den lo (le_of_eq_add (d := zero) (by ipra_ring))
  have right : Γ ⊢[PRAAx] upper (fstT (ap2 G p X)) (fstT (ap2 constantF p F)) two (unit p) := by
    have m := upper_mono _ _ _ _ two (unit p) den hi (le_of_eq_add (d := zero) (by ipra_ring))
    have v := upper_congr (.eqRefl _) (congrFst (constant_at p U)) (.eqRefl _) (.eqRefl _) m
    exact upper_congr (.eqRefl _) (congrFst (constant_at p F)).eqSymm (.eqRefl _) (.eqRefl _)
      (upper_order_right _ _ _ _ _ v (upper_cap_le N a b hs))
  have cost := scalar_coordinate_distance _ _ _ _ pos (endpoint_close a b x K p hs h)
  have forward := upper_of_radius _ _ _ _ cost
  have backward := upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ cost)
  exact .andI (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (small_join _ _ _ _ _ p left forward))
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (small_join _ _ _ _ _ p backward right))

theorem limit_bounds (a b x K : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] translatedRate a b x K) :
    Γ ⊢[PRAAx] firstOrderBounds limitRemainderF a b (limitRemainderData a b x) := by
  let sh (y : PTm n) := Syn.shift y
  let Δ := Γ.map Fm.shift
  let Y := limitRemainderData a b x
  have hs' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have h' : Δ ⊢[PRAAx] translatedRate (sh a) (sh b) (sh x) (sh K) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have left : Γ ⊢[PRAAx] envelope constantF limitRemainderF (firstTerm a b) Y (K+num 14) := by
    refine .allI ?_
    simpa [envelope,sh,Syn.shift,Y,Δ] using
      (observations _ _ _ _ (var 0) hs' (rate_at _ _ _ _ (var 0) h')).andE₁
  have right : Γ ⊢[PRAAx] envelope limitRemainderF constantF Y (finalUpper a b) (K+num 14) := by
    refine .allI ?_
    simpa [envelope,sh,Syn.shift,Y,Δ] using
      (observations _ _ _ _ (var 0) hs' (rate_at _ _ _ _ (var 0) h')).andE₂
  have reg := limit_remainder_regular a b x hs
  exact .andI (order_from_envelope _ _ _ _ _ (constant_regular _) reg left)
    (order_from_envelope _ _ _ _ _ reg (constant_regular _) right)

theorem first_order_bounds (a b x K : PTm n) (hs : Γ ⊢[PRAAx] source a b) (ht : Γ ⊢[PRAAx] translatedRate a b x K)
    (hc : Γ ⊢[PRAAx] crossEquivalent I C x (GaussianStirlingConstant.nameData x)) :
    Γ ⊢[PRAAx] firstOrderBounds remainderF a b (remainderData a b x) := by
  have h := limit_bounds a b x K hs ht
  have e := remainder_cross a b x hs hc
  exact .andI
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_refl _ _ (constant_regular _)) e h.andE₁)
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ e) (cross_refl _ _ (constant_regular _)) h.andE₂)

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBounds
