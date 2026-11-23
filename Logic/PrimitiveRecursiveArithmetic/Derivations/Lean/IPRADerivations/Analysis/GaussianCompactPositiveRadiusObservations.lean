import IPRADerivations.Analysis.GaussianCompactPositiveRadiusDominance
import IPRADerivations.Analysis.GaussianEulerVerticalShiftedRadius

/-!
# Independent observations from actual compact row dominance

The positive corrected companion supplied by the original weighted rows
itself derives the companion's lower observation envelope. Original name
regularity transfers both requested queries independently. One finite
rational gap removes only three auxiliary dyadics. The returned rational
radius is the actual real companion plus the two requested tolerances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactPositiveRadiusObservations

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactPositiveRadiusDominance (source correction)
open GaussianCompactRiemannName (nameF data)
open GaussianEulerVerticalRealRadius (gap denominator_positive)
open GaussianRationalHorner (qadd positive_product scalar_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalGaussianEmbedding (scalarZero)
open RationalValueBounds (upper upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def point (F : PR 3) (p a C E L T x : PTm n) : PTm n := ap2 (nameF F) p (data a C E L T x)
def corrected (G : PR 3) (p a C E L T y : PTm n) : PTm n := qadd (point G p a C E L T y) (correction p C E T)
def radiusNumerator (G : PR 3) (p q a C E L T y : PTm n) : PTm n :=
  gap (point G q a C E L T y) (unit q)*unit p+GaussianEulerVerticalRealRadius.denominator (point G q a C E L T y) (unit q)
def radiusDenominator (G : PR 3) (p q a C E L T y : PTm n) : PTm n :=
  GaussianEulerVerticalRealRadius.denominator (point G q a C E L T y) (unit q)*unit p
def realBound (G : PR 3) (p q a C E L T y : PTm n) : PTm n :=
  RationalArithmetic.add (GaussianEulerVerticalShiftedRadius.shiftedScalar (point G q a C E L T y) (unit q)) (fraction one (unit p))

@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (p a C E L T x : PTm n) :
    Syn.subst σ (point F p a C E L T x) = point F (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [point]

private theorem positive_coordinate (r : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive r) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE scalarZero (fstT r) :=
  GaussianRationalMetric.comparison_of_cleared _ _ zero (GaussianPositiveRealArithmetic.numerator (fstT r)) one
    (RationalSupMetric.denominatorOf (fstT r)) (le_refl one) (RationalArgmin.denominator_positive _)
    (RationalGaussianEmbedding.scalar_zero_represents one) (GaussianPositiveRealArithmetic.natural_representation _ h.andE₂)
    (le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le _))

/-- The actual corrected companion is one original dyadic from its
unchanged companion observation. -/
theorem corrected_distance (G : PR 3) (p a C E L T y : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    distanceBounded (corrected G p a C E L T y) (point G p a C E L T y) one (unit p) := by
  let D := E*unit (GaussianCompactRiemannName.precision p T)
  have hD : Γ ⊢[PRAAx] le one D := positive_product E (unit (GaussianCompactRiemannName.precision p T)) hE (unit_positive _)
  have norm := bounded_radius_mono (correction p C E T) (C*num 4) D one (unit p) hD (unit_positive p)
    (le_congr (.eqRefl _) (by dsimp only [D]; ipra_ring)
      (GaussianCompactPositiveRadiusDominance.correction_budget p C E T hC))
    (GaussianDominantPairAlgebra.radius_bounded (C*num 4) D hD)
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (correction p C E T) :=
    GaussianRationalHorner.ofGaussian_canonical _ _ hD
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qadd_sub_cancel (point G p a C E L T y) (correction p C E T) hc).eqSymm
    (.eqRefl _) (.eqRefl _) norm

/-- No nonnegativity of the compact output is assumed. Its lower
observation envelope follows from the supplied positive row radii. -/
theorem companion_lower (F G : PR 3) (q a C E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] source F G a C E L T x y) : Γ ⊢[PRAAx]
    upper scalarZero (fstT (point G q a C E L T y)) one (unit q) := by
  have diagonal := GaussianCompactPositiveRadiusDominance.original_compact_bound F G q a C E L T x y h
  have near := corrected_distance G q a C E L T y h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₁
  have coord := upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ (unit_positive q) near)
  exact RationalValueBounds.upper_order_left _ _ _ _ _ (positive_coordinate _ diagonal.andE₁) coord

theorem radius_value (F G : PR 3) (p q a C E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] source F G a C E L T x y) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (realBound G p q a C E L T y)
      (ZT.ofNat (radiusNumerator G p q a C E L T y)) (radiusDenominator G p q a C E L T y) := by
  have base := GaussianEulerVerticalShiftedRadius.shifted_represents (point G q a C E L T y) (unit q)
    (unit_positive q) (companion_lower F G q a C E L T x y h)
  have add := RationalRepresentations.represents_add _ _ _ _ _ _ base (fraction_represents one (unit p) (unit_positive p))
  apply scalar_congr (.eqRefl _) _ (.eqRefl _) add
  apply ZT.derive
  simp only [radiusNumerator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem companion_coordinate (F G : PR 3) (q t a C E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] source F G a C E L T x y) : Γ ⊢[PRAAx]
    upper (fstT (corrected G t a C E L T y)) (fstT (point G q a C E L T y))
      (two*unit q+unit t) (unit t*unit q) := by
  have d := positive_product _ _ (unit_positive (Γ := Γ) t) (unit_positive q)
  have near := corrected_distance G t a C E L T y h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₁
  have first := distance_radius_mono _ _ _ _ (unit q) (unit t*unit q) (unit_positive t) d
    (le_of_eq_add (d := zero) (by ipra_ring)) near
  have second := GaussianNameEquivalence.point_at (nameF G) (data a C E L T y) t q
    (GaussianCompactPositiveRadiusDominance.right_regular F G a C E L T x y h)
  have total : Γ ⊢[PRAAx] distanceBounded (corrected G t a C E L T y) (point G q a C E L T y)
      (two*unit q+unit t) (unit t*unit q) := distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ d first second)
  exact upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ d total)

private theorem original_slack (F G : PR 3) (p q t a C E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] source F G a C E L T x y) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point F p a C E L T x) (radiusNumerator G p q a C E L T y)
      (radiusDenominator G p q a C E L T y) (num 3) t := by
  let z := point F p a C E L T x
  let v := point G q a C E L T y
  let D := GaussianEulerVerticalRealRadius.denominator v (unit q)
  have margin := companion_lower F G q a C E L T x y h
  have rows := GaussianCompactPositiveRadiusDominance.original_compact_bound F G t a C E L T x y h
  have comp := GaussianEulerVerticalShiftedRadius.enlarged_norm_after_shift _ _ v (unit q) two (unit t)
    (unit_positive q) (unit_positive t) rows margin (companion_coordinate F G q t a C E L T x y h)
  have den := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive t)
  have step := GaussianNameEquivalence.point_at (nameF F) (data a C E L T x) p t
    (GaussianCompactPositiveRadiusDominance.left_regular F G a C E L T x y h)
  have second := positive_product (Γ := Γ) _ _ (denominator_positive v (unit q) (unit_positive q)) (unit_positive t)
  have total := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den second step comp
  have goalDen := positive_product _ _
    (positive_product (Γ := Γ) _ _ (denominator_positive v (unit q) (unit_positive q)) (unit_positive p)) (unit_positive t)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ den second) goalDen
    (le_congr (by dsimp only [radiusNumerator,radiusDenominator,unit,v]; ipra_ring) (.eqRefl _) (le_refl _)) total

theorem original_observations (F G : PR 3) (p q a C E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] source F G a C E L T x y) : Γ ⊢[PRAAx]
    bounded (point F p a C E L T x) (radiusNumerator G p q a C E L T y) (radiusDenominator G p q a C E L T y) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 3)
    (positive_product _ _ (denominator_positive _ _ (unit_positive q)) (unit_positive p))
    (original_slack F G p q _ a C E L T x y h)

theorem actual_original_compact_dominance_independent_observations_closed (F G : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source F G (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (point F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (radiusNumerator G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8))
        (radiusDenominator G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8)) ⋏
      RationalArithmetic.represents (realBound G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8))
        (ZT.ofNat (radiusNumerator G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8)))
        (radiusDenominator G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8))) :=
  closeUniv 9 (.impI (.andI (original_observations F G _ _ _ _ _ _ _ _ _ Prf.hyp0)
    (radius_value F G _ _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCompactPositiveRadiusObservations
