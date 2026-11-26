import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumChordReadback
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# The strong Gamma chord as a comparison of named differences

The exact normalized product of W and the center difference has the same
cofinal order as the explicit finite comparison. The output retains the
original two independent observation clocks of the normalized names.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaMinimumChord (centerData center_source margin)
open GaussianGammaMinimumChordReadback (difference_at)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameRingLaws (add_sample_error sum_right_error three)
open GaussianNamedNaturalScaleOrder (cost)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGlobalBounds (small_join)
open RationalValueBounds (upper upper_congr upper_of_radius)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => logGammaF
local notation "lg" => logGammaData

abbrev differenceF : PR 2 := GaussianNamedDifference.nameF G G
abbrev scaledDifferenceF : PR 2 := productF differenceF
abbrev lowerF : PR 2 := addF C scaledDifferenceF

def centerDifferenceData (a c b W : PTm n) : PTm n :=
  GaussianNamedDifference.data (centerData a c b W) (lg a b)

def targetDifferenceData (a c b : PTm n) : PTm n :=
  GaussianNamedDifference.data (lg c b) (lg a b)

def lowerData (a c b M W : PTm n) : PTm n :=
  addData (margin a c b M) (productData differenceF W (centerDifferenceData a c b W))

def budget (a c b W : PTm n) : PTm n :=
  GaussianGammaMinimumChordReadback.budget a c b W+cost differenceF W (centerDifferenceData a c b W)+num 6*W+num 9

@[simp] theorem subst_centerDifferenceData {m : ℕ} (σ : Fin n → PTm m) (a c b W : PTm n) :
    Syn.subst σ (centerDifferenceData a c b W) =
      centerDifferenceData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ W) := by
  simp [centerDifferenceData]
@[simp] theorem subst_targetDifferenceData {m : ℕ} (σ : Fin n → PTm m) (a c b : PTm n) :
    Syn.subst σ (targetDifferenceData a c b) =
      targetDifferenceData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) := by
  simp [targetDifferenceData]
@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (a c b M W : PTm n) :
    Syn.subst σ (lowerData a c b M W) =
      lowerData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ M) (Syn.subst σ W) := by
  simp [lowerData]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a c b W : PTm n) :
    Syn.subst σ (budget a c b W) = budget (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ W) := by
  simp [budget]

theorem target_regular (a c b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] pointCN differenceF (targetDifferenceData a c b) :=
  GaussianNamedDifference.name_regular G G _ _ (log_gamma_regular c b (.andI hc hb)) (log_gamma_regular a b (.andI ha hb))

theorem center_regular (a c b W : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] pointCN differenceF (centerDifferenceData a c b W) :=
  GaussianNamedDifference.name_regular G G _ _
    (log_gamma_regular _ _ (center_source a c b W hc hb hW)) (log_gamma_regular a b (.andI ha hb))

theorem lower_regular (a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) (hW : Γ ⊢[PRAAx] le two W) : Γ ⊢[PRAAx] pointCN lowerF (lowerData a c b M W) :=
  add_fast C scaledDifferenceF _ _ (constant_regular _)
    (GaussianNamedNaturalScaleOrder.regular differenceF W _ (center_regular a c b W ha hc hb hW))

theorem sample_envelope (p a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b)) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] upper (fstT (ap2 lowerF p (lowerData a c b M W)))
      (fstT (ap2 differenceF p (targetDifferenceData a c b))) (budget a c b W) (unit p) := by
  let P := unit p
  let m := margin a c b M
  let z := centerDifferenceData a c b W
  let S := ap2 scaledDifferenceF p (productData differenceF W z)
  let D := ap2 differenceF p z
  let L := ap2 lowerF p (lowerData a c b M W)
  let Q := qsub (ap2 G p (centerData a c b W)) (ap2 G p (lg a b))
  have hP := unit_positive (Γ := Γ) p
  have hx := log_gamma_regular a b (.andI ha hb)
  have hy := log_gamma_regular c b (.andI hc hb)
  have hz := log_gamma_regular _ _ (center_source a c b W hc hb hW)
  have hD := center_regular a c b W ha hc hb hW
  have scaled := GaussianNamedNaturalScaleOrder.sample_error differenceF W z p hD
  have delta : Γ ⊢[PRAAx] distanceBounded D Q (num 6) P :=
    GaussianNamedDifference.sample_error G G (centerData a c b W) (lg a b) p hz hx
  have scaleDelta : Γ ⊢[PRAAx] distanceBounded (natScale W D) (natScale W Q) (W*num 6) P :=
    distance_congr (natScale_as_product W D).eqSymm (natScale_as_product W Q).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifferenceQuotient.scale_distance _ _ _ _ _ _ hP (GaussianNamedNaturalScale.natural_point_bound W) delta)
  have scaleError : Γ ⊢[PRAAx] distanceBounded S (natScale W Q) (cost differenceF W z+W*num 6) P :=
    distance_triangle_same _ _ _ _ _ _ hP scaled scaleDelta
  have addError : Γ ⊢[PRAAx] distanceBounded L (qadd m S) three P :=
    distance_congr (.eqRefl _) (qadd_congr (constant_at p m) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
      (add_sample_error C scaledDifferenceF m (productData differenceF W z) p (constant_regular m)
        (GaussianNamedNaturalScaleOrder.regular differenceF W z hD))
  have left := distance_triangle_same _ _ _ _ _ _ hP addError (sum_right_error m _ _ _ _ hP scaleError)
  have right := GaussianNamedDifference.sample_error G G (lg c b) (lg a b) p hy hx
  have raw := difference_at p a c b M W ha hc hb haM hcM hW
  have front := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP left)
  have back := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP (distance_symmetric _ _ _ _ hP right))
  exact upper_congr (.eqRefl _) (.eqRefl _) (by unfold budget three; ipra_ring) (.eqRefl _)
    (small_join _ _ _ _ _ p (small_join _ _ _ _ _ p front raw) back)

theorem difference_order (a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b)) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] realOrder lowerF differenceF (lowerData a c b M W) (targetDifferenceData a c b) := by
  refine order_from_envelope _ _ _ _ (budget a c b W)
    (lower_regular a c b M W ha hc hb hW) (target_regular a c b ha hc hb) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hsa : Δ ⊢[PRAAx] le one (sh a) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using ha.shift
  have hsc : Δ ⊢[PRAAx] le one (sh c) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hc.shift
  have hsb : Δ ⊢[PRAAx] le one (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hb.shift
  have hsaM : Δ ⊢[PRAAx] le (sh a) (sh M*sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using haM.shift
  have hscM : Δ ⊢[PRAAx] le (sh c) (sh M*sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hcM.shift
  have hsW : Δ ⊢[PRAAx] le two (sh W) := by simpa [Δ,sh,Fm.shift,Syn.shift,two,one] using hW.shift
  simpa [envelope,sh,Δ,Syn.shift] using sample_envelope (var 0) (sh a) (sh c) (sh b) (sh M) (sh W)
    hsa hsc hsb hsaM hscM hsW

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordDifference
