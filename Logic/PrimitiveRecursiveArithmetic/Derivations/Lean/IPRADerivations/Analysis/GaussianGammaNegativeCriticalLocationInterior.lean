import IPRADerivations.Analysis.GaussianGammaNegativeCriticalLocation
import IPRADerivations.Analysis.GaussianNamedStrictOrderDifference

/-!
# Strict position between the two negative poles

The selected fraction is separated from both ends of [0,1] by exactly
the guard used by the search, (1/[4(N+2)]). Shifting this offset by
(−N−1) gives strict named order between the actual adjacent poles.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationInterior

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNegativeCriticalEndpoints (mesh mesh_minimum rightNumerator right_add)
open GaussianGammaNegativeCriticalGrid (denominator numerator leftIndex room selected locationF location_at)
open GaussianGammaNegativeCriticalLocation
  (lower fractionLocationF fraction_location_at fraction_location_regular location_regular denominator_positive)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl cross_trans)
open GaussianNameRingLaws (add_sample_error three equivalent_of_envelope)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedStrictOrderDifference (trans_weak weak_trans add_right)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalMetric (distanceBounded qsub qnegative qsub_canonical qnegative_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper_of_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "CF" => constantF
local notation "OF" => fractionLocationF

def leftPole (N : PTm n) : PTm n := qsub qzero (fraction (succ N) one)
def rightPole (N : PTm n) : PTm n := qsub qzero (fraction N one)

@[simp] theorem subst_leftPole {k : ℕ} (σ : Fin n → PTm k) (N : PTm n) :
    Syn.subst σ (leftPole N) = leftPole (Syn.subst σ N) := by simp [leftPole]
@[simp] theorem subst_rightPole {k : ℕ} (σ : Fin n → PTm k) (N : PTm n) :
    Syn.subst σ (rightPole N) = rightPole (Syn.subst σ N) := by simp [rightPole]

private theorem mesh_positive (N : PTm n) : Γ ⊢[PRAAx] le one (mesh N) :=
  le_trans (by ipra_le 7) (mesh_minimum N)

theorem offset_lower_at (p N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT (fraction one (mesh N))) (fstT (GaussianGammaNegativeCriticalLocation.fractionLocation p N)) := by
  let M := mesh N
  let B := denominator p N
  have h : Γ ⊢[PRAAx] le (unit p) (lower p N) := le_add_right _ _
  exact fractions_order one M (lower p N) B (mesh_positive N) (denominator_positive p N)
    (by unfold B denominator; ipra_le 𝔞(M)*sl h)

theorem offset_upper_at (p N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT (GaussianGammaNegativeCriticalLocation.fractionLocation p N))
      (fstT (fraction (rightNumerator N) (mesh N))) := by
  let M := mesh N
  let a := lower p N
  let B := denominator p N
  have h : Γ ⊢[PRAAx] le (a+unit p) B := room p N _ (le_of_lt (selected p N).andE₁)
  have e := natEq (right_add (Γ := Γ) N)
  exact fractions_order a B (rightNumerator N) M (denominator_positive p N) (mesh_positive N)
    (by dsimp only [B,M,denominator] at *
        ipra_le 𝔞(mesh N)*sl h with -𝔞(mesh N)*𝔞(unit p)*e)

theorem offset_bounds (N : PTm n) : Γ ⊢[PRAAx]
    realOrder CF OF (fraction one (mesh N)) N ⋏ realOrder OF CF N (fraction (rightNumerator N) (mesh N)) := by
  refine .andI (.allI (.allI ?_)) (.allI (.allI ?_))
  · let W := Syn.shift (Syn.shift N)
    let Δ := (Γ.map Fm.shift).map Fm.shift
    have h := offset_lower_at (Γ := Δ) (var 0) W
    simp only [Syn.shift,GaussianPositiveRationalLogarithm.subst_fraction,
      GaussianGammaNegativeCriticalEndpoints.subst_mesh,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    exact upper_of_order _ _ _ _
      (rationalLE_congr (congrFst (constant_at (var 1) _)).eqSymm (congrFst (fraction_location_at (var 0) W)).eqSymm h)
  · let W := Syn.shift (Syn.shift N)
    let Δ := (Γ.map Fm.shift).map Fm.shift
    have h := offset_upper_at (Γ := Δ) (var 1) W
    simp only [Syn.shift,GaussianPositiveRationalLogarithm.subst_fraction,
      GaussianGammaNegativeCriticalEndpoints.subst_rightNumerator,GaussianGammaNegativeCriticalEndpoints.subst_mesh]
    exact upper_of_order _ _ _ _
      (rationalLE_congr (congrFst (fraction_location_at (var 1) W)).eqSymm (congrFst (constant_at (var 0) _)).eqSymm h)

private theorem fraction_strict (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] lt (d*a) (c*b)) :
    Γ ⊢[PRAAx] strictOrder CF CF (fraction a b) (fraction c d) :=
  .andI (constant_order _ _ (fractions_order a b c d hb hd (le_of_lt h))) (strict_fractions a b c d hb hd h)

theorem offset_interior (N : PTm n) : Γ ⊢[PRAAx]
    strictOrder CF OF qzero N ⋏ strictOrder OF CF N (fraction one one) := by
  let M := mesh N
  have h := offset_bounds (Γ := Γ) N
  have eq := natEq (right_add (Γ := Γ) N)
  have left := fraction_strict (Γ := Γ) zero one one M (le_refl _) (mesh_positive N) (by unfold lt; ipra_le 0)
  have q := GaussianSignedNameExponentialOrder.constant_equal_cross _ _
    (GaussianGammaRationalWendelBoundary.fraction_zero (Γ := Γ) one (le_refl _)).eqSymm
  have low := trans_weak _ _ _ _ _ _ left h.andE₁
  exact .andI
    (strict_transport _ _ _ _ _ _ _ _ q (cross_refl _ _ (fraction_location_regular N)) low)
    (weak_trans _ _ _ _ _ _ h.andE₂ (fraction_strict (rightNumerator N) M one one (mesh_positive N) (le_refl _)
      (by unfold lt; ipra_le 0 with eq)))

theorem offset_shift_cross (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (addF OF CF) locationF (addData N (leftPole N)) N := by
  have h := fraction_location_regular (Γ := Γ) N
  refine equivalent_of_envelope _ _ _ _ three
    (add_fast _ _ _ _ h (constant_regular _)) (location_regular N) (.allI ?_)
  let W := Syn.shift N
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let L := leftPole W
  let F := fraction (succ W) one
  have e : Δ ⊢[PRAAx] L ≐ qnegative F := qzero_add _ (qnegative_canonical F)
  have e' := qadd_congr (fraction_location_at (Γ := Δ) p W) ((constant_at p L).eqTrans e)
  have er := add_sample_error (Γ := Δ) OF CF W L p (fraction_location_regular W) (constant_regular L)
  have out := distance_congr (.eqRefl _) (e'.eqTrans (location_at p W).eqSymm) (.eqRefl _) (.eqRefl _) er
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNameArithmetic.subst_addData,
    subst_leftPole,Syn.shift,W,L,p,three,PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using out

private theorem right_pole_code (N : PTm n) : Γ ⊢[PRAAx]
    qadd (fraction one one) (leftPole N) ≐ rightPole N := by
  let a : PTm n := fraction one one
  let b := fraction (succ N) one
  let c := fraction N one
  have h : Γ ⊢[PRAAx] le one (succ N) := zero_lt_succ N
  have eg : Γ ⊢[PRAAx] LeanProofs.IPRA.PTm.monus (succ N) one ≐ N :=
    (congrMonus (show Γ ⊢[PRAAx] succ N ≐ N+one from by ipra_ring) (.eqRefl _)).eqTrans (add_monus _ _)
  have d : Γ ⊢[PRAAx] qsub b a ≐ c :=
    (GaussianEulerPositivePowerChartImageWeights.fraction_difference one (succ N) one (le_refl _) h).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ eg (.eqRefl _))
  have neg : Γ ⊢[PRAAx] qnegative (qsub b a) ≐ qnegative c :=
    (qzero_add _ (qnegative_canonical (qsub b a))).eqSymm.eqTrans
      ((qsub_congr (.eqRefl _) d).eqTrans (qzero_add _ (qnegative_canonical c)))
  exact (qadd_congr (.eqRefl _) (qzero_add _ (qnegative_canonical b))).eqTrans
    ((GaussianRationalDistanceOrder.reversed_difference b a).eqSymm.eqTrans
      (neg.eqTrans (qzero_add _ (qnegative_canonical c)).eqSymm))

private theorem constant_sum_as (a b c : PTm n) (h : Γ ⊢[PRAAx] qadd a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (addF CF CF) CF (addData a b) c :=
  cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross a b)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ h)

theorem strict_interior (N : PTm n) : Γ ⊢[PRAAx]
    strictOrder CF locationF (leftPole N) N ⋏ strictOrder locationF CF N (rightPole N) := by
  let L := leftPole N
  let R := rightPole N
  let P : PTm n := fraction one one
  have h := offset_interior (Γ := Γ) N
  have hc := constant_regular (Γ := Γ) L
  have ho := fraction_location_regular (Γ := Γ) N
  have loc := offset_shift_cross (Γ := Γ) N
  have left := add_right CF OF CF qzero N L (constant_regular _) ho hc h.andE₁
  have right := add_right OF CF CF N P L ho (constant_regular _) hc h.andE₂
  have l : Γ ⊢[PRAAx] crossEquivalent (addF CF CF) CF (addData qzero L) L :=
    constant_sum_as _ _ _ (qzero_add _ (qsub_canonical _ _))
  have r : Γ ⊢[PRAAx] crossEquivalent (addF CF CF) CF (addData P L) R :=
    constant_sum_as _ _ _ (right_pole_code N)
  exact .andI
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ l) loc left)
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ loc) r right)

theorem original_shifted_negative_gamma_location_interior_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (strictOrder CF locationF (leftPole (var 0)) (var 0) ⋏ strictOrder locationF CF (var 0) (rightPole (var 0))) :=
  closeUniv 1 (strict_interior _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationInterior
