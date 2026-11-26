import IPRADerivations.Analysis.Gamma.GaussianGammaRationalWendelUniform
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.Names.GaussianNamedStrictOrderDifference

/-!
# Lift a frozen comparison with a fixed margin to real names

Independent rates replace both rational evaluations by the original
named observations. The additive margin is retained in the named
order. A positive margin then gives strict order constructively.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedComparisonTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (three add_sample_error sum_right_error zeroF zero_fast add_zero_left)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr distance_symmetric)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem t_equal (F H : PR 2) (p x y : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F H x y one (unit p)) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 F p x) (ap2 H p y) three (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hU) hU ?_
    (rate_at F H x y one (unit p) p p h)
  apply le_of_eq_add (d := zero)
  unfold rateNumerator rateDenominator three
  ipra_ring

theorem diagonal (F G H : PR 2) (p W x y a b m C : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hW : Γ ⊢[PRAAx] le (unit p) W)
    (hl : Γ ⊢[PRAAx] independentRate F H x a one (unit p))
    (hr : Γ ⊢[PRAAx] independentRate G H y b one (unit p))
    (hm : Γ ⊢[PRAAx] upper (fstT (qadd m (ap2 H p a))) (fstT (ap2 H p b))
      (rateNumerator C W p p) (rateDenominator W p p)) : Γ ⊢[PRAAx]
    upper (fstT (ap2 (addF constantF F) p (addData m x))) (fstT (ap2 G p y)) (C+num 11) (unit p) := by
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have wpos := le_trans hu hW
  have left := t_equal F H p x a hl
  have right := t_equal G H p y b hr
  have actual := add_sample_error constantF F m x p (constant_regular m) hf
  have l₁ := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hu
    (distance_congr (.eqRefl _) (qadd_congr (constant_at p m) (.eqRefl _)) (.eqRefl _) (.eqRefl _) actual))
  have l₂ := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hu
    (sum_right_error m _ _ _ _ hu left))
  have r := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hu
    (distance_symmetric _ _ _ _ hu right))
  have mid : Γ ⊢[PRAAx] upper (fstT (qadd m (ap2 H p a))) (fstT (ap2 H p b)) (C+two) U := by
    apply upper_mono _ _ _ _ _ _ (denominator_positive _ _ _ wpos) hm
    unfold rateNumerator rateDenominator U
    ipra_le 𝔞(C)*𝔞(unit p)^2*sl hW
  have hUU := positive_product _ _ hu hu
  have leftJoin := upper_triangle _ _ _ _ _ _ _ l₁ l₂
  have join := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ leftJoin mid) r
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hUU hu) hu) join
  apply le_of_eq_add (d := zero)
  unfold three
  ipra_ring

theorem zero_left_cross (F : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] crossEquivalent (addF constantF F) F (addData qzero x) x := by
  have hz := GaussianGammaRationalWendelUniform.zero_constant (Γ := Γ) x
  have moved := GaussianNamedGammaHalfShift.add_cross constantF zeroF F F qzero x x x
    (constant_regular _) (zero_fast _) hf hf (cross_symm _ _ _ _ hz) (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ moved (add_zero_left F x hf)

theorem order_from_zero (F G : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] realOrder (addF constantF F) G (addData qzero x) y) :
    Γ ⊢[PRAAx] realOrder F G x y :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (zero_left_cross F x hf)) (cross_refl _ _ hg) h

theorem strict_from_margin (F G : PR 2) (x y m : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x)
    (hp : Γ ⊢[PRAAx] strictOrder constantF constantF qzero m)
    (h : Γ ⊢[PRAAx] realOrder (addF constantF F) G (addData m x) y) :
    Γ ⊢[PRAAx] strictOrder F G x y := by
  have gap := GaussianNamedStrictOrderDifference.add_right constantF constantF F qzero m x
    (constant_regular _) (constant_regular _) hf hp
  have lift := strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (zero_left_cross F x hf))
    (cross_refl _ _ (GaussianNameArithmetic.add_fast _ _ _ _ (constant_regular m) hf)) gap
  exact GaussianNamedStrictOrderDifference.trans_weak _ _ _ _ _ _ lift h

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedComparisonTransfer
