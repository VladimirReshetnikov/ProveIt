import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveExponentialOrder
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalUpperAddition

/-!
# Signed comparison for an original compact Euler prefix

The remainder's signed lower bound suffices to compare the real prefix
with the whole interval. The finite proof retains the original rounded
addition and the two independent observations of the addition identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteLowerPrefixSigned

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (canonical positive_product qadd qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_two_errors_same distance_symmetric distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_of_radius upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem extend_bound (x y A H U L M : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper x y L U)
    (hy : Γ ⊢[PRAAx] upper y (fstT qzero) (A*U+M*H) (H*U)) : Γ ⊢[PRAAx]
    upper x (fstT qzero) (A*U+(L+M)*H) (H*U) := by
  have joined := upper_triangle _ _ _ _ _ _ _ h hy
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hU (positive_product _ _ hH hU)) joined
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _))

theorem remainder_inclusion (x y U : PTm n) (hx : Γ ⊢[PRAAx] canonical x)
    (hy : Γ ⊢[PRAAx] upper (fstT qzero) (fstT y) one U) : Γ ⊢[PRAAx]
    upper (fstT x) (fstT (qadd x y)) one U := by
  have added := RationalUpperAddition.add_upper_order_right hy (RationalArgmin.reflexive (fstT x))
  have empty := (RationalGaussianRealPart.real_add qzero x).eqSymm.eqTrans
    (congrFst (GaussianRationalSyntheticDivision.qzero_add x hx))
  have sum := (RationalGaussianRealPart.real_add (Γ := Γ) y x).eqSymm.eqTrans
    (congrFst (GaussianReciprocalHorner.qadd_commutative y x))
  exact upper_congr empty sum (.eqRefl _) (.eqRefl _) added

theorem rounded_sum_distance (F : PR 2) (t x y : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN F y) : Γ ⊢[PRAAx]
    distanceBounded (qadd (ap2 F t x) (ap2 F t y)) (ap2 (addF F F) t (addData x y)) (num 3) (unit t) := by
  have hU := unit_positive (Γ := Γ) t
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_symmetric _ _ _ _ hU (GaussianNameRingLaws.add_sample_error F F x y t hx hy))

theorem prefix_bound (F : PR 2) (t x y w A H : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN F y)
    (hc : Γ ⊢[PRAAx] canonical (ap2 F t x))
    (hp : Γ ⊢[PRAAx] upper (fstT qzero) (fstT (ap2 F t y)) one (unit t))
    (hw : Γ ⊢[PRAAx] bounded (ap2 F t w) (A*unit t+H) (H*unit t))
    (hadd : Γ ⊢[PRAAx] crossEquivalent (addF F F) F (addData x y) w) : Γ ⊢[PRAAx]
    upper (fstT (ap2 F t x)) (fstT qzero) (A*unit t+num 7*H) (H*unit t) := by
  let U := unit t
  let X := ap2 F t x
  let Y := ap2 F t y
  let W := ap2 F t w
  let Z := qadd X Y
  let S := ap2 (addF F F) t (addData x y)
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one (H*U) := positive_product _ _ hH hU
  have step : Γ ⊢[PRAAx] distanceBounded S W two U :=
    distance_two_errors_same hU (cross_at _ _ _ _ t t hadd)
  have via := distance_triangle_same Z S W (num 3) two U hU (rounded_sum_distance F t x y hx hy) step
  have via' : Γ ⊢[PRAAx] distanceBounded Z W (num 5) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) via
  have first := remainder_inclusion X Y U hc hp
  have middle := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hU via')
  have last := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD
    ((GaussianReconstructionRoots.distance_zero_iff W _ _ hD).iffMpr hw))
  have joined := extend_bound _ _ A H U (num 5) one hH hU middle
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) last)
  exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (extend_bound _ _ A H U one (num 5+one) hH hU first joined)

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteLowerPrefixSigned
