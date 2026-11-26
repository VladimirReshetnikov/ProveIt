import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaHarmonicCells
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Finite scalar order on frozen regular real names

An ordinary named order gives a comparison between literal rational
points which independently approximate the two names. The finite
comparison pays the sum of the two input errors, with the observation
allowances removed. Positive fraction encodings clear this bound
without relying on their reduced denominators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFrozenScalarOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono positive_cancel)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem own_rate (f : PR 2) (x s k q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hk : Γ ⊢[PRAAx] le s k) (hq : Γ ⊢[PRAAx] ap2 f k x ≐ q) :
    Γ ⊢[PRAAx] independentRate f constantF x q one (unit s) := by
  have grow := GaussianExponentialReference.unit_monotone hk
  have raw : Γ ⊢[PRAAx] independentRate f constantF x (ap2 f k x) one (unit s) :=
    GaussianNamedRateRadius.weaken f constantF x (ap2 f k x) one (unit k) one (unit s)
      (unit_positive k) (unit_positive s) (le_congr (one_mul _).eqSymm (one_mul _).eqSymm grow)
      (GaussianSignedNameExponentialOrder.own_sample_rate f x k hf)
  exact GaussianNamedRateTransport.transport f constantF f constantF x (ap2 f k x) x q one (unit s)
    (unit_positive s) raw (GaussianNameEquivalence.cross_refl f x hf)
    (GaussianSignedNameExponentialOrder.constant_equal_cross q (ap2 f k x) hq.eqSymm)

private theorem order_slack (f g : PR 2) (x y q r A B D t : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] independentRate constantF f q x A D)
    (hg : Γ ⊢[PRAAx] independentRate g constantF y r B D)
    (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upperSlack (fstT q) (fstT r) (A+B) D (num 6) t := by
  have hRate := denominator_positive D t t hD
  have hObs := positive_product _ _ (unit_positive (Γ := Γ) t) (unit_positive t)
  have left := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hRate
    (distance_congr (constant_at t q) (.eqRefl _) (.eqRefl _) (.eqRefl _) (rate_at constantF f q x A D t t hf)))
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hRate
    (distance_congr (.eqRefl _) (constant_at t r) (.eqRefl _) (.eqRefl _) (rate_at g constantF y r B D t t hg)))
  have middle := real_order_at f g x y t t h
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left middle) right
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hRate hObs) hRate) joined
  exact le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)

theorem finite_order (f g : PR 2) (x y q r A B D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] independentRate f constantF x q A D)
    (hg : Γ ⊢[PRAAx] independentRate g constantF y r B D)
    (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upper (fstT q) (fstT r) (A+B) D :=
  remove_upper_slack _ _ _ _ (num 6)
    (order_slack f g x y q r A B D (precision (fstT q) (fstT r) D (num 6)) hD
      (GaussianNamedRateComposition.symmetric f constantF x q A D hD hf) hg h)

theorem clear_fraction_order (a b c d E D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c d)) E D) :
    Γ ⊢[PRAAx] le (D*(a*d)) (D*(c*b)+E*b*d) := by
  let l := RationalRepresentedUpper.left (ZT.ofNat a) d D
  let r := RationalRepresentedUpper.right (ZT.ofNat c) b d E D
  have order := RationalRepresentedUpper.to_signed _ _ _ _ _ _ _ _
    (GaussianGammaDigammaHarmonicCells.point_fraction_represents a b hb)
    (GaussianGammaDigammaHarmonicCells.point_fraction_represents c d hd) h
  have eq := zle_toZ order
  apply le_of_eq_add (d := PolynomialBisection.slack l r)
  apply deriveNat
  simp only [l,r,RationalRepresentedUpper.left,RationalRepresentedUpper.right,PolynomialBisection.slack,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at eq ⊢
  simp only [Q.mk_mul,Q.mk_add,map_mul,map_add] at eq ⊢
  linear_combination -eq

theorem clear_common_chart (a c b e E D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] b ≐ e*D)
    (h : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c b)) E D) :
    Γ ⊢[PRAAx] le a (c+E*e) := by
  have orig := clear_fraction_order a b c b E D hb hb h
  have out : Γ ⊢[PRAAx] le (D*a) (D*c+E*b) :=
    positive_cancel (c := b) hb (le_congr (by ipra_ring) (by ipra_ring) orig)
  have scale := congrMul (.eqRefl E) he
  exact positive_cancel (c := D) hD
    (le_congr (.eqRefl _) ((congrAdd (.eqRefl _) scale).eqTrans (by ipra_ring)) out)

theorem actual_named_frozen_scalar_order_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((le one (var 6) ⋏ realOrder f g (var 0) (var 1)) ⋏
        (independentRate f constantF (var 0) (var 2) (var 4) (var 6) ⋏
          independentRate g constantF (var 1) (var 3) (var 5) (var 6)) ⟶
          upper (fstT (var 2)) (fstT (var 3)) (var 4+var 5) (var 6)) :=
  closeUniv 7 (.impI (finite_order f g _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂ Prf.hyp0.andE₁.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedFrozenScalarOrder
