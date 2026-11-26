import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaStrongLogConvexityAlgebra
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsStrictOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartTimeOrder

/-!
# Translation and signed differences of strictly ordered Gaussian names

Common additions preserve strict real order since they reflect the reverse
weak order. These are exact equivalences of the original normalized names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianNamedStrictOrderDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaStrongLogConvexityAlgebra (cancel_common add_negative_front)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianNamedDifference (nameF data)
open Syn

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem add_left (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z)
    (h : Γ ⊢[PRAAx] strictOrder F H x y) :
    Γ ⊢[PRAAx] strictOrder (addF J F) (addF J H) (addData z x) (addData z y) :=
  .andI (add_order J J F H z z x y (order_refl _ _ hj) h.andE₁)
    (.impI (h.andE₂.wk.impE (cancel_common J H F z y x hj.wk hh.wk hf.wk Prf.hyp0)))

theorem add_right (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z)
    (h : Γ ⊢[PRAAx] strictOrder F H x y) :
    Γ ⊢[PRAAx] strictOrder (addF F J) (addF H J) (addData x z) (addData y z) :=
  strict_transport _ _ _ _ _ _ _ _ (add_commutative F J x z hf hj)
    (add_commutative J H z y hj hh) (add_left F H J x y z hf hh hj h)

theorem sum_sub_right (F H : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hh : Γ ⊢[PRAAx] pointCN H y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (addF F H) H) F (data (addData x y) y) x := by
  let N := negativeF H
  let Y := negativeData y
  have hY := negative_fast H y hh
  have a := add_commutative (addF F H) N (addData x y) Y (add_fast _ _ _ _ hf hh) hY
  have b := add_cross N N (addF F H) (addF H F) Y Y (addData x y) (addData y x)
    hY hY (add_fast _ _ _ _ hf hh) (add_fast _ _ _ _ hh hf) (cross_refl _ _ hY)
    (add_commutative F H x y hf hh)
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b (add_negative_front H F y x hh hf))

theorem difference_lt (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z)
    (h : Γ ⊢[PRAAx] strictOrder F (addF H J) x (addData y z)) :
    Γ ⊢[PRAAx] strictOrder (nameF F J) H (data x z) y := by
  have a := add_right F (addF H J) (negativeF J) x (addData y z) (negativeData z)
    hf (add_fast _ _ _ _ hh hj) (negative_fast _ _ hj) h
  exact strict_transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianNamedDifference.name_regular _ _ _ _ hf hj))
    (sum_sub_right H J y z hh hj) a

theorem lt_difference (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z)
    (h : Γ ⊢[PRAAx] strictOrder (addF F J) H (addData x z) y) :
    Γ ⊢[PRAAx] strictOrder F (nameF H J) x (data y z) := by
  have a := add_right (addF F J) H (negativeF J) (addData x z) y (negativeData z)
    (add_fast _ _ _ _ hf hj) hh (negative_fast _ _ hj) h
  exact strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (sum_sub_right F J x z hf hj))
    (cross_refl _ _ (GaussianNamedDifference.name_regular _ _ _ _ hh hj)) a

theorem trans_weak (F H J : PR 2) (x y z : PTm n) (h : Γ ⊢[PRAAx] strictOrder F H x y)
    (j : Γ ⊢[PRAAx] realOrder H J y z) : Γ ⊢[PRAAx] strictOrder F J x z :=
  .andI (order_trans _ _ _ _ _ _ h.andE₁ j)
    (.impI (h.andE₂.wk.impE (order_trans _ _ _ _ _ _ j.wk Prf.hyp0)))

theorem weak_trans (F H J : PR 2) (x y z : PTm n) (h : Γ ⊢[PRAAx] realOrder F H x y)
    (j : Γ ⊢[PRAAx] strictOrder H J y z) : Γ ⊢[PRAAx] strictOrder F J x z :=
  .andI (order_trans _ _ _ _ _ _ h j.andE₁)
    (.impI (j.andE₂.wk.impE (order_trans _ _ _ _ _ _ Prf.hyp0 h.wk)))

end LeanProofs.IPRA.Analysis.GaussianNamedStrictOrderDifference
