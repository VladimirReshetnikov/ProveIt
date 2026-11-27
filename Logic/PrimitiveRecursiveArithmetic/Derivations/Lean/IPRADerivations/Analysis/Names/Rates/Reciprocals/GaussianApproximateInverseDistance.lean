import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower
import IPRADerivations.Core.OrderCertificates

/-!
# Exact fractional inverse-distance constants with finite residuals

The original raw inverse candidates need not be canonical. Their exact
fractional bounds A/B are retained in the central product term. Only
the inverse-product residuals are multiplied by the coarse integer A.
All such residuals belong to an explicit auxiliary error coefficient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianApproximateInverseDistance

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def errorCost (A K L : PTm n) : PTm n := two*A*A+A*(K+L)
ipra_subst errorCost

theorem unit_product_recode (q : PTm n) : Γ ⊢[PRAAx] qmul q qone ≐ GaussianFastValueCut.recode q := by
  have rep := GaussianRationalHorner.qmul_represents q qone (rawGaussian q) ComplexLogarithmRemainder.oneCode
    (rawDen q) one (raw_den_positive (Γ := Γ) q) (le_refl one) (raw_represents q)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianFastValueCut.recode_canonical q) (raw_den_positive q) (hrv := GaussianFastValueCut.recode_represents q)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (by ipra_ring : Γ ⊢[PRAAx] rawDen q*one ≐ rawDen q) rep
  apply GaussianRootAlgebra.equal_of_values <;> simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
    GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring

theorem unit_product_distance (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    distanceBounded (qmul q qone) q zero U :=
  distance_congr (unit_product_recode q).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ zero one zero U (le_refl one) hU (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianFastValueCut.recode_distance q))

theorem multiply_distance (c u v A E F : PTm n) (hF : Γ ⊢[PRAAx] le one F)
    (hc : Γ ⊢[PRAAx] bounded c A one) (h : Γ ⊢[PRAAx] distanceBounded u v E F) : Γ ⊢[PRAAx]
    distanceBounded (qmul c u) (qmul c v) (A*E) F :=
  GaussianRationalRoundedPower.distance_mul_left_one hF hc h

theorem left_rearrange (i j q : PTm n) : Γ ⊢[PRAAx]
    qmul i (qmul q j) ≐ qmul (qmul i j) q :=
  (qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative q j)).eqTrans
    (GaussianReciprocalHorner.qmul_associative i j q).eqSymm

theorem right_rearrange (i j p : PTm n) : Γ ⊢[PRAAx]
    qmul j (qmul p i) ≐ qmul (qmul i j) p :=
  (left_rearrange j i p).eqTrans (qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative j i) (.eqRefl _))

/-- The central comparison retains the full (A/B)^2 factor. -/
theorem central_distance (p q i j A B E F : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hF : Γ ⊢[PRAAx] le one F) (hi : Γ ⊢[PRAAx] bounded i A B) (hj : Γ ⊢[PRAAx] bounded j A B)
    (hpq : Γ ⊢[PRAAx] distanceBounded p q E F) : Γ ⊢[PRAAx]
    distanceBounded (qmul i (qmul q j)) (qmul j (qmul p i)) (A*A*E) (B*B*F) := by
  have ij := GaussianRationalReciprocal.bounded_product i j A B A B hB hB hi hj
  have main := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (positive_product _ _ hB hB) hF ij
    (distance_symmetric _ _ _ _ hF hpq)
  exact distance_congr (left_rearrange i j q).eqSymm (right_rearrange i j p).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference (qmul i j) q p).eqSymm
      (.eqRefl _) (.eqRefl _) main)

/-- Finite residuals contribute only the displayed errorCost/U; A may be zero. -/
theorem finite_inverse_error (p q i j A B D N U K L : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hi : Γ ⊢[PRAAx] bounded i A B) (hj : Γ ⊢[PRAAx] bounded j A B)
    (hpq : Γ ⊢[PRAAx] distanceBounded p q (D*U+two*N) (N*U))
    (hpi : Γ ⊢[PRAAx] distanceBounded (qmul p i) qone K U)
    (hqj : Γ ⊢[PRAAx] distanceBounded (qmul q j) qone L U) : Γ ⊢[PRAAx]
    distanceBounded i j ((A*A*D)*U+errorCost A K L*(B*B*N)) ((B*B*N)*U) := by
  let Z := (B*B*N)*U
  have nz : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ (positive_product _ _ hB hB) hN) hU
  have ia := GaussianCoefficientNameBounds.bounded_radius_mono_den (le_refl one) hB hi
  have ja := GaussianCoefficientNameBounds.bounded_radius_mono_den (le_refl one) hB hj
  have left := distance_radius_mono _ _ _ _ (A*L*(B*B*N)) Z hU nz
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
    (multiply_distance i qone (qmul q j) A L U hU ia (distance_symmetric _ _ _ _ hU hqj))
  have middle : Γ ⊢[PRAAx] distanceBounded (qmul i (qmul q j)) (qmul j (qmul p i)) (A*A*(D*U+two*N)) Z :=
    distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (by dsimp only [Z]; ipra_ring)
      (central_distance p q i j A B _ _ hB (positive_product _ _ hN hU) hi hj hpq)
  have right := distance_radius_mono _ _ _ _ (A*K*(B*B*N)) Z hU nz
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) (multiply_distance j (qmul p i) qone A K U hU ja hpi)
  have chain := distance_triangle_same _ _ _ _ _ _ nz
    (distance_triangle_same _ _ _ _ _ _ nz
      (distance_triangle_same _ _ _ _ _ _ nz
        (distance_symmetric _ _ _ _ nz (unit_product_distance i Z nz)) left) middle)
    (distance_triangle_same _ _ _ _ _ _ nz right (unit_product_distance j Z nz))
  apply distance_radius_mono _ _ _ _ _ _ nz nz _ chain
  have bb := le_mul_mono hB hB
  dsimp only [Z]
  unfold errorCost
  ipra_le 2*𝔞 A*𝔞 A*𝔞 N*𝔞 ((B*B*N)*U)*sl bb

theorem original_fractional_approximate_inverse_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (le one (var 5) ⟶ le one (var 7) ⟶ le one (var 8) ⟶ bounded (var 2) (var 4) (var 5) ⟶
      bounded (var 3) (var 4) (var 5) ⟶ distanceBounded (var 0) (var 1) (var 6*var 8+two*var 7) (var 7*var 8) ⟶
      distanceBounded (qmul (var 0) (var 2)) qone (var 9) (var 8) ⟶ distanceBounded (qmul (var 1) (var 3)) qone (var 10) (var 8) ⟶
      distanceBounded (var 2) (var 3) ((var 4*var 4*var 6)*var 8+errorCost (var 4) (var 9) (var 10)*(var 5*var 5*var 7)) ((var 5*var 5*var 7)*var 8)) := by
  apply closeUniv 11
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact finite_inverse_error _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianApproximateInverseDistance
