import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# Uniform same-clock readback of the original normalized product

Use certified bounds for the actual factor observations. The computed
normalization clock may depend on their codes, but the error bound
depends only on the two certified radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedProductObservationBound

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiplyRaw)
open GaussianNameEquivalence (point_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem late_observation (f : PR 2) (x p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hp : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] distanceBounded (ap2 f q x) (ap2 f p x) two (unit p) := by
  have up := unit_positive (Γ := Γ) p
  have uq := unit_positive (Γ := Γ) q
  have order := GaussianExponentialReference.unit_monotone hp
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ uq up) up
    (le_congr (.eqRefl _) (by ipra_ring)
      (mul_le_mul_right (unit p) (add_le_add₂ (le_refl (unit q)) order)))
    (point_at f x q p hf)

theorem sample_error (f g : PR 2) (x y p A B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hA : Γ ⊢[PRAAx] pointBounds f A x) (hB : Γ ⊢[PRAAx] pointBounds g B y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF f g) p (multiplyData f g x y))
      (qmul (ap2 f p x) (ap2 g p y)) (two*(A+B)) (unit p) := by
  let q := exponent (multiplyModulus f g x y) p
  have pq : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have left := late_observation f x p q hf pq
  have right := late_observation g y p q hg pq
  have gy : Γ ⊢[PRAAx] bounded (ap2 g q y) B one := by simpa [pointBounds] using hB.allE q
  have fx : Γ ⊢[PRAAx] bounded (ap2 f p x) A one := by simpa [pointBounds] using hA.allE p
  have product := GaussianNameArithmetic.product_distance (ap2 f q x) (ap2 f p x)
    (ap2 g q y) (ap2 g p y) two two (unit p) B A (unit_positive p) left right gy fx
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) f g x y p).eqTrans
    (GaussianExponentialReference.recode_fixed (multiplyRaw f g q x y) (qmul_canonical _ _))
  exact distance_congr read.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) product

theorem actual_uniform_product_observation_error_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (((pointCN f (var 0) ⋏ pointCN g (var 1)) ⋏ (pointBounds f (var 3) (var 0) ⋏ pointBounds g (var 4) (var 1))) ⟶
      distanceBounded (ap2 (multiplyF f g) (var 2) (multiplyData f g (var 0) (var 1)))
        (qmul (ap2 f (var 2) (var 0)) (ap2 g (var 2) (var 1)))
        (two*(var 3+var 4)) (unit (var 2))) :=
  closeUniv 5 (.impI (sample_error f g _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedProductObservationBound
