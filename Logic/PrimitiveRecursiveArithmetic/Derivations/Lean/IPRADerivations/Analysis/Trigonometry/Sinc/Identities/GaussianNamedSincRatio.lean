import IPRADerivations.Analysis.Trigonometry.Sinc.Series.GaussianNamedSincQuadraticBounds
import IPRADerivations.Analysis.Names.Arithmetic.GaussianBoundedInverseApartness

/-!
# Sinc ratio error on two small disks

These estimates use independently requested observations of the
original sinc names. The denominator is bounded away from zero on
the unit disk, and the error in the squared quotient is bounded by
six times the sum of the squared argument radii.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSincRatio

open_ipra
open GaussianNamedSinc (nameF data)
open GaussianNamedSincQuadraticBounds (observationBound quadratic_bound square_quadratic_bound)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalReciprocal (qone reciprocal)
open GaussianRationalLowerBounds (lower lower_congr product_lower reciprocal_identity_of_lower inverse_bound)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianBoundedInverseApartness (lower_near_one)
open GaussianReconstructionRoots (distance_triangle)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (f : PR 2) (R x p : PTm n) : PTm n := ap2 (nameF f) p (data f R x)
def square (f : PR 2) (R x p : PTm n) : PTm n := qmul (value f R x p) (value f R x p)

def ratio (f g : PR 2) (R x S y p q : PTm n) : PTm n :=
  qmul (reciprocal (square g S y q)) (square f R x p)

ipra_subst value
ipra_subst square
ipra_subst ratio

theorem value_lower (f : PR 2) (R x A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] lower (value f R x p) one two := by
  apply lower_near_one
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB))
    (le_succ_self one) (le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl two) (le_mul_mono hAB hAB))) (quadratic_bound f R x A B p hB hAB h)

theorem square_lower (f : PR 2) (R x A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] lower (square f R x p) one (num 4) :=
  lower_congr (.eqRefl _) (one_mul one) (by ipra_ring)
    (product_lower _ _ one two one two (le_succ_self one) (le_succ_self one)
      (value_lower f R x A B p hB hAB h) (value_lower f R x A B p hB hAB h))

theorem ratio_error (f g : PR 2) (R x S y A B C D p q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (hD : Γ ⊢[PRAAx] le one D) (hCD : Γ ⊢[PRAAx] le C D)
    (hf : Γ ⊢[PRAAx] observationBound f x A B) (hg : Γ ⊢[PRAAx] observationBound g y C D) :
    Γ ⊢[PRAAx] distanceBounded (ratio f g R x S y p q) qone
      (num 6*((A*A)*(D*D)+(C*C)*(B*B))) ((B*B)*(D*D)) := by
  let u := square f R x p
  let v := square g S y q
  let E := two*(B*B)
  let F := two*(D*D)
  let M := num 3*(A*A)
  let N := num 3*(C*C)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB)
  have hF : Γ ⊢[PRAAx] le one F := positive_product _ _ (le_succ_self one) (positive_product _ _ hD hD)
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have low := square_lower g S y C D q hD hCD hg
  have d : Γ ⊢[PRAAx] distanceBounded u v (M*F+N*E) (E*F) :=
    distance_triangle u qone v M E N F hE hF (square_quadratic_bound f R x A B p hB hAB hf)
      (distance_symmetric _ _ _ _ hF (square_quadratic_bound g S y C D q hD hCD hg))
  have hrec := inverse_bound v one (num 4) (le_refl one) h4 low
  have recId := (GaussianRationalPowerAlgebra.qmul_commutative v (reciprocal v)).eqSymm.eqTrans
    (reciprocal_identity_of_lower v one (num 4) (le_refl one) h4 low)
  have hEF := positive_product E F hE hF
  have raw := distance_congr (.eqRefl _) recId (.eqRefl _) (.eqRefl _)
    (multiply_distance (reciprocal v) u v (num 4) (M*F+N*E) (E*F) hEF hrec d)
  exact distance_radius_mono _ _ _ _ _ _ hEF
    (positive_product _ _ (positive_product _ _ hB hB) (positive_product _ _ hD hD))
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [M,N,E,F]; ipra_ring)) raw

theorem actual_named_sinc_ratio_bound_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((le one (var 4) ⋏ le (var 5) (var 4)) ⟶ (le one (var 2) ⋏ le (var 3) (var 2)) ⟶
        observationBound f (var 8) (var 5) (var 4) ⟶ observationBound g (var 6) (var 3) (var 2) ⟶
        distanceBounded (ratio f g (var 9) (var 8) (var 7) (var 6) (var 1) (var 0)) qone
          (num 6*((var 5*var 5)*(var 2*var 2)+(var 3*var 3)*(var 4*var 4)))
          ((var 4*var 4)*(var 2*var 2))) :=
  closeUniv 10 (.impI (.impI (.impI (.impI
    (ratio_error f g _ _ _ _ _ _ _ _ _ _ hyp2.wk.andE₁ hyp2.wk.andE₂ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianNamedSincRatio
