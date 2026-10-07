import GowersSzemeredi.Proofs13FeaturePolynomial

/-! The polynomial parameterization agrees with the scalar feature xy
on the actual lower and upper vertices of balanced vertical pairs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def balancedHorizontal {I R : Type*} [Fintype I] [CommRing R]
    (sign x : I → R) : Option I → R
  | none => ∑ i, sign i * x i
  | some i => x i

def balancedFeatureVertex {I R : Type*} [Fintype I] [CommRing R]
    (sign x : I → R) (y : Option I → R) (h : R) (v : Option I × Bool) : R × R :=
  (balancedHorizontal sign x v.1, y v.1 + if v.2 then h else 0)

def balancedRelationCoefficient {I R : Type*} (u₀ u₁ : Option I → R)
    (v : Option I × Bool) : R := if v.2 then u₁ v.1 else u₀ v.1

theorem balancedFeatureVertex_pair_relation {I R : Type*} [Fintype I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (x : I → R)
    (y : Option I → R) (h : R) :
    (∑ j : Option I,
      (u₀ j * ((balancedFeatureVertex sign x y h (j, false)).1 *
        (balancedFeatureVertex sign x y h (j, false)).2) +
      u₁ j * ((balancedFeatureVertex sign x y h (j, true)).1 *
        (balancedFeatureVertex sign x y h (j, true)).2))) =
      balancedFeatureRelation sign u₀ u₁ x y h := by
  classical
  have ht (j : Option I) :
      u₀ j * ((balancedFeatureVertex sign x y h (j, false)).1 *
        (balancedFeatureVertex sign x y h (j, false)).2) +
      u₁ j * ((balancedFeatureVertex sign x y h (j, true)).1 *
        (balancedFeatureVertex sign x y h (j, true)).2) =
      balancedHorizontal sign x j * ((u₀ j + u₁ j) * y j + u₁ j * h) := by
    simp only [balancedFeatureVertex, Bool.false_eq_true, if_false, if_true, add_zero]
    ring
  simp_rw [ht]
  rw [Fintype.sum_option]
  simp only [balancedHorizontal, balancedFeatureRelation]
  exact add_comm _ _

theorem balancedFeatureVertex_relation {I R : Type*} [Fintype I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (x : I → R)
    (y : Option I → R) (h : R) :
    (∑ v : Option I × Bool, balancedRelationCoefficient u₀ u₁ v *
      ((balancedFeatureVertex sign x y h v).1 * (balancedFeatureVertex sign x y h v).2)) =
      balancedFeatureRelation sign u₀ u₁ x y h := by
  classical
  rw [Fintype.sum_prod_type]
  simpa only [Fintype.sum_bool, balancedRelationCoefficient, Bool.false_eq_true,
    if_false, if_true, add_comm] using
    balancedFeatureVertex_pair_relation sign u₀ u₁ x y h

theorem balancedFeatureVertex_polynomial {I R : Type*} [Fintype I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (x : I → R)
    (y : Option I → R) (h : R) :
    (∑ v : Option I × Bool, balancedRelationCoefficient u₀ u₁ v *
      ((balancedFeatureVertex sign x y h v).1 * (balancedFeatureVertex sign x y h v).2)) =
      MvPolynomial.eval (balancedFeatureAssignment x y h)
        (balancedFeaturePolynomial sign u₀ u₁) := by
  rw [balancedFeatureVertex_relation, balancedFeaturePolynomial_eval]

theorem balancedHorizontal_balance {I R : Type*} [Fintype I] [CommRing R]
    (sign x : I → R) :
    (∑ i, sign i * balancedHorizontal sign x (some i)) - balancedHorizontal sign x none = 0 := by
  simp [balancedHorizontal]

end LeanProofs.GowersSzemeredi
