import GowersSzemeredi.Definitions
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Universal relations of the scalar feature F(x,y)=xy on balanced
vertical-pair arrangements. `none` denotes the eliminated final pair.
The free horizontal coordinates determine its coordinate by the signs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def balancedFeatureRelation {I R : Type*} [Fintype I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (x : I → R)
    (y : Option I → R) (h : R) : R :=
  (∑ i, x i * ((u₀ (some i) + u₁ (some i)) * y (some i) + u₁ (some i) * h)) +
    (∑ i, sign i * x i) * ((u₀ none + u₁ none) * y none + u₁ none * h)

theorem balancedFeatureRelation_pair_test {I R : Type*}
    [Fintype I] [DecidableEq I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (i : I) :
    balancedFeatureRelation sign u₀ u₁ (Pi.single i 1) (Pi.single (some i) 1) 0 =
      u₀ (some i) + u₁ (some i) := by
  classical
  simp [balancedFeatureRelation, Pi.single_apply]

theorem balancedFeatureRelation_last_test {I R : Type*}
    [Fintype I] [DecidableEq I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (i : I) :
    balancedFeatureRelation sign u₀ u₁ (Pi.single i 1) (Pi.single none 1) 0 =
      sign i * (u₀ none + u₁ none) := by
  classical
  simp [balancedFeatureRelation, Pi.single_apply]

theorem balancedFeatureRelation_height_test {I R : Type*}
    [Fintype I] [DecidableEq I] [CommRing R]
    (sign : I → R) (u₀ u₁ : Option I → R) (i : I) :
    balancedFeatureRelation sign u₀ u₁ (Pi.single i 1) 0 1 =
      u₁ (some i) + sign i * u₁ none := by
  classical
  simp [balancedFeatureRelation, Pi.single_apply]

theorem balancedFeatureRelation_universal_iff {I R : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Field R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0) (u₀ u₁ : Option I → R) :
    (∀ x y h, balancedFeatureRelation sign u₀ u₁ x y h = 0) ↔
      ∃ c : R, u₀ none = c ∧ u₁ none = -c ∧
        (∀ i, u₀ (some i) = -(sign i * c)) ∧
        (∀ i, u₁ (some i) = sign i * c) := by
  classical
  constructor
  · intro hall
    have hpair (i : I) : u₀ (some i) + u₁ (some i) = 0 := by
      simpa only [balancedFeatureRelation_pair_test] using
        hall (Pi.single i 1) (Pi.single (some i) 1) 0
    have hlast : u₀ none + u₁ none = 0 := by
      let i : I := Classical.arbitrary I
      have ht : sign i * (u₀ none + u₁ none) = 0 := by
        simpa only [balancedFeatureRelation_last_test] using
          hall (Pi.single i 1) (Pi.single none 1) 0
      exact (mul_eq_zero.mp ht).resolve_left (hsign i)
    have hheight (i : I) : u₁ (some i) + sign i * u₁ none = 0 := by
      simpa only [balancedFeatureRelation_height_test] using hall (Pi.single i 1) 0 1
    refine ⟨-u₁ none, by linear_combination hlast, by ring, ?_, ?_⟩
    · intro i
      linear_combination hpair i - hheight i
    · intro i
      linear_combination hheight i
  · rintro ⟨c, h₀, h₁, h₀s, h₁s⟩ x y h
    simp only [balancedFeatureRelation, h₀, h₁, h₀s, h₁s,
      neg_add_cancel, add_neg_cancel, zero_mul, zero_add]
    rw [Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    ring

theorem balancedFeatureRelation_nonzero_witness {I R : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Field R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0) (u₀ u₁ : Option I → R)
    (hnot : ¬ ∃ c : R, u₀ none = c ∧ u₁ none = -c ∧
      (∀ i, u₀ (some i) = -(sign i * c)) ∧
      (∀ i, u₁ (some i) = sign i * c)) :
    ∃ x y h, balancedFeatureRelation sign u₀ u₁ x y h ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hnot ((balancedFeatureRelation_universal_iff sign hsign u₀ u₁).mp h)

end LeanProofs.GowersSzemeredi
