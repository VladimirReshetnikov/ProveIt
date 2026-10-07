import GowersSzemeredi.Proofs13FeatureZeroCount
import GowersSzemeredi.Proofs13FeatureVertices
import GowersSzemeredi.Proofs13FejerRelations

/-! Encode every difference of two kernel frequencies in a box of size
2L. Counting box vectors rather than pairs avoids a quadratic loss in L.
No injectivity of the box into the field is required for the union bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def fejerCoefficientBoxIndex {L : Nat} (v : Fin L × Fin L) : Fin (2 * L) :=
  ⟨v.1.val + L - v.2.val, by have h₁ := v.1.isLt; have h₂ := v.2.isLt; omega⟩

def fejerBoxCoefficient {N L : Nat} (a : Fin (2 * L)) : ZMod N := (a.val : ZMod N) - L

theorem fejerCoefficientBox_difference {N L : Nat} (v : Fin L × Fin L) :
    fejerBoxCoefficient (N := N) (fejerCoefficientBoxIndex v) =
      ((v.1 : Nat) : ZMod N) - ((v.2 : Nat) : ZMod N) := by
  have h : v.2.val ≤ v.1.val + L := by have hv := v.2.isLt; omega
  simp only [fejerBoxCoefficient, fejerCoefficientBoxIndex, Nat.cast_sub h, Nat.cast_add]
  ring

def fejerFeatureExceptional {N L : Nat} {I : Type*} [Fintype I]
    (sign : I → ZMod N) (z : BalancedFeatureVariable I → ZMod N) : Prop :=
  ∃ a : (Option I × Bool) → Fin (2 * L),
    let u₀ := fun j => fejerBoxCoefficient (a (j, false))
    let u₁ := fun j => fejerBoxCoefficient (a (j, true))
    balancedFeaturePolynomial sign u₀ u₁ ≠ 0 ∧
      MvPolynomial.eval z (balancedFeaturePolynomial sign u₀ u₁) = 0

theorem fejerFeatureExceptional_count {N L : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (sign : I → ZMod N) (hsign : ∀ i, sign i ≠ 0) :
    countWhere (fejerFeatureExceptional (L := L) sign) ≤
      (2 * L) ^ (2 * Fintype.card I + 2) * (2 * N ^ (2 * Fintype.card I + 1)) := by
  classical
  let u₀ (a : (Option I × Bool) → Fin (2 * L)) := fun j => fejerBoxCoefficient (N := N) (a (j, false))
  let u₁ (a : (Option I × Bool) → Fin (2 * L)) := fun j => fejerBoxCoefficient (N := N) (a (j, true))
  let S := Finset.univ.filter (fun a => balancedFeaturePolynomial sign (u₀ a) (u₁ a) ≠ 0)
  have hnot : ∀ a ∈ S, ¬ ∃ c : ZMod N, u₀ a none = c ∧ u₁ a none = -c ∧
      (∀ i, u₀ a (some i) = -(sign i * c)) ∧ (∀ i, u₁ a (some i) = sign i * c) := by
    intro a ha hc
    exact (Finset.mem_filter.mp ha).2
      ((balancedFeaturePolynomial_eq_zero_iff sign hsign (u₀ a) (u₁ a)).mpr hc)
  have h := balancedFeaturePolynomial_exceptional_count sign hsign S u₀ u₁ hnot
  have heq : (fun z => ∃ a ∈ S, MvPolynomial.eval z (balancedFeaturePolynomial sign (u₀ a) (u₁ a)) = 0) =
      fejerFeatureExceptional (L := L) sign := by
    funext z
    simp [S, fejerFeatureExceptional, u₀, u₁]
  rw [heq, ZMod.card] at h
  have hc : S.card ≤ (2 * L) ^ (2 * Fintype.card I + 2) := by
    calc
      S.card ≤ Fintype.card ((Option I × Bool) → Fin (2 * L)) := Finset.card_le_univ _
      _ = _ := by
        simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
          Fintype.card_option, Fintype.card_bool]
        congr 1
        omega
  exact h.trans (Nat.mul_le_mul_right _ hc)

theorem fejerFeatureExceptional_count_32 {N L : Nat} [NeZero N] [Fact N.Prime]
    (sign : Fin 15 → ZMod N) (hsign : ∀ i, sign i ≠ 0) :
    countWhere (fejerFeatureExceptional (L := L) sign) ≤ (2 * L) ^ 32 * (2 * N ^ 31) := by
  simpa using fejerFeatureExceptional_count (L := L) sign hsign

end LeanProofs.GowersSzemeredi
