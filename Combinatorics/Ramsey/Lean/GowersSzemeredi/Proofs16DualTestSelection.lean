import GowersSzemeredi.Proofs16LocalModelTests

/-! Select one test which retains many vertices and detects many models
from uniform pairwise test counts. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

theorem dual_test_selection {X J Y : Type*} (A : Finset X) (I : Finset J) (M : Finset Y)
    (E : X → Y → Prop) (D : J → Y → Prop) [DecidableRel E] [DecidableRel D] {beta : Real}
    (hA : A.Nonempty) (hI : I.Nonempty) (hM : M.Nonempty)
    (hcount : ∀ x ∈ A, ∀ j ∈ I,
      beta*M.card ≤ ((M.filter (fun y => E x y ∧ D j y)).card : Real)) :
    ∃ y ∈ M, beta*A.card ≤ ((A.filter (fun x => E x y)).card : Real) ∧
      beta*I.card ≤ ((I.filter (fun j => D j y)).card : Real) := by
  let a := fun y => (A.filter (fun x => E x y)).card
  let b := fun y => (I.filter (fun j => D j y)).card
  have hsumN : ∑ y ∈ M, a y*b y =
      ∑ x ∈ A, ∑ j ∈ I, (M.filter (fun y => E x y ∧ D j y)).card := by
    simp only [a,b,Finset.card_filter,Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro y _
    by_cases he : E x y <;> by_cases hd : D j y <;> simp [he,hd]
  have hsum : ∑ y ∈ M, ((a y : Real)*b y) =
      ∑ x ∈ A, ∑ j ∈ I, ((M.filter (fun y => E x y ∧ D j y)).card : Real) := by
    exact_mod_cast hsumN
  have havg : (∑ _y ∈ M, beta*(A.card : Real)*I.card) ≤ ∑ y ∈ M, ((a y : Real)*b y) := by
    rw [hsum]
    calc _ = ∑ _x ∈ A, ∑ _j ∈ I, beta*M.card := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j hj => hcount x hx j hj
  obtain ⟨y,hy,hprod⟩ := Finset.exists_le_of_sum_le hM havg
  have ha : (a y : Real) ≤ A.card := by exact_mod_cast Finset.card_filter_le A (fun x => E x y)
  have hb : (b y : Real) ≤ I.card := by exact_mod_cast Finset.card_filter_le I (fun j => D j y)
  have hAp : (0 : Real) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hIp : (0 : Real) < I.card := by exact_mod_cast Finset.card_pos.mpr hI
  refine ⟨y,hy,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ hIp).mp
    simpa only [a,mul_comm] using hprod.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · apply (mul_le_mul_iff_right₀ hAp).mp
    have h := hprod.trans (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))
    nlinarith only [h]

end LeanProofs.GowersSzemeredi
