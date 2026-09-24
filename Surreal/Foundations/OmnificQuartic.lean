import Surreal.Algebra.QuarticConstants
import Surreal.Surcomplex.PellRigidity

/-!
# The quartic definition on the actual omnific integers

Proves `odg:thm:standarddef`, including standardness of every witness,
and the subsequent vector version with six auxiliary variables.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A square bounded by an ordinary integer makes an omnific integer ordinary. -/
theorem omnific_standard_of_sq_le_int (z : OmnificInteger.{u}) (a : ℤ)
    (h : z ^ 2 ≤ omnificIntCast a) : ∃ b : ℤ, z = omnificIntCast b := by
  have hs : omnificToSurreal z ^ 2 ≤ (a : SignSequence.{u}) := by
    have h' : omnificToSurreal (z ^ 2) ≤ omnificToSurreal (omnificIntCast a) := h
    simpa only [map_pow, omnificToSurreal_intCast] using h'
  have ha : (0 : SignSequence.{u}) ≤ a := (sq_nonneg _).trans hs
  have hb : |omnificToSurreal z| ≤ (a : SignSequence.{u}) + 1 :=
    abs_le_of_sq_le_sq (by nlinarith) (by linarith)
  apply (omnific_bounded_iff z).mp
  exact ⟨(a : ℝ) + 1, by simpa only [map_add, map_one, map_intCast] using hb⟩

/-- Every coordinate, including all six witnesses, of a vector quartic zero is ordinary. -/
theorem omnific_quartic_vector_witnesses {n : ℕ} (t : Fin n → OmnificInteger.{u})
    (x y : OmnificInteger.{u}) (z : Fin 4 → OmnificInteger.{u})
    (h : QuarticConstants.vectorValue t x y z = 0) :
    (∀ i, ∃ a : ℤ, t i = omnificIntCast a) ∧
      (∃ a : ℤ, x = omnificIntCast a) ∧ (∃ b : ℤ, y = omnificIntCast b) ∧
      (∀ j, ∃ c : ℤ, z j = omnificIntCast c) := by
  obtain ⟨hp, hs⟩ := (QuarticConstants.vectorValue_eq_zero_iff
    omnificToSurreal omnificToSurreal_injective t x y z).mp h
  have hp' : x ^ 2 - omnificIntCast 2 * y ^ 2 = omnificIntCast 1 := by
    simpa only [map_ofNat, map_one] using hp
  obtain ⟨hx, hy⟩ := Surcomplex.omnific_pell_rigidity 2 1 (by norm_num) (by norm_num) x y hp'
  have ht : 0 ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨?_, ⟨_, hx⟩, ⟨_, hy⟩, ?_⟩
  · intro i
    apply omnific_standard_of_sq_le_int (t i) (omnificConstantCoeff x)
    rw [← hx]
    have hi : t i ^ 2 ≤ ∑ i, t i ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (t j)) (Finset.mem_univ i)
    linarith
  · intro j
    apply omnific_standard_of_sq_le_int (z j) (omnificConstantCoeff x)
    rw [← hx]
    have hj : z j ^ 2 ≤ ∑ j, z j ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ j)
    linarith

/-- The vector formula defines exactly ordinary integer vectors, with six witnesses for any n. -/
theorem omnific_quartic_vector_iff {n : ℕ} (t : Fin n → OmnificInteger.{u}) :
    (∃ x y : OmnificInteger.{u}, ∃ z : Fin 4 → OmnificInteger.{u},
      QuarticConstants.vectorValue t x y z = 0) ↔
        ∀ i, ∃ a : ℤ, t i = omnificIntCast a := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact (omnific_quartic_vector_witnesses t x y z h).1
  · intro h
    choose a ha using h
    obtain ⟨x, y, z, he⟩ := QuarticConstants.integer_vector_defines a
    refine ⟨omnificIntCast x, omnificIntCast y, omnificIntCast ∘ z, ?_⟩
    have ht : t = omnificIntCast ∘ a := funext ha
    rw [ht, ← QuarticConstants.map_vectorValue, he, map_zero]

/-- The literal quartic predicate defines exactly the ordinary integers in the actual carrier. -/
theorem omnific_quartic_iff (t : OmnificInteger.{u}) :
    QuarticConstants.Defines t ↔ ∃ a : ℤ, t = omnificIntCast a := by
  constructor
  · rintro ⟨x, y, z, h⟩
    have hv : QuarticConstants.vectorValue (fun _ : Fin 1 => t) x y z = 0 := by
      simpa [QuarticConstants.vectorValue, QuarticConstants.value] using h
    exact (omnific_quartic_vector_witnesses _ x y z hv).1 0
  · rintro ⟨a, rfl⟩
    exact (QuarticConstants.integer_defines a).map omnificIntCast

/-- The two-equation formulation is equivalent to being an ordinary integer. -/
theorem omnific_standard_system_iff (t : OmnificInteger.{u}) :
    (∃ x y : OmnificInteger.{u}, ∃ z : Fin 4 → OmnificInteger.{u},
      x ^ 2 - 2 * y ^ 2 = 1 ∧ x - t ^ 2 = ∑ j, z j ^ 2) ↔
        ∃ a : ℤ, t = omnificIntCast a := by
  rw [← omnific_quartic_iff]
  unfold QuarticConstants.Defines
  exact exists_congr (fun x => exists_congr (fun y => exists_congr (fun z =>
    (QuarticConstants.value_eq_zero_iff omnificToSurreal omnificToSurreal_injective t x y z).symm)))

/-- Every witness of the scalar two-equation system is an ordinary integer. -/
theorem omnific_standard_system_witnesses (t x y : OmnificInteger.{u})
    (z : Fin 4 → OmnificInteger.{u})
    (hp : x ^ 2 - 2 * y ^ 2 = 1) (hs : x - t ^ 2 = ∑ j, z j ^ 2) :
    (∃ a : ℤ, x = omnificIntCast a) ∧ (∃ b : ℤ, y = omnificIntCast b) ∧
      (∀ j, ∃ c : ℤ, z j = omnificIntCast c) := by
  have he := (QuarticConstants.value_eq_zero_iff
    omnificToSurreal omnificToSurreal_injective t x y z).mpr ⟨hp, hs⟩
  have hv : QuarticConstants.vectorValue (fun _ : Fin 1 => t) x y z = 0 := by
    simpa [QuarticConstants.vectorValue, QuarticConstants.value] using he
  exact (omnific_quartic_vector_witnesses _ x y z hv).2

end
end Surreal.Foundations.SignSequence
