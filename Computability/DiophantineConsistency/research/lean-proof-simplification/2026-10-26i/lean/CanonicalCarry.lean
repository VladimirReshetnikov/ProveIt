import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-! A finite maximum principle for carries with a fixed digit vector.
This does not claim uniqueness of arbitrary quotient-recurrence solutions. -/
namespace AdditionalSimplifications

theorem carry_le_of_same_digits {ι : Type*} [Fintype ι]
    {ρ : ℕ} (hρ : 1 < ρ) (prev : ι → ι)
    (raw digits k l : ι → ℕ)
    (hk : ∀ i, raw i + k (prev i) = digits i + ρ * k i)
    (hl : ∀ i, raw i + l (prev i) = digits i + ρ * l i) :
    ∀ i, k i ≤ l i := by
  classical
  intro j
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun a => (k a : ℤ) - l a) ⟨j, Finset.mem_univ j⟩
  have hp := hmax (prev i) (Finset.mem_univ _)
  have hj := hmax j (Finset.mem_univ _)
  have hki : (raw i : ℤ) + k (prev i) = digits i + (ρ : ℤ) * k i := by
    exact_mod_cast hk i
  have hli : (raw i : ℤ) + l (prev i) = digits i + (ρ : ℤ) * l i := by
    exact_mod_cast hl i
  have hr : (1 : ℤ) < ρ := by exact_mod_cast hρ
  have hdelta : (k i : ℤ) - l i ≤ 0 := by nlinarith
  omega

theorem carries_unique_of_same_digits {ι : Type*} [Fintype ι]
    {ρ : ℕ} (hρ : 1 < ρ) (prev : ι → ι)
    (raw digits k l : ι → ℕ)
    (hk : ∀ i, raw i + k (prev i) = digits i + ρ * k i)
    (hl : ∀ i, raw i + l (prev i) = digits i + ρ * l i) : k = l := by
  funext i
  exact Nat.le_antisymm
    (carry_le_of_same_digits hρ prev raw digits k l hk hl i)
    (carry_le_of_same_digits hρ prev raw digits l k hl hk i)

/-- Fixed-length radix packing is injective on bounded digit vectors. -/
theorem packed_digits_injective {n ρ : ℕ} (hρ : 1 < ρ)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < ρ) (hb : ∀ i, b i < ρ)
    (hword : Nat.ofDigits ρ (List.ofFn a) = Nat.ofDigits ρ (List.ofFn b)) :
    a = b := by
  apply List.ofFn_injective
  apply Nat.ofDigits_inj_of_len_eq hρ (by simp) _ _ hword
  · simpa only [List.forall_mem_ofFn_iff] using ha
  · simpa only [List.forall_mem_ofFn_iff] using hb

/-- Equal complete packed words determine both the digits and the carries.
Equality of words cannot be weakened to congruence modulo a Mersenne number. -/
theorem normalization_unique {n ρ : ℕ} (hρ : 1 < ρ)
    (prev : Fin n → Fin n) (raw a b k l : Fin n → ℕ)
    (ha : ∀ i, a i < ρ) (hb : ∀ i, b i < ρ)
    (hword : Nat.ofDigits ρ (List.ofFn a) = Nat.ofDigits ρ (List.ofFn b))
    (hk : ∀ i, raw i + k (prev i) = a i + ρ * k i)
    (hl : ∀ i, raw i + l (prev i) = b i + ρ * l i) : a = b ∧ k = l := by
  have hab := packed_digits_injective hρ a b ha hb hword
  subst b
  exact ⟨rfl, carries_unique_of_same_digits hρ prev raw a k l hk hl⟩

#print axioms packed_digits_injective
#print axioms normalization_unique

#print axioms carry_le_of_same_digits
#print axioms carries_unique_of_same_digits
end AdditionalSimplifications
