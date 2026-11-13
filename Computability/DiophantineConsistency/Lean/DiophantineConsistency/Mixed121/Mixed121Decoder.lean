import DiophantineConsistency.ModelDigitTransfer
import DiophantineConsistency.Compact44.CompactSelectorSum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The radix-four clause decoder

The clause argument of `31-sun10/coefficients/COEFFICIENT_PROOF.md` §2, in
any model of `𝗜𝚺₁`. A clause coefficient is `c_i = 1 + 2^10·Σ_{k<m} b_ik 4^k`
with Boolean field digits `b_ik`. The copy and anchor coefficients add Boolean
digits `g_k` at the same radix-four places. The mask is
`(2^10 − 2) + 2^10·Σ_{k<m} 4^k`.

If the selected clause sum has no carry against the mask, then either nothing
is selected and every `g_k` is zero, or exactly one selector `i` is active and
`g_k = b_ik` for every `k`. The order of the argument matters. The low ten
bits are exactly the selector count `n` (all other terms are multiples of
`2^10`), and the low mask forces `n ≤ 1`. Only then does each radix-four field
hold a digit below four, so that the masked low bit forces it into `{0, 2}`.
No carry-freeness of the upper fields is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Decoder
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry DiophantineConsistency.ArithmeticWindowDigits
  DiophantineConsistency.ModelCarries DiophantineConsistency.ModelDigitTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem noCarry_one_even (x : V) (h : NoCarry x 1) : x%2=0 := by
  have hx : x%2≤1 := lt_two_iff_le_one.mp (by simp)
  have heq : 2*(x/2)+x%2=x := div_add_mod x 2
  have hh : NoCarry (2*(x/2)+x%2) (2*(0:V)+1) := by simpa only [heq, mul_zero, zero_add] using h
  have hl := ((noCarry_binary (x/2) 0 (x%2) 1 hx le_rfl).mp hh).1
  have hl' : x%2+1≤(0:V)+1 := by simpa using hl
  exact le_antisymm ((add_le_add_iff_right (1:V)).mp hl') (by simp)

private theorem exp_two' : Exp.exp (2:V) = 4 := by
  rw [show (2:V) = 1 + 1 by norm_num, exp_succ, exp_one]; norm_num

theorem dsum_add (R : V) (f g : ℕ → V) (n : ℕ) :
    dsum R f n + dsum R g n = dsum R (fun k => f k + g k) n := by
  simp only [dsum, add_mul, Finset.sum_add_distrib]

/-- Radix-four digits below four have no carry against `Σ 4^k` exactly when
every digit is even. -/
theorem field_even (δ : ℕ → V) (m : ℕ) (hδ : ∀ k < m, δ k < 4)
    (h : NoCarry (dsum (Exp.exp 2) δ m) (dsum (Exp.exp 2) (fun _ => 1) m)) :
    ∀ k < m, δ k % 2 = 0 := by
  have hδ' : ∀ k < m, δ k < Exp.exp (2:V) := fun k hk => by rw [exp_two']; exact hδ k hk
  have h1 : ∀ k < m, (fun _ => (1:V)) k < Exp.exp (2:V) := fun _ _ => by
    rw [exp_two']; norm_num
  have hd := (noCarry_dsum_iff (2:V) δ (fun _ => 1) m hδ' h1).mp h
  exact fun k hk => noCarry_one_even _ (hd k hk)

/-- A Boolean radix-four field with no carry against `Σ 4^k` is zero. -/
theorem boolean_field_zero (g : ℕ → V) (m : ℕ) (hg : ∀ k < m, g k ≤ 1)
    (h : NoCarry (dsum (Exp.exp 2) g m) (dsum (Exp.exp 2) (fun _ => 1) m)) :
    ∀ k < m, g k = 0 := by
  have he := field_even g m (fun k hk => lt_of_le_of_lt (hg k hk) (by norm_num)) h
  intro k hk
  rcases le_one_iff_eq_zero_or_one.mp (hg k hk) with h0 | h1
  · exact h0
  · have := he k hk; rw [h1] at this; simp at this

/-- Two Boolean digits with even sum are equal. -/
private theorem eq_of_even_sum {a b : V} (ha : a ≤ 1) (hb : b ≤ 1) (h : (a + b) % 2 = 0) :
    b = a := by
  rcases le_one_iff_eq_zero_or_one.mp ha with rfl | rfl <;>
    rcases le_one_iff_eq_zero_or_one.mp hb with rfl | rfl <;> simp_all

/-- **The radix-four clause decoder.** -/
theorem decode {ι : Type*} [Fintype ι] (f : ι → V) (b : ι → ℕ → V) (g : ℕ → V) (m : ℕ)
    (hn : (∑ i, f i) < Exp.exp 10)
    (hb : ∀ i, ∀ k < m, b i k ≤ 1) (hg : ∀ k < m, g k ≤ 1)
    (h : NoCarry ((∑ i, f i * (1 + Exp.exp 10 * dsum (Exp.exp 2) (b i) m))
                   + Exp.exp 10 * dsum (Exp.exp 2) g m)
                 ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) m)) :
    ((∀ i, f i = 0) ∧ ∀ k < m, g k = 0) ∨
      ∃ i, CompactSelectorSum.Selected f i ∧ ∀ k < m, g k = b i k := by
  classical
  set E : V := Exp.exp 10 with hE
  set R : V := Exp.exp 2
  set M : V := dsum R (fun _ => 1) m
  set P : V := (∑ i, f i * dsum R (b i) m) + dsum R g m
  have hpt : ∀ i, f i * (1 + E * dsum R (b i) m) = f i + (f i * dsum R (b i) m) * E :=
    fun i => by ring
  have hD : (∑ i, f i * (1 + E * dsum R (b i) m)) + E * dsum R g m = (∑ i, f i) + P * E := by
    simp only [hpt, Finset.sum_add_distrib, ← Finset.sum_mul, P]
    ring
  have hT : E - 2 < E := tsub_lt_self (exp_pos _) (by norm_num)
  have hsplit := (noCarry_concat (k := (10:V)) hn hT).mpr
    (by rw [← hD, show (E - 2) + M * E = (E - 2) + E * M by ring]; exact h)
  obtain ⟨hlow, hhigh⟩ := hsplit
  have hcount : (∑ i, f i) ≤ 1 := by
    apply noCarry_ones_two 9
    · simpa only [show (9:V)+1=10 by norm_num] using hn
    · simpa only [show (9:V)+1=10 by norm_num] using hlow
  rcases CompactSelectorSum.sum_le_one_cases f hcount with hz | ⟨i, hi⟩
  · left
    refine ⟨hz, ?_⟩
    have hP : P = dsum R g m := by
      simp only [P, hz, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hP] at hhigh
    exact boolean_field_zero g m hg hhigh
  · right
    refine ⟨i, hi, ?_⟩
    have hsel : (∑ j, f j * dsum R (b j) m) = dsum R (b i) m := by
      have := CompactSelectorSum.selected_weighted hi (fun j => dsum R (b j) m)
      simpa only [mul_comm] using this
    have hP : P = dsum R (fun k => b i k + g k) m := by
      simp only [P, hsel, dsum_add]
    rw [hP] at hhigh
    have he := field_even (fun k => b i k + g k) m (fun k hk =>
      lt_of_le_of_lt (add_le_add (hb i k hk) (hg k hk)) (by norm_num)) hhigh
    exact fun k hk => eq_of_even_sum (hb i k hk) (hg k hk) (he k hk)
end Mixed121Decoder
#print axioms Mixed121Decoder.field_even
#print axioms Mixed121Decoder.boolean_field_zero
#print axioms Mixed121Decoder.decode
