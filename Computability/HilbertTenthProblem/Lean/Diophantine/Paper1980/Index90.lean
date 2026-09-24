import Diophantine.Paper1980.DValid90b
import Diophantine.Paper1980.CodeDigits

/-!
# The fixed index of a 90-operation layout

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 3, (8)–(9).  From a layout
the certificate's index is built as follows:

* the indicator support `supp = {vᵢ} ∪ {r, r + 1, r + 2 : r a tested start}`
  (`DValid90b.lean`), all below `K = t_last + 3`;
* `ℓ₀(T) = Σ_{h ∈ supp} T^h`, given by its digit list `ell0d L` of length `L`;
* `e₀(T) = ℓ₀(T) + D(T)`, with digit list `e0d` of length `K`; its digits are
  `ind h + [X^h] D ∈ {0, 1}`, because the negative coefficients of `D` sit on
  the support and the positive ones off it;
* `V = ℓ₀(2) + e₀(2)·2^L = ofDigits 2 (ell0d L ++ e0d)`.

This file defines the digit lists and proves their digit bounds and radix-`B`
values; `e₀(B) − ℓ₀(B) = D(B)`.
-/

namespace Jones1980

namespace L90

open Polynomial Finset Nat
open Layout (Row)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))

/-- The digit of `ℓ₀` at `h`. -/
def ind (h : ℕ) : ℕ := if h ∈ supp rows then 1 else 0

theorem ind_le_one (h : ℕ) : ind rows h ≤ 1 := by unfold ind; split_ifs <;> omega

theorem ind_eq_one_iff (h : ℕ) : ind rows h = 1 ↔ h ∈ supp rows := by
  unfold ind; split_ifs with hh <;> simp [hh]

theorem ind_eq_zero_iff (h : ℕ) : ind rows h = 0 ↔ h ∉ supp rows := by
  unfold ind; split_ifs with hh <;> simp [hh]

/-- The indicator support lies below `K`. -/
theorem mem_supp_lt {h : ℕ} (hh : h ∈ supp rows) : h < K m s := by
  unfold K
  rcases (mem_supp rows).1 hh with ⟨i, rfl⟩ | ⟨r, hr, hr'⟩
  · have := v_le_M i.isLt
    have := t_ge m s (s - 1)
    unfold tl; omega
  · have := (Rset_bounds rows hr).2
    omega

theorem ind_eq_zero_of_ge {h : ℕ} (hK : K m s ≤ h) : ind rows h = 0 := by
  rw [ind_eq_zero_iff]
  intro hh
  have := mem_supp_lt rows hh
  omega

/-- The digit list of `ℓ₀`, of length `L`. -/
def ell0d (L : ℕ) : List ℕ := (List.range L).map (ind rows)

/-- The digit list of `e₀ = ℓ₀ + D`, of length `K`. -/
def e0d : List ℕ :=
  (List.range (K m s)).map fun h => ((ind rows h : ℤ) + (D s rows hel PX).coeff h).toNat

theorem ell0d_length (L : ℕ) : (ell0d rows L).length = L := by simp [ell0d]

theorem e0d_length : (e0d rows hel PX).length = K m s := by simp [e0d]

theorem ell0d_mem_le (L : ℕ) : ∀ y ∈ ell0d rows L, y ≤ 1 := by
  intro y hy
  unfold ell0d at hy
  rw [List.mem_map] at hy
  obtain ⟨h, _, rfl⟩ := hy
  exact ind_le_one rows h

variable (hL : LayoutOk s rows hel)
include hL

/-- The digits of `e₀` are binary. -/
theorem e0_digit_bounds (h : ℕ) :
    0 ≤ (ind rows h : ℤ) + (D s rows hel PX).coeff h ∧
      (ind rows h : ℤ) + (D s rows hel PX).coeff h ≤ 1 := by
  have habs := abs_le.1 (abs_coeff_D_le_one rows hel PX hL h)
  by_cases hh : h ∈ supp rows
  · rw [(ind_eq_one_iff rows h).2 hh]
    have := coeff_D_nonpos_of_mem_supp rows hel PX hL hh
    push_cast; constructor <;> linarith
  · rw [(ind_eq_zero_iff rows h).2 hh]
    have : 0 ≤ (D s rows hel PX).coeff h := by
      by_contra hneg; push Not at hneg
      exact hh (mem_supp_of_mem_Rset rows (coeff_D_neg_mem_Rset rows hel PX hL hneg))
    push_cast; constructor <;> linarith

theorem e0d_mem_le : ∀ y ∈ e0d rows hel PX, y ≤ 1 := by
  intro y hy
  unfold e0d at hy
  rw [List.mem_map] at hy
  obtain ⟨h, _, rfl⟩ := hy
  have := (e0_digit_bounds rows hel PX hL h).2
  omega

omit hL

/-- The radix-`B` value of the digit list of `ℓ₀`: `Σ_{h<L} ind h · B^h`. -/
theorem ofDigits_ell0d (B L : ℕ) :
    ofDigits B (ell0d rows L) = ∑ h ∈ Finset.range L, ind rows h * B ^ h := by
  unfold ell0d
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, ofDigits_append, ih, Finset.sum_range_succ]
    simp
    ring

/-- The radix-`B` value of the digit list of `e₀`, in `ℕ`. -/
theorem ofDigits_e0d_nat (B : ℕ) :
    ofDigits B (e0d rows hel PX) = ∑ h ∈ Finset.range (K m s),
      ((ind rows h : ℤ) + (D s rows hel PX).coeff h).toNat * B ^ h := by
  unfold e0d
  generalize K m s = N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, ofDigits_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, ofDigits_singleton, List.length_map,
      List.length_range]
    ring

include hL

/-- The radix-`B` value of the digit list of `e₀`, as an integer. -/
theorem ofDigits_e0d (B : ℕ) :
    ((ofDigits B (e0d rows hel PX) : ℕ) : ℤ) =
      ∑ h ∈ Finset.range (K m s), ((ind rows h : ℤ) + (D s rows hel PX).coeff h) * (B : ℤ) ^ h := by
  rw [ofDigits_e0d_nat]
  push_cast
  apply Finset.sum_congr rfl
  intro h _
  rw [Int.toNat_of_nonneg (e0_digit_bounds rows hel PX hL h).1]

/-- `e₀(B) − ℓ₀(B) = D(B)`. -/
theorem e0_sub_ell0 (B : ℕ) {L : ℕ} (hKL : K m s ≤ L) :
    ((ofDigits B (e0d rows hel PX) : ℕ) : ℤ) - (ofDigits B (ell0d rows L) : ℕ) =
      (D s rows hel PX).eval (B : ℤ) := by
  rw [ofDigits_e0d rows hel PX hL, ofDigits_ell0d]
  have hdeg : (D s rows hel PX).natDegree < K m s := by
    have hK : 3 ≤ K m s := by unfold K; omega
    have : (D s rows hel PX).natDegree ≤ K m s - 1 :=
      natDegree_le_iff_coeff_eq_zero.2 fun N hN => coeff_D_eq_zero_of_ge rows hel PX hL (by omega)
    omega
  rw [eval_eq_sum_range' hdeg]
  -- `ℓ₀` beyond `K` has zero digits
  have hl : ∑ h ∈ Finset.range L, ind rows h * B ^ h =
      ∑ h ∈ Finset.range (K m s), ind rows h * B ^ h := by
    symm
    apply Finset.sum_subset (Finset.range_mono hKL)
    intro h _ hh
    rw [Finset.mem_range] at hh
    rw [ind_eq_zero_of_ge rows (by omega), zero_mul]
  rw [hl]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

end

end L90

end Jones1980
