import Diophantine.Paper1980.Isolation93d
import Diophantine.Paper1980.Bound93
import Diophantine.Paper1980.CodeDigits

/-!
# The fixed index of a layout (Section 2, (7)–(13))

From a layout (`m` physical coordinates, `s` rows, padding sets `P₅`, `P₇`)
the certificate's index is built as follows:

* `K = t_{s−1} + 3`: every exponent of `D` is below `K`;
* the indicator support `supp = {vᵢ} ∪ {t_j, t_j + 1, t_j + 2}`;
* `ℓ₀(T) = Σ_{h ∈ supp} T^h`, given by its digit list `ell0d L` of length `L`;
* `e₀(T) = Σ_{h<K} T^h + D(T)`, with digit list `e0d K` of length `K`
  (digits `1 + [X^h] D ∈ {0, 1, 2}` when `|[X^h] D| ≤ 1`);
* `V = ℓ₀(4) + e₀(4)·4^L = ofDigits 4 (ell0d L ++ e0d K)`.

`L` and `H₀` are chosen afterwards: `L > 3K + 2`, `H₀` a power of two with
`H₀ ≥ 2·4^(2L+1)`, `H₀ ≥ 64 D₁ (m+1)²`, `H₀ ≥ 3L`, `H₀ ≥ 1024`; `H = H₀ − 3`,
`Tindex = ψ₄(L)`.  This file defines the digit lists and proves their digit
bounds and radix-`B` values.
-/

namespace Jones1980

namespace Iso

open Polynomial Layout Nat

noncomputable section

section IndexDefs

variable (m s : ℕ)

/-- `K = t_{s−1} + 3`. -/
def K : ℕ := t m s (s - 1) + 3

/-- The indicator support: the coordinate weights and the three tested positions of
every target. -/
def supp : Finset ℕ :=
  (Finset.range m).image v ∪
    (Finset.range s).biUnion (fun j => {t m s j, t m s j + 1, t m s j + 2})

/-- The digit of `ℓ₀` at `h`. -/
def ind (h : ℕ) : ℕ := if h ∈ supp m s then 1 else 0

/-- The digit list of `ℓ₀`, of length `L`. -/
def ell0d (L : ℕ) : List ℕ := (List.range L).map (ind m s)

/-- The digit list of `e₀`, of length `K`, for the coefficient polynomial `D`. -/
def e0d (D : ℤ[X]) : List ℕ := (List.range (K m s)).map fun h => (1 + D.coeff h).toNat

theorem ind_le_one (h : ℕ) : ind m s h ≤ 1 := by unfold ind; split_ifs <;> omega

theorem ell0d_length (L : ℕ) : (ell0d m s L).length = L := by simp [ell0d]

theorem e0d_length (D : ℤ[X]) : (e0d m s D).length = K m s := by simp [e0d]

theorem ell0d_mem_le (L : ℕ) : ∀ y ∈ ell0d m s L, y ≤ 1 := by
  intro y hy
  unfold ell0d at hy
  rw [List.mem_map] at hy
  obtain ⟨h, _, rfl⟩ := hy
  exact ind_le_one m s h

theorem e0d_mem_le (D : ℤ[X]) (hD : ∀ h, |D.coeff h| ≤ 1) : ∀ y ∈ e0d m s D, y ≤ 2 := by
  intro y hy
  unfold e0d at hy
  rw [List.mem_map] at hy
  obtain ⟨h, _, rfl⟩ := hy
  have := abs_le.1 (hD h)
  omega

/-- The radix-`B` value of the digit list of `ℓ₀`: `Σ_{h<L} ind h · B^h`. -/
theorem ofDigits_ell0d (B L : ℕ) :
    ofDigits B (ell0d m s L) = ∑ h ∈ Finset.range L, ind m s h * B ^ h := by
  unfold ell0d
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, ofDigits_append, ih, Finset.sum_range_succ]
    simp
    ring

/-- The radix-`B` value of the digit list of `e₀`, in `ℕ`. -/
theorem ofDigits_e0d_nat (B : ℕ) (D : ℤ[X]) :
    ofDigits B (e0d m s D) = ∑ h ∈ Finset.range (K m s), (1 + D.coeff h).toNat * B ^ h := by
  unfold e0d
  generalize K m s = N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, ofDigits_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, ofDigits_singleton, List.length_map,
      List.length_range]
    ring

/-- The radix-`B` value of the digit list of `e₀`: `Σ_{h<K} (1 + [X^h]D) · B^h` (as integers). -/
theorem ofDigits_e0d (B : ℕ) (D : ℤ[X]) (hD : ∀ h, |D.coeff h| ≤ 1) :
    ((ofDigits B (e0d m s D) : ℕ) : ℤ) =
      ∑ h ∈ Finset.range (K m s), (1 + D.coeff h) * (B : ℤ) ^ h := by
  rw [ofDigits_e0d_nat]
  push_cast
  apply Finset.sum_congr rfl
  intro h _
  have := abs_le.1 (hD h)
  rw [Int.toNat_of_nonneg (by omega)]

end IndexDefs

end

end Iso

end Jones1980
