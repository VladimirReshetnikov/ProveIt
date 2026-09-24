import Diophantine.Paper1980.Layout93
import Diophantine.Paper1980.Weights93

/-!
# Coefficient isolation for the certificate layout (Sections 2 and 5)

With the layout of `Layout93.lean`, the coefficient polynomial
`D = D_main + D_reset + D₅ + D₇` and the digit polynomial
`C = x + Σ zᵢ X^(vᵢ) + (dummies)`, the coefficients `a_p = [X^p](D·C²)` at
the positions of the window of target `j` are

* `a_{t_j} = ` the value of row `j` at `(x, z)`,
* `a_{t_j−3} = x²`,
* `a_{t_j−1} = 0` for an ordinary target, and `x² + 2x Σ_{p ∈ P} z_p` for a
  padded one,
* `a_p = 0` at `t_j − 5, t_j − 4, t_j − 2, t_j + 1, t_j + 2`,

and `|a_p| ≤ C(1)²` everywhere (`isolation_bound`).  The proofs use the
residue classes modulo six of the three kinds of exponents, the band
separation of distinct targets, and the exclusion of the dummy digits from
every tested position.
-/

namespace Jones1980

namespace Iso

open Polynomial Layout

noncomputable section

/-- `coeff` of a list sum. -/
theorem coeff_list_sum {ι : Type*} (l : List ι) (f : ι → ℤ[X]) (n : ℕ) :
    (l.map f).sum.coeff n = (l.map fun a => (f a).coeff n).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- `[X^p] (C c · X^e · Q) = c · [X^(p−e)] Q` if `e ≤ p`, else `0`. -/
theorem coeff_C_mul_X_pow_mul (c : ℤ) (e : ℕ) (Q : ℤ[X]) (p : ℕ) :
    (C c * X ^ e * Q).coeff p = if e ≤ p then c * Q.coeff (p - e) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

section Defs

variable (m s : ℕ)

/-- The main polynomial of row `R` placed at target `j`. -/
def rowPoly (j : ℕ) (R : Row m) : ℤ[X] :=
  (R.terms.map fun p => C p.2 * X ^ (t m s j - p.1)).sum

/-- The reset monomial of target `j`. -/
def resetPoly (j : ℕ) : ℤ[X] := X ^ (t m s j - 3)

/-- The padding polynomial of target `j` with physical set `P`. -/
def padPoly (j : ℕ) (P : Finset (Fin m)) : ℤ[X] :=
  X ^ (t m s j - 1) + ∑ p ∈ P, X ^ (t m s j - 1 - v p)

/-- The coefficient polynomial of a layout with rows `rows`, padding sets `P₅`, `P₇`
attached to the targets `s − 2` and `s − 1`. -/
def D (rows : Fin s → Row m) (P5 P7 : Finset (Fin m)) : ℤ[X] :=
  (∑ j : Fin s, rowPoly m s j (rows j)) + (∑ j : Fin s, resetPoly m s j) +
    padPoly m s (s - 2) P5 + padPoly m s (s - 1) P7

/-- The digit polynomial of the true coordinates. -/
def Cmain (x : ℤ) (z : Fin m → ℤ) : ℤ[X] := C x + ∑ i : Fin m, C (z i) * X ^ (v i)

/-- The digit polynomial of the dummy coordinates. -/
def Cdum (dum : Fin s → Fin 3 → ℤ) : ℤ[X] :=
  ∑ j : Fin s, ∑ e : Fin 3, C (dum j e) * X ^ (t m s j + e)

end Defs

section Csq

variable {m : ℕ} (x : ℤ) (z : Fin m → ℤ)

/-- `C² = x² + Σᵢ 2x zᵢ X^(vᵢ) + Σᵢ Σ_k zᵢ z_k X^(vᵢ + v_k)`. -/
theorem Cmain_sq :
    Cmain m x z ^ 2 = C (x ^ 2) + (∑ i : Fin m, C (2 * x * z i) * X ^ (v i)) +
      ∑ i : Fin m, ∑ k : Fin m, C (z i * z k) * X ^ (v i + v k) := by
  unfold Cmain
  rw [sq, add_mul, mul_add, mul_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul_sum]
  have h1 : ∑ i : Fin m, C x * (C (z i) * X ^ (v i)) = ∑ i : Fin m, C (x * z i) * X ^ (v i) := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [C_mul]; ring
  have h2 : ∑ i : Fin m, C (z i) * X ^ (v i) * C x = ∑ i : Fin m, C (x * z i) * X ^ (v i) := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [C_mul]; ring
  have h3 : ∑ i : Fin m, ∑ k : Fin m, C (z i) * X ^ (v i) * (C (z k) * X ^ (v k)) =
      ∑ i : Fin m, ∑ k : Fin m, C (z i * z k) * X ^ (v i + v k) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul, pow_add]; ring
  have h4 : ∑ i : Fin m, C (x * z i) * X ^ (v i) + ∑ i : Fin m, C (x * z i) * X ^ (v i) =
      ∑ i : Fin m, C (2 * x * z i) * X ^ (v i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (2 : ℤ) * x * z i = x * z i + x * z i by ring, C_add]; ring
  rw [h1, h2, h3, ← C_mul, ← sq, ← h4]; ring

/-- The coefficient of `C²` at `w`. -/
theorem coeff_Cmain_sq (w : ℕ) :
    (Cmain m x z ^ 2).coeff w = (if w = 0 then x ^ 2 else 0) +
      (∑ i : Fin m, if w = v i then 2 * x * z i else 0) +
      ∑ i : Fin m, ∑ k : Fin m, if w = v i + v k then z i * z k else 0 := by
  rw [Cmain_sq, coeff_add, coeff_add, coeff_C, finsetSum_coeff, finsetSum_coeff]
  have e1 : ∀ i : Fin m, (C (2 * x * z i) * X ^ (v i)).coeff w =
      if w = v i then 2 * x * z i else 0 := fun i => by rw [coeff_C_mul_X_pow]
  have e2 : ∀ i : Fin m, (∑ k : Fin m, C (z i * z k) * X ^ (v i + v k)).coeff w =
      ∑ k : Fin m, if w = v i + v k then z i * z k else 0 := fun i => by
    rw [finsetSum_coeff]
    exact Finset.sum_congr rfl fun k _ => by rw [coeff_C_mul_X_pow]
  simp only [e1, e2]

/-- `[X^0] C² = x²`. -/
theorem coeff_Cmain_sq_zero : (Cmain m x z ^ 2).coeff 0 = x ^ 2 := by
  rw [coeff_Cmain_sq]
  have h1 : ∀ i : Fin m, (if (0 : ℕ) = v i then 2 * x * z i else 0) = 0 := fun i => by
    have := v_pos i; split_ifs <;> omega
  have h2 : ∀ i k : Fin m, (if (0 : ℕ) = v i + v k then z i * z k else 0) = 0 := fun i k => by
    have := v_pos i; split_ifs <;> omega
  rw [if_pos rfl, Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => h2 i k))]
  ring

/-- `[X^(vᵢ)] C² = 2 x zᵢ`. -/
theorem coeff_Cmain_sq_v (i : Fin m) : (Cmain m x z ^ 2).coeff (v i) = 2 * x * z i := by
  rw [coeff_Cmain_sq]
  have h0 : (if v i = 0 then x ^ 2 else 0) = 0 := by have := v_pos i; split_ifs <;> omega
  have h1 : (∑ k : Fin m, if v i = v k then 2 * x * z k else 0) = 2 * x * z i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      have : v i ≠ v k := fun h => hk (Fin.ext (v_strictMono.injective h)).symm
      simp [this]
    · simp
  have h2 : ∀ a k : Fin m, (if v i = v a + v k then z a * z k else 0) = 0 := fun a k => by
    split_ifs with h
    · exfalso
      unfold v at h
      exact Weights.pow_ne_add i a k (by omega)
    · rfl
  rw [h0, h1, Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun k _ => h2 a k))]
  ring

/-- `[X^(2vᵢ)] C² = zᵢ²`. -/
theorem coeff_Cmain_sq_two_v (i : Fin m) : (Cmain m x z ^ 2).coeff (2 * v i) = z i ^ 2 := by
  rw [coeff_Cmain_sq]
  have h0 : (if 2 * v i = 0 then x ^ 2 else 0) = 0 := by have := v_pos i; split_ifs <;> omega
  have h1 : ∀ k : Fin m, (if 2 * v i = v k then 2 * x * z k else 0) = 0 := fun k => by
    split_ifs with h
    · exfalso; unfold v at h; exact Weights.pow_ne_two_mul k i (by omega)
    · rfl
  have hii : (if 2 * v i = v i + v i then z i * z i else 0) = z i * z i := by
    rw [if_pos (by ring)]
  have h2 : (∑ a : Fin m, ∑ k : Fin m, if 2 * v i = v a + v k then z a * z k else 0) = z i ^ 2 := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [hii, sq]
      · intro k _ hk
        split_ifs with h
        · exfalso; unfold v at h
          have := Weights.two_mul_pow_eq_add i i k (by omega)
          exact hk (Fin.ext this.2)
        · rfl
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · exfalso; unfold v at h
        have := Weights.two_mul_pow_eq_add i a k (by omega)
        exact ha (Fin.ext this.1)
      · rfl
    · simp
  rw [h0, Finset.sum_eq_zero (fun k _ => h1 k), h2]
  ring

/-- `[X^(vᵢ + v_k)] C² = 2 zᵢ z_k` for `i ≠ k`. -/
theorem coeff_Cmain_sq_add_v {i k : Fin m} (hik : i ≠ k) :
    (Cmain m x z ^ 2).coeff (v i + v k) = 2 * z i * z k := by
  rw [coeff_Cmain_sq]
  have h0 : (if v i + v k = 0 then x ^ 2 else 0) = 0 := by have := v_pos i; split_ifs <;> omega
  have h1 : ∀ a : Fin m, (if v i + v k = v a then 2 * x * z a else 0) = 0 := fun a => by
    split_ifs with h
    · exfalso; unfold v at h; exact Weights.pow_ne_add a i k (by omega)
    · rfl
  have key : ∀ a b : Fin m, v i + v k = v a + v b → (a = i ∧ b = k) ∨ (a = k ∧ b = i) := by
    intro a b h; unfold v at h
    rcases Weights.add_pow_eq_add i k a b (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨(Fin.ext h1).symm, (Fin.ext h2).symm⟩
    · right; exact ⟨(Fin.ext h2).symm, (Fin.ext h1).symm⟩
  -- the inner sums
  have gi : (∑ b : Fin m, if v i + v k = v i + v b then z i * z b else 0) = z i * z k := by
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro b _ hb
      split_ifs with h
      · exfalso
        rcases key i b h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hb h2
        · exact hik h1
      · rfl
    · simp
  have gk : (∑ b : Fin m, if v i + v k = v k + v b then z k * z b else 0) = z k * z i := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos (by ring)]
    · intro b _ hb
      split_ifs with h
      · exfalso
        rcases key k b h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hik h1.symm
        · exact hb h2
      · rfl
    · simp
  have hother : ∀ a : Fin m, a ≠ i → a ≠ k →
      (∑ b : Fin m, if v i + v k = v a + v b then z a * z b else 0) = 0 := by
    intro a hai hak
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with h
    · exfalso
      rcases key a b h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hai h1
      · exact hak h1
    · rfl
  have h2 : (∑ a : Fin m, ∑ b : Fin m, if v i + v k = v a + v b then z a * z b else 0) =
      2 * z i * z k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hik.symm, Finset.mem_univ k⟩)]
    rw [gi, gk, Finset.sum_eq_zero]
    · ring
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha
      exact hother a ha.2 ha.1
  rw [h0, Finset.sum_eq_zero (fun a _ => h1 a), h2]
  ring

/-- `[X^w] C² = 0` unless `6 ∣ w`. -/
theorem coeff_Cmain_sq_of_not_dvd {w : ℕ} (hw : ¬ 6 ∣ w) : (Cmain m x z ^ 2).coeff w = 0 := by
  rw [coeff_Cmain_sq]
  have h0 : (if w = 0 then x ^ 2 else 0) = 0 := by
    split_ifs with h
    · exact absurd (h ▸ dvd_zero 6) hw
    · rfl
  have h1 : ∀ i : Fin m, (if w = v i then 2 * x * z i else 0) = 0 := fun i => by
    split_ifs with h
    · exact absurd (h ▸ six_dvd_v i) hw
    · rfl
  have h2 : ∀ i k : Fin m, (if w = v i + v k then z i * z k else 0) = 0 := fun i k => by
    split_ifs with h
    · exact absurd (h ▸ dvd_add (six_dvd_v i) (six_dvd_v k)) hw
    · rfl
  rw [h0, Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => h2 i k))]
  ring

/-- `[X^w] C² = 0` for `w > 2M`. -/
theorem coeff_Cmain_sq_of_gt {w : ℕ} (hw : 2 * M m < w) : (Cmain m x z ^ 2).coeff w = 0 := by
  rw [coeff_Cmain_sq]
  have h0 : (if w = 0 then x ^ 2 else 0) = 0 := by
    split_ifs with h
    · omega
    · rfl
  have h1 : ∀ i : Fin m, (if w = v i then 2 * x * z i else 0) = 0 := fun i => by
    split_ifs with h
    · exfalso; have := v_le_M i.2; omega
    · rfl
  have h2 : ∀ i k : Fin m, (if w = v i + v k then z i * z k else 0) = 0 := fun i k => by
    split_ifs with h
    · exfalso; have := v_le_M i.2; have := v_le_M k.2; omega
    · rfl
  rw [h0, Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => h2 i k))]
  ring

end Csq

end

end Iso

end Jones1980
