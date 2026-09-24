import Diophantine.Paper1980.Layout90

/-!
# The coefficients of `C(T)²` for the 90-operation layout

`C = x + Σᵢ zᵢ T^(vᵢ)` with the base-seven weights `vᵢ = 8·7ⁱ`.  The coefficient
of `T^w` in `C²` is `x²` at `w = 0`, `2 x zᵢ` at `w = vᵢ`, `zᵢ²` at `w = 2vᵢ`,
`2 zᵢ z_k` at `w = vᵢ + v_k` (`i ≠ k`), and zero at every other `w`; in
particular it vanishes unless `w = W μ` for a monomial `μ` of degree at most
two.  The six helper pairs of a group sum to the square of the group's value.
-/

namespace Jones1980

namespace L90

open Polynomial
open Layout (Row)

noncomputable section

variable {m : ℕ} (x : ℤ) (z : Fin m → ℤ)

/-! ### Pairs of coordinates -/

theorem pair_eq {i k a b : Fin m} (h : ({i, k} : Multiset (Fin m)) = {a, b}) :
    (i = a ∧ k = b) ∨ (i = b ∧ k = a) := by
  simp only [Multiset.insert_eq_cons] at h
  rcases (Multiset.cons_eq_cons).1 h with ⟨h1, h2⟩ | ⟨_, cs, h2, h3⟩
  · left; exact ⟨h1, Multiset.singleton_inj.1 h2⟩
  · right
    obtain ⟨h4, h5⟩ := (Multiset.singleton_eq_cons_iff _).1 h2
    obtain ⟨h6, _⟩ := (Multiset.singleton_eq_cons_iff _).1 h3
    exact ⟨h6.symm, h4⟩

theorem v_ne_add (i a k : Fin m) : v i ≠ v a + v k := by
  intro h
  have : W ({i} : Multiset (Fin m)) = W {a, k} := by rw [W_singleton, W_pair]; exact h
  have := congrArg Multiset.card (W_inj (by simp) (by simp) this)
  simp at this

theorem two_v_eq_add {i a k : Fin m} (h : 2 * v i = v a + v k) : a = i ∧ k = i := by
  have : W ({i, i} : Multiset (Fin m)) = W {a, k} := by rw [W_pair, W_pair]; omega
  have := W_inj (by simp) (by simp) this
  rcases pair_eq this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1.symm, h2.symm⟩
  · exact ⟨h2.symm, h1.symm⟩

theorem add_v_eq_add {i k a b : Fin m} (h : v i + v k = v a + v b) :
    (a = i ∧ b = k) ∨ (a = k ∧ b = i) := by
  have : W ({i, k} : Multiset (Fin m)) = W {a, b} := by rw [W_pair, W_pair]; exact h
  have := W_inj (by simp) (by simp) this
  rcases pair_eq this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1.symm, h2.symm⟩
  · right; exact ⟨h2.symm, h1.symm⟩

/-! ### The expansion of `C²` -/

theorem Cmain_sq :
    Cmain x z ^ 2 = C (x ^ 2) + (∑ i : Fin m, C (2 * x * z i) * X ^ (v i)) +
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
    (Cmain x z ^ 2).coeff w = (if w = 0 then x ^ 2 else 0) +
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
theorem coeff_Cmain_sq_zero : (Cmain x z ^ 2).coeff 0 = x ^ 2 := by
  rw [coeff_Cmain_sq]
  have h1 : ∀ i : Fin m, (if (0 : ℕ) = v i then 2 * x * z i else 0) = 0 := fun i => by
    have := v_pos i; split_ifs <;> omega
  have h2 : ∀ i k : Fin m, (if (0 : ℕ) = v i + v k then z i * z k else 0) = 0 := fun i k => by
    have := v_pos i; split_ifs <;> omega
  rw [if_pos rfl, Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => h2 i k))]
  ring

/-- `[X^(vᵢ)] C² = 2 x zᵢ`. -/
theorem coeff_Cmain_sq_v (i : Fin m) : (Cmain x z ^ 2).coeff (v i) = 2 * x * z i := by
  rw [coeff_Cmain_sq]
  have h0 : (if v i = 0 then x ^ 2 else 0) = 0 := by have := v_pos i; split_ifs <;> omega
  have h1 : (∑ k : Fin m, if v i = v k then 2 * x * z k else 0) = 2 * x * z i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      have : v i ≠ v k := fun h => hk (Fin.ext (v_inj h)).symm
      simp [this]
    · simp
  have h2 : ∀ a k : Fin m, (if v i = v a + v k then z a * z k else 0) = 0 := fun a k => by
    split_ifs with h
    · exact absurd h (v_ne_add i a k)
    · rfl
  rw [h0, h1, Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun k _ => h2 a k))]
  ring

/-- `[X^(2vᵢ)] C² = zᵢ²`. -/
theorem coeff_Cmain_sq_two_v (i : Fin m) : (Cmain x z ^ 2).coeff (2 * v i) = z i ^ 2 := by
  rw [coeff_Cmain_sq]
  have h0 : (if 2 * v i = 0 then x ^ 2 else 0) = 0 := by have := v_pos i; split_ifs <;> omega
  have h1 : ∀ k : Fin m, (if 2 * v i = v k then 2 * x * z k else 0) = 0 := fun k => by
    split_ifs with h
    · exact absurd (show v k = v i + v i by omega) (v_ne_add k i i)
    · rfl
  have hii : (if 2 * v i = v i + v i then z i * z i else 0) = z i * z i := by
    rw [if_pos (by ring)]
  have h2 : (∑ a : Fin m, ∑ k : Fin m, if 2 * v i = v a + v k then z a * z k else 0) = z i ^ 2 := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [hii, sq]
      · intro k _ hk
        split_ifs with h
        · exact absurd (two_v_eq_add h).2 hk
        · rfl
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · exact absurd (two_v_eq_add h).1 ha
      · rfl
    · simp
  rw [h0, Finset.sum_eq_zero (fun k _ => h1 k), h2]
  ring

/-- `[X^(vᵢ + v_k)] C² = 2 zᵢ z_k` for `i ≠ k`. -/
theorem coeff_Cmain_sq_add_v {i k : Fin m} (hik : i ≠ k) :
    (Cmain x z ^ 2).coeff (v i + v k) = 2 * z i * z k := by
  rw [coeff_Cmain_sq]
  have h0 : (if v i + v k = 0 then x ^ 2 else 0) = 0 := by have := v_pos i; split_ifs <;> omega
  have h1 : ∀ a : Fin m, (if v i + v k = v a then 2 * x * z a else 0) = 0 := fun a => by
    split_ifs with h
    · exact absurd h.symm (v_ne_add a i k)
    · rfl
  have key : ∀ a b : Fin m, v i + v k = v a + v b → (a = i ∧ b = k) ∨ (a = k ∧ b = i) :=
    fun a b h => add_v_eq_add h
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

/-- `[X^w] C² = 0` unless `w` is the weight of a monomial of degree at most two. -/
theorem coeff_Cmain_sq_eq_zero {w : ℕ}
    (hw : ∀ μ : Multiset (Fin m), Multiset.card μ ≤ 2 → W μ ≠ w) :
    (Cmain x z ^ 2).coeff w = 0 := by
  rw [coeff_Cmain_sq]
  have h0 : (if w = 0 then x ^ 2 else 0) = 0 := by
    split_ifs with h
    · exact absurd (by rw [W_zero, h]) (hw 0 (by simp))
    · rfl
  have h1 : ∀ i : Fin m, (if w = v i then 2 * x * z i else 0) = 0 := fun i => by
    split_ifs with h
    · exact absurd (by rw [W_singleton, h]) (hw {i} (by simp))
    · rfl
  have h2 : ∀ i k : Fin m, (if w = v i + v k then z i * z k else 0) = 0 := fun i k => by
    split_ifs with h
    · exact absurd (by rw [W_pair, h]) (hw {i, k} (by simp))
    · rfl
  rw [h0, Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => h2 i k))]
  ring

/-- A nonzero coefficient of `C²` sits at the weight of a monomial of degree at most two. -/
theorem exists_W_of_coeff_ne_zero {w : ℕ} (h : (Cmain x z ^ 2).coeff w ≠ 0) :
    ∃ μ : Multiset (Fin m), Multiset.card μ ≤ 2 ∧ W μ = w := by
  by_contra hne
  push Not at hne
  exact h (coeff_Cmain_sq_eq_zero x z hne)

/-- `[X^w] C² = 0` unless `8 ∣ w`. -/
theorem coeff_Cmain_sq_of_not_dvd {w : ℕ} (hw : ¬ 8 ∣ w) : (Cmain x z ^ 2).coeff w = 0 := by
  apply coeff_Cmain_sq_eq_zero
  intro μ _ hμ
  exact hw (hμ ▸ eight_dvd_W μ)

/-- `[X^w] C² = 0` for `w > 2M`. -/
theorem coeff_Cmain_sq_of_gt {w : ℕ} (hw : 2 * M m < w) : (Cmain x z ^ 2).coeff w = 0 := by
  apply coeff_Cmain_sq_eq_zero
  intro μ hμ hW
  have := W_le μ
  have : Multiset.card μ * M m ≤ 2 * M m := Nat.mul_le_mul_right _ hμ
  omega

/-- The coefficients of `C²` are nonnegative for nonnegative digits. -/
theorem coeff_Cmain_sq_nonneg (hx : 0 ≤ x) (hz : ∀ i, 0 ≤ z i) (w : ℕ) :
    0 ≤ (Cmain x z ^ 2).coeff w := by
  rw [coeff_Cmain_sq]
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · split_ifs <;> positivity
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> [exact mul_nonneg (mul_nonneg (by norm_num) hx) (hz i); exact le_rfl]
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by
      split_ifs <;> [exact mul_nonneg (hz i) (hz k); exact le_rfl]

theorem eval_one_Cmain : (Cmain x z).eval 1 = x + ∑ i, z i := by
  unfold Cmain; simp [eval_finset_sum]

/-! ### Monomial values -/

/-- The value of a row is the coefficient-weighted sum of the coefficients of `C²` at the
weights of its monomials. -/
theorem terms_sum_eq_val (R : Row m) (hcross : ∀ q ∈ R.cross, q.1 ≠ q.2.1) :
    ((terms R).map fun q => q.2 * (Cmain x z ^ 2).coeff (W q.1)).sum = R.val x z := by
  unfold terms Row.val
  simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Function.comp_def]
  have e1 : (R.sq.map fun p => p.2 * (Cmain x z ^ 2).coeff (W ({p.1, p.1} : Multiset (Fin m)))).sum =
      (R.sq.map fun p => p.2 * z p.1 ^ 2).sum := by
    congr 1; apply List.map_congr_left; intro p _
    rw [W_pair, ← two_mul, coeff_Cmain_sq_two_v]
  have e2 : (R.cross.map fun p => p.2.2 * (Cmain x z ^ 2).coeff (W ({p.1, p.2.1} : Multiset (Fin m)))).sum =
      (R.cross.map fun p => 2 * p.2.2 * z p.1 * z p.2.1).sum := by
    congr 1; apply List.map_congr_left; intro p hp
    rw [W_pair, coeff_Cmain_sq_add_v x z (hcross p hp)]; ring
  have e3 : (R.xz.map fun p => p.2 * (Cmain x z ^ 2).coeff (W ({p.1} : Multiset (Fin m)))).sum =
      (R.xz.map fun p => 2 * p.2 * x * z p.1).sum := by
    congr 1; apply List.map_congr_left; intro p _
    rw [W_singleton, coeff_Cmain_sq_v]; ring
  rw [e1, e2, e3, W_zero, coeff_Cmain_sq_zero]
  ring

/-- The group value. -/
def S (P : Fin 3 → Fin m) (z : Fin m → ℤ) : ℤ := z (P 0) + z (P 1) + z (P 2)

/-- The six helper complements of a group sum to the square of its value. -/
theorem pairs_sum_eq_sq (P : Fin 3 → Fin m) (hP : Function.Injective P) :
    ((pairs P).map fun π => (Cmain x z ^ 2).coeff (W π)).sum = S P z ^ 2 := by
  have h01 : P 0 ≠ P 1 := fun h => by have := hP h; simp at this
  have h02 : P 0 ≠ P 2 := fun h => by have := hP h; simp at this
  have h12 : P 1 ≠ P 2 := fun h => by have := hP h; simp at this
  unfold pairs S
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, W_pair]
  rw [← two_mul (v (P 0)), ← two_mul (v (P 1)), ← two_mul (v (P 2)), coeff_Cmain_sq_two_v,
    coeff_Cmain_sq_two_v, coeff_Cmain_sq_two_v, coeff_Cmain_sq_add_v x z h01,
    coeff_Cmain_sq_add_v x z h02, coeff_Cmain_sq_add_v x z h12]
  ring

end

end L90

end Jones1980
