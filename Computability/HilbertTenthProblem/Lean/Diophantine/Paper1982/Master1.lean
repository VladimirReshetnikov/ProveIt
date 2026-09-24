import Diophantine.Paper1982.Section4

/-!
# Jones 1982, §4: the index triple, the code and the criterion for a solution

With `δ = 4` and `L = 5^(ν+1)`:

* `Index ν P z u y` is (4.1): `z pow 2`, `z > 1 + max* |P_i|`, `u = Σ_{i=1}^ν (2z)^(5^i)`,
  `y = Σ* (z + P_i)(2z)^(L − e(i))`;
* `Wset P x` is `x ∈ W_{⟨z,u,y⟩}`: `P(x, z₁, …, z_ν) = 0` for some `z₁, …, z_ν ≥ 0`;
* `Normalized P` is the normalization of §3, `P(x, 0, …, 0) ≠ 0`, under which the unknown
  `g` of the systems is positive;
* `tau3_iff` is (4.10)/(4.11): for a code `c = 1 + xB + g` of `z₀ = x, z₁, …, z_ν < b`,
  `τ₂(S₃, T₃) = 0 ⟺ P(z₀, …, z_ν) = 0`, where `S₃ = −2c⁴D₀ + Bλ(1 + q⁴)`, `T₃ = (B − 2)q`.
-/

namespace Jones1982

open Polynomial Finset

/-- `L = 5^(ν+1)` (`δ = 4`). -/
abbrev L4 (ν : ℕ) : ℕ := Lexp ν 4

theorem L4_eq (ν : ℕ) : L4 ν = 5 ^ (ν + 1) := rfl

/-- (4.1): the index triple `⟨z, u, y⟩` of the polynomial `P` (`δ = 4`). -/
structure Index (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z u y : ℕ) : Prop where
  pow2 : ∃ s, z = 2 ^ s
  big : ∀ k ∈ star ν 4, |Pcoef ν P k| + 1 < z
  hu : (u : ℤ) = (lpoly ν 4).eval (2 * z : ℤ)
  hy : (y : ℤ) = (epoly ν 4 P z).eval (2 * z : ℤ)

/-- `x ∈ W_{⟨z,u,y⟩}`: `P(x, z₁, …, z_ν) = 0` has a solution in nonnegative integers. -/
def Wset {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ) (x : ℕ) : Prop :=
  ∃ zs : Fin (ν + 1) → ℕ, zs 0 = x ∧ MvPolynomial.eval (fun j => (zs j : ℤ)) P = 0

/-- The normalization of §3: `P(x, 0, …, 0) ≠ 0` for all `x`. -/
def Normalized {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ) : Prop :=
  ∀ x : ℕ, MvPolynomial.eval (fun j : Fin (ν + 1) => if j = 0 then (x : ℤ) else 0) P ≠ 0

section Index

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

theorem Index.two_le (hI : Index ν P z u y) : 2 ≤ z := by
  have hk : (fun _ => 0 : Fin (ν + 2) → ℕ) + Pi.single 0 4 ∈ star ν 4 := by
    rw [mem_star]; simp
  have := hI.big _ hk
  have := abs_nonneg (Pcoef ν P ((fun _ => 0 : Fin (ν + 2) → ℕ) + Pi.single 0 4))
  omega

theorem Index.Pcoef_le (hI : Index ν P z u y) {k : Fin (ν + 2) → ℕ} (hk : k ∈ star ν 4) :
    |Pcoef ν P k| ≤ z := by
  have := hI.big k hk; omega

/-- The coefficients of `epoly` lie in `[0, 2z)` (they are `0` or `z + P_k`). -/
theorem Index.coeff_epoly_bounds (hI : Index ν P z u y) (i : ℕ) :
    0 ≤ (epoly ν 4 P z).coeff i ∧ (epoly ν 4 P z).coeff i < 2 * z := by
  by_cases h : ∃ k ∈ star ν 4, L4 ν - expo ν 4 k = i
  · obtain ⟨k, hk, rfl⟩ := h
    rw [coeff_epoly_of_mem ν 4 P z hk]
    have := hI.big k hk
    have := abs_lt.1 (show |Pcoef ν P k| < z by omega)
    constructor <;> push_cast <;> linarith
  · push Not at h
    rw [coeff_epoly_of_not ν 4 P z h]
    have := hI.two_le
    constructor <;> push_cast <;> linarith

/-- The digit at `L` of `y` (the term `k = (4, 0, …, 0)`) is `z + P_k ≥ 2`, so `y ≥ 2(2z)^L`. -/
theorem Index.y_ge (hI : Index ν P z u y) : 2 * (2 * z) ^ L4 ν ≤ y := by
  obtain ⟨k₀, hk₀, hexp⟩ : ∃ k₀ ∈ star ν 4, expo ν 4 k₀ = 0 :=
    ⟨(fun _ => 0 : Fin (ν + 2) → ℕ) + Pi.single 0 4, by rw [mem_star]; simp, by simp [expo]⟩
  have hyZ := hI.hy
  rw [eval_epoly] at hyZ
  have h1 : ((z : ℤ) + Pcoef ν P k₀) * (2 * z : ℤ) ^ (L4 ν - expo ν 4 k₀) ≤
      ∑ k ∈ star ν 4, ((z : ℤ) + Pcoef ν P k) * (2 * z : ℤ) ^ (L4 ν - expo ν 4 k) := by
    apply Finset.single_le_sum (f := fun k => ((z : ℤ) + Pcoef ν P k) * (2 * z : ℤ) ^ (L4 ν - expo ν 4 k))
      (fun k hk => ?_) hk₀
    have := hI.big k hk
    have := abs_lt.1 (show |Pcoef ν P k| < z by omega)
    apply mul_nonneg (by linarith) (by positivity)
  rw [hexp, Nat.sub_zero] at h1
  have h2 : (2 : ℤ) ≤ (z : ℤ) + Pcoef ν P k₀ := by
    have := hI.big k₀ hk₀
    have := abs_lt.1 (show |Pcoef ν P k₀| < z by omega)
    have : (1 : ℤ) ≤ z - |Pcoef ν P k₀| := by
      have := hI.big k₀ hk₀; push_cast at this ⊢; linarith
    have := neg_abs_le (Pcoef ν P k₀)
    linarith
  have h3 : (2 : ℤ) * (2 * z : ℤ) ^ L4 ν ≤ ((z : ℤ) + Pcoef ν P k₀) * (2 * z : ℤ) ^ L4 ν :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : (2 : ℤ) * (2 * z : ℤ) ^ L4 ν ≤ y := by rw [hyZ]; linarith
  exact_mod_cast h4

theorem Index.y_pos (hI : Index ν P z u y) : 0 < y := by
  have := hI.y_ge
  have hz := hI.two_le
  have : 0 < (2 * z) ^ L4 ν := pow_pos (by omega) _
  omega

theorem Index.two_z_le_y (hI : Index ν P z u y) : 2 * z ≤ y := by
  have h1 := hI.y_ge
  have h2 : 2 * z ≤ (2 * z) ^ L4 ν := Nat.le_self_pow (by positivity) _
  omega

/-- `y < (2z)^(L+1)` (at most `L + 1` digits). -/
theorem Index.y_lt (hI : Index ν P z u y) : y < (2 * z) ^ (L4 ν + 1) := by
  have hz := hI.two_le
  have hyZ : (y : ℤ) = ((Nat.ofDigits (2 * z) (coeffList (epoly ν 4 P z) (L4 ν + 1)) : ℕ) : ℤ) := by
    rw [ofDigits_coeffList_eq_eval _ (fun i => (hI.coeff_epoly_bounds i).1) _
      (lt_of_le_of_lt (natDegree_epoly_le ν 4 P z) (Nat.lt_succ_self _)), hI.hy]
    push_cast; rfl
  have hy : y = Nat.ofDigits (2 * z) (coeffList (epoly ν 4 P z) (L4 ν + 1)) := by exact_mod_cast hyZ
  rw [hy]
  have := Nat.ofDigits_lt_base_pow_length (b := 2 * z) (l := coeffList (epoly ν 4 P z) (L4 ν + 1))
    (by omega) (fun x hx => by
      obtain ⟨i, -, rfl⟩ := mem_coeffList hx
      have := hI.coeff_epoly_bounds i
      rw [Int.toNat_lt this.1]; push_cast; exact this.2)
  rwa [coeffList_length] at this

/-- `2z(ν+2)⁴ < y` (used for the bound `|hⱼ| < B/2`). -/
theorem Index.y_big (hI : Index ν P z u y) (hν : 1 ≤ ν) : 2 * z * (ν + 2) ^ 4 < y := by
  have hz := hI.two_le
  have h1 := hI.y_ge
  -- `(2z)^L ≥ 4^(L-1) · 2z` and `4^(L-1) ≥ 4 (ν+2)^4`
  have hL : 4 * (ν + 1) + 2 ≤ L4 ν := by
    rw [L4_eq]
    have : ∀ n, 1 ≤ n → 4 * (n + 1) + 2 ≤ 5 ^ (n + 1) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n _ ih => rw [pow_succ]; omega
    exact this ν hν
  have h2 : (ν + 2) ^ 4 ≤ (4 ^ (ν + 1)) ^ 4 := by
    apply Nat.pow_le_pow_left
    have : ν + 2 ≤ 2 ^ (ν + 1) := by
      have := Nat.lt_two_pow_self (n := ν + 1); omega
    have : 2 ^ (ν + 1) ≤ 4 ^ (ν + 1) := Nat.pow_le_pow_left (by norm_num) _
    omega
  have h3 : 4 * (ν + 2) ^ 4 ≤ 4 ^ (L4 ν - 1) := by
    calc 4 * (ν + 2) ^ 4 ≤ 4 * (4 ^ (ν + 1)) ^ 4 := Nat.mul_le_mul_left _ h2
      _ = 4 ^ (4 * (ν + 1) + 1) := by rw [← pow_mul, pow_succ]; ring
      _ ≤ 4 ^ (L4 ν - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ^ (L4 ν - 1) ≤ (2 * z) ^ (L4 ν - 1) := Nat.pow_le_pow_left (by omega) _
  have h5 : (2 * z) ^ L4 ν = (2 * z) ^ (L4 ν - 1) * (2 * z) := by
    rw [← pow_succ]; congr 1; omega
  have h6 : 4 * (ν + 2) ^ 4 * (2 * z) ≤ (2 * z) ^ L4 ν := by
    rw [h5]; exact Nat.mul_le_mul_right _ (h3.trans h4)
  have h7 : 0 < (ν + 2) ^ 4 := by positivity
  nlinarith

end Index

/-! ### The coefficients of `lpoly` -/

theorem coeff_lpoly_of_mem (ν : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 ν) :
    (lpoly ν 4).coeff (5 ^ i) = 1 := by
  unfold lpoly
  rw [finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_X_pow, if_pos rfl]
  · intro i' _ hne
    rw [coeff_X_pow, if_neg]
    intro h'
    exact hne (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h'.symm)
  · intro h; exact absurd hi h

theorem coeff_lpoly_of_not (ν : ℕ) {j : ℕ} (hj : ¬ ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j) :
    (lpoly ν 4).coeff j = 0 := by
  unfold lpoly
  rw [finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [coeff_X_pow, if_neg]
  intro h'
  exact hj ⟨i, hi, h'.symm⟩

theorem coeff_lpoly_bounds (ν : ℕ) (j : ℕ) :
    0 ≤ (lpoly ν 4).coeff j ∧ (lpoly ν 4).coeff j ≤ 1 := by
  by_cases h : ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j
  · obtain ⟨i, hi, rfl⟩ := h
    rw [coeff_lpoly_of_mem ν hi]; norm_num
  · rw [coeff_lpoly_of_not ν h]; norm_num

theorem natDegree_lpoly_le (ν : ℕ) : (lpoly ν 4).natDegree ≤ 5 ^ ν := by
  unfold lpoly
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact (natDegree_X_pow_le _).trans (Nat.pow_le_pow_right (by norm_num) hi.2)

theorem five_pow_le_L4 (ν : ℕ) : 5 ^ ν ≤ L4 ν := by
  rw [L4_eq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The polynomial `g = Σ_{i=1}^ν zᵢ X^(5^i)` -/

/-- `g(X) = Σ_{j ≠ 0} z_j X^(5^j)`, so that `c = 1 + xB + g(B)`. -/
noncomputable def gpoly (ν : ℕ) (zs : Fin (ν + 1) → ℕ) : ℤ[X] :=
  ∑ j : Fin (ν + 1), if j = 0 then 0 else C (zs j : ℤ) * X ^ (5 ^ (j : ℕ))

/-- The positions `5^i`, `1 ≤ i ≤ ν`, are the `5^j` for `j : Fin (ν+1)`, `j ≠ 0`. -/
theorem exists_Icc_iff (ν j : ℕ) :
    (∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j) ↔ ∃ j' : Fin (ν + 1), j' ≠ 0 ∧ 5 ^ (j' : ℕ) = j := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_Icc] at hi
    exact ⟨⟨i, by omega⟩, by simp [Fin.ext_iff]; omega, rfl⟩
  · rintro ⟨j', hj', rfl⟩
    refine ⟨j', Finset.mem_Icc.2 ⟨?_, by omega⟩, rfl⟩
    have : (j' : ℕ) ≠ 0 := fun h => hj' (Fin.ext h)
    omega

theorem coeff_gpoly_of_ne (ν : ℕ) (zs : Fin (ν + 1) → ℕ) {j : Fin (ν + 1)} (hj : j ≠ 0) :
    (gpoly ν zs).coeff (5 ^ (j : ℕ)) = (zs j : ℤ) := by
  unfold gpoly
  rw [finset_sum_coeff, Finset.sum_eq_single j]
  · rw [if_neg hj, coeff_C_mul_X_pow, if_pos rfl]
  · intro j' _ hne
    split_ifs with h
    · simp
    · rw [coeff_C_mul_X_pow, if_neg]
      intro h'
      exact hne (Fin.ext (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h'.symm))
  · intro h; exact absurd (Finset.mem_univ j) h

theorem coeff_gpoly_of_not (ν : ℕ) (zs : Fin (ν + 1) → ℕ) {j : ℕ}
    (hj : ¬ ∃ j' : Fin (ν + 1), j' ≠ 0 ∧ 5 ^ (j' : ℕ) = j) : (gpoly ν zs).coeff j = 0 := by
  unfold gpoly
  rw [finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j' _
  split_ifs with h
  · simp
  · rw [coeff_C_mul_X_pow, if_neg]
    intro h'
    exact hj ⟨j', h, h'.symm⟩

theorem coeff_gpoly_nonneg (ν : ℕ) (zs : Fin (ν + 1) → ℕ) (j : ℕ) :
    0 ≤ (gpoly ν zs).coeff j := by
  by_cases h : ∃ j' : Fin (ν + 1), j' ≠ 0 ∧ 5 ^ (j' : ℕ) = j
  · obtain ⟨j', hj', rfl⟩ := h
    rw [coeff_gpoly_of_ne ν zs hj']; positivity
  · rw [coeff_gpoly_of_not ν zs h]

theorem natDegree_gpoly_le (ν : ℕ) (zs : Fin (ν + 1) → ℕ) : (gpoly ν zs).natDegree ≤ 5 ^ ν := by
  unfold gpoly
  apply natDegree_sum_le_of_forall_le
  intro j _
  split_ifs
  · simp
  · exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `c = 1 + xB + g(B)`: the code polynomial evaluated at `B`. -/
theorem eval_cpoly_eq (ν : ℕ) (zs : Fin (ν + 1) → ℕ) (B : ℤ) :
    (cpoly ν 4 zs).eval B = 1 + (zs 0 : ℤ) * B + (gpoly ν zs).eval B := by
  rw [eval_cpoly]
  unfold gpoly
  rw [eval_finset_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, pow_one, eval_zero, zero_add, if_true, ite_true,
    if_neg (Fin.succ_ne_zero _), eval_mul, eval_C, eval_pow, eval_X, Fin.isValue]
  ring

end Jones1982
