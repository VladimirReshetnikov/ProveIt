import GowersSzemeredi.Proofs16ExplicitVarietyDecomposition

/-! Upper bounds for the named constants of the variety route.

The four constants `explicitLiftK`, `explicitLiftP`, `explicitVarietyK`,
`explicitVarietyP` are built from the per-degree Schmidt constants
`schmidtMonomialK j` and `schmidtMonomialP j`, `j ≤ 2`:
* `schmidt_base_formula_le`: the formula of `schmidtRecurrenceBase C e` is at
  most `2^1600` when `C ≤ 2^704` and `e ≤ 256`. It is stated without the
  port's names, so it is checked locally.
* `uniformSchmidtK_le_of`, `uniformSchmidtP_le_of`,
  `multiaffinePartitionK_le_of`, `multiaffinePartitionP_le_pow`: monotone
  bookkeeping for the uniformization and the multiaffine recursion.
* `explicit_constants_le_of`: from `schmidtMonomialK j ≤ 2^1600` and
  `schmidtMonomialP j ≤ 3878` for `j ≤ 2`, all four constants are at most
  `2^1700`.

The per-degree bounds themselves unfold the port's definitions and are proved
on the full-verification host (`Proofs16VarietyTheoremThree`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The Schmidt base formula is at most `2^1600`.** -/
theorem schmidt_base_formula_le (C e : Nat) (hC : (C : Real) ≤ 2 ^ 704) (he : e ≤ 256) :
    2 + 121 * Real.exp 10 + (10 + 8 * Real.exp (4 * Real.pi + 1)) *
        (1 + 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e) +
      ((15 * (e + 1) + 23 : Nat) : Real) ≤ 2 ^ 1600 := by
  have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hexp : ∀ n : Nat, Real.exp n ≤ 3 ^ n := fun n => by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he1 n
  have h10 : Real.exp 10 ≤ 3 ^ 10 := by exact_mod_cast hexp 10
  have h14 : Real.exp (4 * Real.pi + 1) ≤ 3 ^ 14 := by
    have hpi := Real.pi_lt_d2
    calc Real.exp (4 * Real.pi + 1) ≤ Real.exp 14 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 ^ 14 := by exact_mod_cast hexp 14
  have h4 : Real.exp Real.pi ≤ 81 := by
    have hpi := Real.pi_lt_d2
    calc Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 ^ 4 := by exact_mod_cast hexp 4
      _ = 81 := by norm_num
  have h8 : (8 : Real) ^ e ≤ 2 ^ 768 := by
    calc (8 : Real) ^ e ≤ 8 ^ 256 := pow_le_pow_right₀ (by norm_num) he
      _ = 2 ^ 768 := by rw [show (8 : Real) = 2 ^ 3 by norm_num, ← pow_mul]
  have hEe : ((15 * (e + 1) + 23 : Nat) : Real) ≤ 4096 := by
    have : 15 * (e + 1) + 23 ≤ 4096 := by omega
    exact_mod_cast this
  -- the large powers stay atoms
  have hsplit : (2 : Real) ^ 1600 = 2 ^ 704 * 2 ^ 768 * 2 ^ 128 := by
    rw [← pow_add, ← pow_add]
  rw [hsplit]
  obtain ⟨a, ha⟩ : ∃ a, (2 : Real) ^ 704 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (2 : Real) ^ 768 = b := ⟨_, rfl⟩
  rw [ha] at hC ⊢
  rw [hb] at h8 ⊢
  have ha1 : 1 ≤ a := by rw [← ha]; exact one_le_pow₀ (by norm_num)
  have hb1 : 1 ≤ b := by rw [← hb]; exact one_le_pow₀ (by norm_num)
  -- equations between huge numerals derail `linarith`; drop them
  clear hsplit ha hb
  have hC0 : (0 : Real) ≤ C := Nat.cast_nonneg C
  have h8e : (0 : Real) ≤ 8 ^ e := by positivity
  have hpi0 : 0 ≤ Real.exp Real.pi := (Real.exp_pos _).le
  have hinner : 1 + 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e ≤ 256 * (a * b) := by
    have hCe : (C : Real) * 8 ^ e ≤ a * b := mul_le_mul hC h8 h8e (by linarith)
    have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha1 hb1
    have : 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e ≤ 162 * (a * b) := by
      calc 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e
          = 2 * Real.exp Real.pi * ((C : Real) * 8 ^ e) := by ring
        _ ≤ 2 * 81 * (a * b) :=
          mul_le_mul (by linarith) hCe (by positivity) (by norm_num)
        _ = 162 * (a * b) := by ring
    linarith
  have houter : 10 + 8 * Real.exp (4 * Real.pi + 1) ≤ 2 ^ 26 := by
    have : (10 : Real) + 8 * 3 ^ 14 ≤ 2 ^ 26 := by norm_num
    linarith
  have hprod : (10 + 8 * Real.exp (4 * Real.pi + 1)) *
      (1 + 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e) ≤ 2 ^ 26 * (256 * (a * b)) :=
    mul_le_mul houter hinner (by positivity) (by positivity)
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha1 hb1
  have h121 : 2 + 121 * Real.exp 10 ≤ 2 ^ 23 := by
    have : (2 : Real) + 121 * 3 ^ 10 ≤ 2 ^ 23 := by norm_num
    linarith
  have hfinal : (2 : Real) ^ 23 + 2 ^ 26 * (256 * (a * b)) + 4096 ≤ a * b * 2 ^ 128 := by
    have : (2 : Real) ^ 23 + 4096 ≤ 2 ^ 24 * (a * b) := by nlinarith
    have h2 : (2 : Real) ^ 26 * 256 + 2 ^ 24 ≤ 2 ^ 128 := by norm_num
    nlinarith
  linarith

/-- The uniform base constant is at most `1 + k·B` under per-degree bounds `B`. -/
theorem uniformSchmidtK_le_of {k : Nat} {B : Real} (hB : ∀ j : Fin k, schmidtMonomialK j ≤ B) :
    uniformSchmidtK k ≤ 1 + k * B := by
  unfold uniformSchmidtK
  have : ∑ j : Fin k, schmidtMonomialK j ≤ ∑ _j : Fin k, B := Finset.sum_le_sum fun j _ => hB j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

/-- The uniform exponent constant is at most `1 + k·B` under per-degree bounds `B`. -/
theorem uniformSchmidtP_le_of {k B : Nat} (hB : ∀ j : Fin k, schmidtMonomialP j ≤ B) :
    uniformSchmidtP k ≤ 1 + k * B := by
  unfold uniformSchmidtP
  have : ∑ j : Fin k, schmidtMonomialP j ≤ ∑ _j : Fin k, B := Finset.sum_le_sum fun j _ => hB j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- The multiaffine base constant stays below any bound `B ≥ 2` on the uniform one. -/
theorem multiaffinePartitionK_le_of {k : Nat} {B : Real} (hB : uniformSchmidtK k ≤ B) (h2 : 2 ≤ B)
    (h : Nat) : multiaffinePartitionK k h ≤ B := by
  induction h with
  | zero => exact h2
  | succ h ih => exact max_le ih hB

/-- The multiaffine exponent constant is at most `(2(k+1)·P + 4)^h`. -/
theorem multiaffinePartitionP_le_pow (k h : Nat) :
    multiaffinePartitionP k h ≤ (2 * (k + 1) * uniformSchmidtP k + 4) ^ h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih =>
    show multiaffinePartitionP k h * (2 * (k + 1) * uniformSchmidtP k + 4) ≤ _
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ ih

/-- **The four named constants are at most `2^1700`**, given per-degree bounds. -/
theorem explicit_constants_le_of
    (hK : ∀ j : Nat, j ≤ 2 → schmidtMonomialK j ≤ 2 ^ 1600)
    (hP : ∀ j : Nat, j ≤ 2 → schmidtMonomialP j ≤ 3878) :
    (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700 := by
  have hbig : (2 : Real) ^ 1700 = 2 ^ 1600 * 2 ^ 100 := by rw [← pow_add]
  have h100a : (2 : Real) ^ 100 ≤ 2 ^ 1600 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a, (2 : Real) ^ 1600 = a := ⟨_, rfl⟩
  rw [ha] at hK h100a
  have ha1 : (1 : Real) ≤ a := le_trans (by norm_num) h100a
  rw [hbig, ha]
  clear hbig ha
  have h100 : (16 : Real) ≤ 2 ^ 100 := by norm_num
  -- base constants
  have hU : ∀ k : Nat, k ≤ 3 → uniformSchmidtK k ≤ 4 * a := by
    intro k hk
    refine (uniformSchmidtK_le_of (B := a) fun j => hK j (by have := j.isLt; omega)).trans ?_
    have : (k : Real) ≤ 3 := by exact_mod_cast hk
    nlinarith
  have hMK : ∀ k h : Nat, k ≤ 3 → multiaffinePartitionK k h ≤ 4 * a := fun k h hk =>
    multiaffinePartitionK_le_of (hU k hk) (by linarith) h
  have hceil : ∀ k h : Nat, k ≤ 3 →
      ((Nat.ceil (multiaffinePartitionK k h) : Nat) : Real) ≤ a * 2 ^ 100 := by
    intro k h hk
    have hc := Nat.ceil_lt_add_one (show 0 ≤ multiaffinePartitionK k h by
      linarith [two_le_multiaffinePartitionK k h])
    have := hMK k h hk
    nlinarith
  -- exponent constants
  have hUP : ∀ k : Nat, k ≤ 3 → uniformSchmidtP k ≤ 11635 := by
    intro k hk
    have := uniformSchmidtP_le_of (k := k) (B := 3878) fun j => hP j (by have := j.isLt; omega)
    have : k * 3878 ≤ 3 * 3878 := Nat.mul_le_mul_right _ hk
    omega
  have hLP : explicitLiftP ≤ 3 * 93084 ^ 8 := by
    unfold explicitLiftP
    have h1 := multiaffinePartitionP_le_pow (2 + 1) (2 ^ (2 + 1))
    have h2 : 2 * (2 + 1 + 1) * uniformSchmidtP (2 + 1) + 4 ≤ 93084 := by
      have := hUP (2 + 1) le_rfl; omega
    have h3 := Nat.pow_le_pow_left h2 (2 ^ (2 + 1))
    have := Nat.mul_le_mul_left (2 + 1) (h1.trans h3)
    simpa using this
  have hVP : explicitVarietyP ≤ 93084 ^ 4 := by
    unfold explicitVarietyP
    have h1 := multiaffinePartitionP_le_pow 2 (2 ^ 2)
    have h2 : 2 * (2 + 1) * uniformSchmidtP 2 + 4 ≤ 93084 := by
      have := hUP 2 (by norm_num); omega
    have h3 := Nat.pow_le_pow_left h2 (2 ^ 2)
    simpa using h1.trans h3
  have hsmall : (3 * 93084 ^ 8 : Real) ≤ a * 2 ^ 100 := by
    have : (3 * 93084 ^ 8 : Real) ≤ 2 ^ 100 * 2 ^ 100 := by norm_num
    exact this.trans (mul_le_mul_of_nonneg_right h100a (by norm_num))
  refine ⟨hceil _ _ (by norm_num), ?_, hceil _ _ (by norm_num), ?_⟩
  · exact (show (explicitLiftP : Real) ≤ 3 * 93084 ^ 8 by exact_mod_cast hLP).trans hsmall
  · calc (explicitVarietyP : Real) ≤ 93084 ^ 4 := by exact_mod_cast hVP
      _ ≤ 3 * 93084 ^ 8 := by norm_num
      _ ≤ a * 2 ^ 100 := hsmall

end LeanProofs.GowersSzemeredi
