import Diophantine.Paper1976.MR

/-!
# Jones 1978, Lemma 2.10: the `χ`-variant definition of `C = ψ_A(B)` (conditions Q1–Q4)

> **Lemma 2.10.** For `1 < A` and `0 < B`, `C = ψ_A(B)` iff there are nonnegative integers
> `D, E, F, G, H, I, i, j` with
> P1 `D ≤ I`, `F ∣ I − D`, `B ≤ C`; P2 `D² = (A²−1)C² + 1`; P3 `E = 2iC²`;
> P4 `F² = (A²−1)E² + 1`; P5 `G = A + F²(F² − A)`; P6 `H = B + 2jC`; P7 `I² = (G²−1)H² + 1`.

Eliminating `E, G, H, I` (with `I = D + τF`) gives the article's Q1–Q4:
Q1 `B ≤ C`; Q2 `D² = (A²−1)C² + 1`; Q3 `F² = 4(A²−1)i²C⁴ + 1`;
Q4 `(D + τF)² = ((A + F²(F² − A))² − 1)(B + 2jC)² + 1`.

Q4 is an equation over the integers: `F² − A` is negative when `i = 0` (then `F = 1`),
and the integer reading is what excludes that case.  With truncated natural-number
subtraction the system would have spurious solutions, e.g. `A = 2, B = 1, C = 4, D = 7,
F = 1, i = 0, j = 26, τ = 355`.

The article says the lemma "may be proved exactly as Lemma 2.9 is proved in [20]", with
Davis's step-down lemma for the `χ` sequence (Mathlib's `Pell.modEq_of_xn_modEq`) in place
of the one for `ψ`.  That is the proof given here.
-/

namespace Jones1978

open Pell Diophantine JSWW1976

/-- The conditions Q1–Q4. -/
structure QConds (A B C D F i j τ : ℕ) : Prop where
  Q1 : B ≤ C
  Q2 : D ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1
  Q3 : F ^ 2 = 4 * (A ^ 2 - 1) * i ^ 2 * C ^ 4 + 1
  Q4 : ((D : ℤ) + τ * F) ^ 2 =
    (((A : ℤ) + F ^ 2 * (F ^ 2 - A)) ^ 2 - 1) * ((B : ℤ) + 2 * j * C) ^ 2 + 1

/-- `χ_a(n) ≤ (2a)^n`. -/
theorem xn_le_pow {a : ℕ} (a1 : 1 < a) (n : ℕ) : xn a1 n ≤ (2 * a) ^ n := by
  have h1 : xn a1 n ≤ yn a1 (n + 1) := by
    rw [yn_succ]; exact Nat.le_add_right _ _
  exact h1.trans (ψ_succ_le_pow a1 n)

/-- A Pell pair from an equation `x² = (a²−1) y² + 1` in `ℕ`. -/
theorem eq_pell_of_sq {a x y : ℕ} (a1 : 1 < a) (h : x ^ 2 = (a ^ 2 - 1) * y ^ 2 + 1) :
    ∃ n, x = xn a1 n ∧ y = yn a1 n := by
  have hp : x * x - (a * a - 1) * y * y = 1 := by
    have : x * x = (a * a - 1) * y * y + 1 := by
      rw [← pow_two, h, pow_two a]; ring
    omega
  exact Pell.eq_pell a1 hp

/-- `G = A + F²(F² − A)`: `G ≡ A (mod F)` and `2C ∣ G − 1` when `2C ∣ E` and `E ∣ F² − 1`. -/
theorem G_facts {A C E F : ℕ} (hA : 1 < A) (hF : A + 1 ≤ F ^ 2) (hEF : E ∣ F ^ 2 - 1)
    (h2C : 2 * C ∣ E) :
    1 < A + F ^ 2 * (F ^ 2 - A) ∧ A ≡ A + F ^ 2 * (F ^ 2 - A) [MOD F] ∧
      2 * C ∣ A + F ^ 2 * (F ^ 2 - A) - 1 := by
  refine ⟨helper_G_gt hA hF, ?_, ?_⟩
  · refine (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 ?_
    rw [Nat.add_sub_cancel_left, pow_two]
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  · rw [helper_G_sub_one hF]
    exact (h2C.trans hEF).mul_right _

/-! ### Q1–Q4 ⟹ `C = ψ_A(B)` -/

set_option maxHeartbeats 1000000 in
theorem psi_of_QConds {A B C D F i j τ : ℕ} (hA : 1 < A) (hB : 0 < B)
    (h : QConds A B C D F i j τ) : C = ψ hA B := by
  obtain ⟨Q1, Q2, Q3, Q4⟩ := h
  have hC1 : 1 ≤ C := by omega
  -- the Pell pairs `(D, C)` and `(F, 2iC²)`
  obtain ⟨t₀, hD, hC⟩ := eq_pell_of_sq hA Q2
  obtain ⟨t', hF, hE⟩ := eq_pell_of_sq hA (y := 2 * i * C ^ 2)
    (by rw [Q3]; ring)
  -- `C = 1` is the trivial case
  rcases Nat.eq_or_lt_of_le hC1 with hC1' | hC2
  · have hB1 : B = 1 := by omega
    rw [hB1, ← hC1', ψ, yn_one]
  -- `C ≥ 2`: `t₀ ≥ 2`
  have ht₀ : 2 ≤ t₀ := by
    by_contra hlt
    push Not at hlt
    have : C ≤ 1 := by
      rw [hC]
      calc yn hA t₀ ≤ yn hA 1 := (strictMono_y hA).monotone (by omega)
        _ = 1 := yn_one hA
    omega
  -- `i ≥ 1` (the integer reading of Q4 excludes `i = 0`)
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exfalso
      have hF1 : F = 1 := by
        have : F ^ 2 = 1 := by rw [Q3]; ring
        nlinarith
      rw [hF1] at Q4
      push_cast at Q4
      have hG : ((A : ℤ) + 1 * (1 - A)) ^ 2 - 1 = 0 := by ring
      rw [hG, zero_mul, zero_add] at Q4
      have h0 : (0 : ℤ) ≤ (D : ℤ) + τ * 1 := by positivity
      have hDle : (D : ℤ) + τ * 1 ≤ 1 := by nlinarith
      have hD4 : 4 ≤ D ^ 2 := by
        rw [Q2]
        have : 3 ≤ A ^ 2 - 1 := by
          have : 4 ≤ A ^ 2 := by nlinarith
          omega
        have : 3 * 1 ≤ (A ^ 2 - 1) * C ^ 2 := Nat.mul_le_mul this (Nat.one_le_pow _ _ hC1)
        omega
      have hD2 : 2 ≤ D := by
        by_contra h
        push Not at h
        have : D ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have : (2 : ℤ) ≤ D := by exact_mod_cast hD2
      have : (0 : ℤ) ≤ τ := by positivity
      linarith
    · exact hi
  -- `E = ψ_A(t') ≥ 2C²`, `C ∣ t'`, `t' ≥ 1`, `F ≥ A`
  have hEpos : 0 < 2 * i * C ^ 2 := by positivity
  have ht'pos : 0 < t' := by
    by_contra h0
    push Not at h0
    have : t' = 0 := by omega
    rw [this, yn_zero] at hE
    omega
  have hCC : C * C ∣ 2 * i * C ^ 2 := ⟨2 * i, by ring⟩
  have hCt' : C ∣ t' := by
    rw [hE, hC] at hCC
    have := dvd_of_ysq_dvd hA hCC
    rwa [← hC] at this
  have hCt'le : C ≤ t' := Nat.le_of_dvd ht'pos hCt'
  have ht₀C : t₀ ≤ C := by rw [hC]; exact yn_ge_n hA t₀
  have hFA : A ≤ F := by
    rw [hF]
    calc A = xn hA 1 := (xn_one hA).symm
      _ ≤ xn hA t' := (strictMono_x hA).monotone ht'pos
  have hFA2 : A + 1 ≤ F ^ 2 := by nlinarith
  -- `G` as a natural number
  obtain ⟨G, hG⟩ : ∃ G, G = A + F ^ 2 * (F ^ 2 - A) := ⟨_, rfl⟩
  have hEF : 2 * i * C ^ 2 ∣ F ^ 2 - 1 := ⟨(A ^ 2 - 1) * (2 * i * C ^ 2), by rw [Q3]; rw [Nat.add_sub_cancel]; ring⟩
  have h2C : 2 * C ∣ 2 * i * C ^ 2 := ⟨i * C, by ring⟩
  obtain ⟨hG1, hGA, hG2C⟩ := G_facts hA hFA2 hEF h2C
  rw [← hG] at hG1 hGA hG2C
  have hGZ : (G : ℤ) = (A : ℤ) + F ^ 2 * (F ^ 2 - A) := by
    rw [hG]; push_cast [show A ≤ F ^ 2 by omega]; ring
  -- the Pell pair `(D + τF, B + 2jC)` for `G`
  have hQ4' : (D + τ * F) ^ 2 = (G ^ 2 - 1) * (B + 2 * j * C) ^ 2 + 1 := by
    have hG1' : 1 ≤ G ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hG1']
    rw [hGZ]
    exact Q4
  obtain ⟨t'', hI, hH⟩ := eq_pell_of_sq hG1 hQ4'
  -- `χ_A(t'') ≡ χ_A(t₀) (mod χ_A(t'))`
  have hIF : xn hG1 t'' ≡ xn hA t₀ [MOD F] := by
    rw [← hI, ← hD]
    show (D + τ * F) % F = D % F
    rw [mul_comm, Nat.add_mul_mod_self_left]
  have hxG : xn hA t'' ≡ xn hG1 t'' [MOD F] := (xy_modEq_of_modEq hA hG1 hGA t'').1
  have hstep : xn hA t'' ≡ xn hA t₀ [MOD xn hA t'] := by
    rw [← hF]; exact hxG.trans hIF
  have hcases := modEq_of_xn_modEq hA (by omega) (by omega) hstep
  -- `t'' ≡ B (mod 2C)`
  have hHB : yn hG1 t'' ≡ B [MOD 2 * C] := by
    rw [← hH]
    show (B + 2 * j * C) % (2 * C) = B % (2 * C)
    rw [show 2 * j * C = 2 * C * j by ring, Nat.add_mul_mod_self_left]
  have ht''B : t'' ≡ B [MOD 2 * C] :=
    (Nat.ModEq.of_dvd hG2C (yn_modEq_a_sub_one hG1 t'')).symm.trans hHB
  -- combine: `B ≡ ±t₀ (mod 2C)`
  have h2C4 : 2 * C ∣ 4 * t' := by
    obtain ⟨q, hq⟩ := hCt'
    exact ⟨2 * q, by rw [hq]; ring⟩
  have hBt₀ : B ≡ t₀ [MOD 2 * C] ∨ B + t₀ ≡ 0 [MOD 2 * C] := by
    rcases hcases with h1 | h1
    · left; exact ht''B.symm.trans (Nat.ModEq.of_dvd h2C4 h1)
    · right
      have h2 : t'' + t₀ ≡ 0 [MOD 2 * C] := Nat.ModEq.of_dvd h2C4 h1
      exact (Nat.ModEq.add_right t₀ ht''B).symm.trans h2
  rcases hBt₀ with h1 | h1
  · -- `B = t₀`
    have : B = t₀ := Nat.ModEq.eq_of_lt_of_lt h1 (by omega) (by omega)
    rw [this, hC]
  · -- `B + t₀ = 2C` forces `B = t₀ = C`, impossible for `C ≥ 2`
    exfalso
    have hdvd : 2 * C ∣ B + t₀ := (Nat.modEq_zero_iff_dvd).1 h1
    have hle : B + t₀ ≤ 2 * C := by omega
    have hpos : 0 < B + t₀ := by omega
    have heq : B + t₀ = 2 * C := by
      obtain ⟨q, hq⟩ := hdvd
      have hq1 : q = 1 := by
        rcases Nat.lt_or_ge q 2 with hq2 | hq2
        · interval_cases q <;> omega
        · exfalso
          have := Nat.mul_le_mul_left (2 * C) hq2
          omega
      rw [hq1] at hq
      omega
    have ht₀C' : t₀ = C := by omega
    have := lt_yn_of_two_le hA (n := C) hC2
    rw [← ht₀C', ← hC] at this
    omega

/-! ### `C = ψ_A(B)` ⟹ Q1–Q4 -/

set_option maxHeartbeats 1000000 in
theorem exists_QConds_of_psi {A B : ℕ} (hA : 1 < A) (hB : 0 < B) :
    ∃ D F i j τ, QConds A B (ψ hA B) D F i j τ := by
  obtain ⟨C, hC⟩ : ∃ C, C = ψ hA B := ⟨_, rfl⟩
  rw [← hC]
  have hC1 : 1 ≤ C := by rw [hC]; exact le_trans hB (yn_ge_n hA B)
  have hA2 : 1 ≤ A ^ 2 - 1 := by
    have : 4 ≤ A ^ 2 := by nlinarith
    omega
  -- `E = ψ_A(t')` a positive multiple of `2C²`
  obtain ⟨t', ht'pos, i, hi⟩ := exists_dvd_yn hA (by positivity : 0 < 2 * C ^ 2)
  obtain ⟨F, hF⟩ : ∃ F, F = xn hA t' := ⟨_, rfl⟩
  have hQ3 : F ^ 2 = 4 * (A ^ 2 - 1) * i ^ 2 * C ^ 4 + 1 := by
    have h := χ_sq hA t'
    simp only [ψ, χ] at h
    rw [hi] at h
    rw [hF, pow_two, h]
    have : A * A - 1 = A ^ 2 - 1 := by rw [pow_two]
    rw [this]; ring
  have hFA : A ≤ F := by
    rw [hF]
    calc A = xn hA 1 := (xn_one hA).symm
      _ ≤ xn hA t' := (strictMono_x hA).monotone ht'pos
  have hFA2 : A + 1 ≤ F ^ 2 := by nlinarith
  have hEF : 2 * C ^ 2 * i ∣ F ^ 2 - 1 :=
    ⟨2 * (A ^ 2 - 1) * i * C ^ 2, by rw [hQ3, Nat.add_sub_cancel]; ring⟩
  have h2C : 2 * C ∣ 2 * C ^ 2 * i := ⟨C * i, by ring⟩
  obtain ⟨G, hG⟩ : ∃ G, G = A + F ^ 2 * (F ^ 2 - A) := ⟨_, rfl⟩
  obtain ⟨hG1, hGA, hG2C⟩ := G_facts hA hFA2 hEF h2C
  rw [← hG] at hG1 hGA hG2C
  have hGZ : (G : ℤ) = (A : ℤ) + F ^ 2 * (F ^ 2 - A) := by
    rw [hG]; push_cast [show A ≤ F ^ 2 by omega]; ring
  -- `D = χ_A(B)`, `H = ψ_G(B)`, `I = χ_G(B)`
  obtain ⟨D, hD⟩ : ∃ D, D = xn hA B := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = yn hG1 B := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = xn hG1 B := ⟨_, rfl⟩
  -- `I ≡ D (mod F)` and `D ≤ I`
  have hID : I ≡ D [MOD F] := by
    rw [hI, hD]; exact ((xy_modEq_of_modEq hA hG1 hGA B).1).symm
  have hDI : D ≤ I := by
    have h1 : D ≤ (2 * A) ^ B := by rw [hD]; exact xn_le_pow hA B
    have h2 : (2 * A) ^ B ≤ G ^ B := by
      apply Nat.pow_le_pow_left
      rw [hG]
      have : F ^ 2 ≤ F ^ 2 * (F ^ 2 - A) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h3 : G ^ B ≤ I := by rw [hI]; exact xn_ge_a_pow hG1 B
    omega
  obtain ⟨τ, hτ⟩ := (Nat.modEq_iff_dvd' hDI).1 hID.symm
  -- `H ≡ B (mod 2C)` and `B ≤ H`
  have hHB : H ≡ B [MOD 2 * C] := by
    rw [hH]; exact Nat.ModEq.of_dvd hG2C (yn_modEq_a_sub_one hG1 B)
  have hBH : B ≤ H := by rw [hH]; exact yn_ge_n hG1 B
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hBH).1 hHB.symm
  refine ⟨D, F, i, j, τ, ⟨?_, ?_, hQ3, ?_⟩⟩
  · rw [hC]; exact yn_ge_n hA B
  · have h := χ_sq hA B
    simp only [ψ, χ] at h
    rw [hD, pow_two, hC, h]
    simp only [ψ]
    have : A * A - 1 = A ^ 2 - 1 := by rw [pow_two]
    rw [this]; ring
  · have hIeq : I = D + τ * F := by rw [mul_comm]; omega
    have hHeq : H = B + 2 * j * C := by
      rw [show 2 * j * C = 2 * C * j by ring]; omega
    have h := χ_sq hG1 B
    simp only [ψ, χ] at h
    rw [← hI, ← hH] at h
    have hG1' : 1 ≤ G * G := by nlinarith
    have hZ : (I : ℤ) ^ 2 = ((G : ℤ) ^ 2 - 1) * H ^ 2 + 1 := by
      have : ((I * I : ℕ) : ℤ) = (((G * G - 1) * H * H + 1 : ℕ) : ℤ) := by exact_mod_cast h
      push_cast [hG1'] at this
      linear_combination this
    rw [← hGZ]
    have e1 : ((D : ℤ) + τ * F) = I := by rw [hIeq]; push_cast; ring
    have e2 : ((B : ℤ) + 2 * j * C) = H := by rw [hHeq]; push_cast; ring
    rw [e1, e2]
    exact hZ

/-- **Lemma 2.10** (in the form Q1–Q4). -/
theorem lemma_2_10 {A B : ℕ} (hA : 1 < A) (hB : 0 < B) (C : ℕ) :
    C = ψ hA B ↔ ∃ D F i j τ, QConds A B C D F i j τ :=
  ⟨fun h => h ▸ exists_QConds_of_psi hA hB, fun ⟨_, _, _, _, _, h⟩ => psi_of_QConds hA hB h⟩

end Jones1978
