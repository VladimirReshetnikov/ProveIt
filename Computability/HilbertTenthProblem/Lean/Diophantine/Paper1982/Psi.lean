import Diophantine.Paper1978.Lemma210

/-!
# Jones 1982, Lemma 2.28 and Corollary 2.29: `C = ψ_A(B)` defined modulo `C`

> **Lemma 2.28.** For `1 < A`, `1 < B ≤ C` and either `2B ≤ C` or `B` odd, `C = ψ_A(B)` iff
> there exist positive integers `D, F, i, j` such that
> (P1) `F ∣ I − D`, (P2) `D² = (A²−1)C² + 1`, (P3) `E = iC²`, (P4) `F² = (A²−1)E² + 1`,
> (P5) `G = A + F²(D² − A)`, (P6) `H = B + jC`, (P7) `I² = (G²−1)H² + 1`.
> *Remark.* The proof is similar to that in [15] except that again we work modulo `C`
> instead of `2C`; instead of the `ψ` form of the second step-down lemma one uses the `χ`
> form.  Of course (P5) may be replaced by `G = A + F²(F² − A)`.
>
> **Corollary 2.29.** Under the same hypotheses, `C = ψ_A(B)` iff there exist positive
> integers `D, F, i, j, o` with (Q1) `D² = (A²−1)C² + 1`, (Q2) `F² = (A²−1)i²C⁴ + 1`,
> (Q3) `(D + oF)² = ((A + F²(D² − A))² − 1)(B + jC)² + 1`.

The proof follows the 1978 Lemma 2.10 (`Jones1978.psi_of_QConds`, modulo `2C`).  Working
modulo `C` leaves the extra case `B + t₀ = C` (with `C = ψ_A(t₀)`). Parity excludes
this case when `B` is odd. When `2B ≤ C`, the bound `ψ_A(t₀) = B + t₀ ≤ 2t₀`
instead forces the harmless case `t₀ = 2`, `A = 2`, `B = 2 = t₀`. The core
`psi_of_core` only uses `G ≡ A (mod F)`, `C ∣ G − 1` and `1 < G`, so both forms of (P5)
are covered (`G_facts_D`, `G_facts_F`).  (P1) is stated as the congruence `I ≡ D (mod F)`
(the article's `F ∣ I − D` over the integers); (Q3) is an equation over `ℤ`.
-/

namespace Jones1982

open Pell Diophantine JSWW1976 Jones1978

/-- `ψ_A(n) ≤ 2n` forces `n ≤ 2` (`A ≥ 2`). -/
theorem le_two_of_ψ_le {A n : ℕ} (hA : 1 < A) (h : ψ hA n ≤ 2 * n) : n ≤ 2 := by
  by_contra hn
  push Not at hn
  have h1 : (2 * A - 1) ^ (n - 1) ≤ ψ hA n := pow_le_ψ hA (by omega)
  have h2 : 3 ^ (n - 1) ≤ (2 * A - 1) ^ (n - 1) := Nat.pow_le_pow_left (by omega) _
  have h3 : ∀ m, 3 ≤ m → 2 * m < 3 ^ (m - 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have e : 3 ^ (m + 1 - 1) = 3 * 3 ^ (m - 1) := by
        rw [Nat.add_sub_cancel, ← pow_succ']; congr 1; omega
      omega
  have := h3 n (by omega)
  omega

/-- `χ_G(n) > χ_A(n)` for `n ≥ 1` when `G ≥ 2A + 1`. -/
theorem xn_lt_xn_of_base {A G n : ℕ} (hA : 1 < A) (hG : 1 < G) (hAG : 2 * A + 1 ≤ G)
    (hn : 1 ≤ n) : xn hA n < xn hG n := by
  calc xn hA n ≤ (2 * A) ^ n := xn_le_pow hA n
    _ < G ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
    _ ≤ xn hG n := xn_ge_a_pow hG n

/-- The core of the sufficiency: `(D, C)` and `(F, E)` Pell pairs for `A` with `C² ∣ E`,
`E > 0`, `(I, H)` a Pell pair for `G` with `G ≡ A (mod F)`, `C ∣ G − 1`, `I ≡ D (mod F)`,
`H ≡ B (mod C)`, and `1 < B ≤ C` with `2B ≤ C` or `B` odd, give `C = ψ_A(B)`. -/
theorem psi_of_core {A B C D E F G H I t₀ t' t'' : ℕ} (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C)
    (hpar : 2 * B ≤ C ∨ Odd B)
    (hD : D = xn hA t₀) (hC : C = yn hA t₀) (hF : F = xn hA t') (hE : E = yn hA t')
    (hEpos : 0 < E) (hCE : C * C ∣ E)
    (hG1 : 1 < G) (hGA : A ≡ G [MOD F]) (hGC : C ∣ G - 1)
    (hI : I = xn hG1 t'') (hH : H = yn hG1 t'') (hID : I ≡ D [MOD F]) (hHB : H ≡ B [MOD C]) :
    C = ψ hA B := by
  have hC2 : 2 ≤ C := by omega
  have ht₀ : 2 ≤ t₀ := by
    by_contra hlt
    push Not at hlt
    have : C ≤ 1 := by
      rw [hC]
      calc yn hA t₀ ≤ yn hA 1 := (strictMono_y hA).monotone (by omega)
        _ = 1 := yn_one hA
    omega
  have ht'pos : 0 < t' := by
    by_contra h0
    push Not at h0
    have : t' = 0 := by omega
    rw [this, yn_zero] at hE
    omega
  have hCt' : C ∣ t' := by
    rw [hE, hC] at hCE
    have := dvd_of_ysq_dvd hA hCE
    rwa [← hC] at this
  have hCt'le : C ≤ t' := Nat.le_of_dvd ht'pos hCt'
  have ht₀C : t₀ ≤ C := by rw [hC]; exact yn_ge_n hA t₀
  -- `χ_A(t'') ≡ χ_A(t₀) (mod χ_A(t'))`
  have hxG : xn hA t'' ≡ xn hG1 t'' [MOD F] := (xy_modEq_of_modEq hA hG1 hGA t'').1
  have hID' : xn hG1 t'' ≡ D [MOD F] := by rw [← hI]; exact hID
  have hstep : xn hA t'' ≡ xn hA t₀ [MOD xn hA t'] := by
    rw [← hF, ← hD]; exact hxG.trans hID'
  have hcases := modEq_of_xn_modEq hA (by omega) (by omega) hstep
  -- `t'' ≡ B (mod C)`
  have ht''B : t'' ≡ B [MOD C] := by
    have h1 : yn hG1 t'' ≡ t'' [MOD G - 1] := yn_modEq_a_sub_one hG1 t''
    have h2 : yn hG1 t'' ≡ t'' [MOD C] := Nat.ModEq.of_dvd hGC h1
    rw [← hH] at h2
    exact h2.symm.trans hHB
  have hC4 : C ∣ 4 * t' := (dvd_mul_left _ _).trans (mul_dvd_mul_left 4 hCt')
  have hBt₀ : B ≡ t₀ [MOD C] ∨ B + t₀ ≡ 0 [MOD C] := by
    rcases hcases with h1 | h1
    · left; exact ht''B.symm.trans (Nat.ModEq.of_dvd hC4 h1)
    · right
      have h2 : t'' + t₀ ≡ 0 [MOD C] := Nat.ModEq.of_dvd hC4 h1
      exact (Nat.ModEq.add_right t₀ ht''B).symm.trans h2
  have hψC : C < yn hA C := lt_yn_of_two_le hA hC2
  have ht₀C' : t₀ ≠ C := by
    intro h; rw [h] at hC; omega
  rcases hBt₀ with h1 | h1
  · -- `B = t₀`
    have hBC' : B ≠ C := by
      intro h
      rw [h] at h1
      have : C ∣ t₀ := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
      have := Nat.le_of_dvd (by omega) this
      omega
    have : B = t₀ := Nat.ModEq.eq_of_lt_of_lt h1 (by omega) (by omega)
    rw [this, hC]
  · -- `C ∣ B + t₀`: `B + t₀ = C` (the case `2C` gives `t₀ = C`)
    have hdvd : C ∣ B + t₀ := (Nat.modEq_zero_iff_dvd).1 h1
    obtain ⟨q, hq⟩ := hdvd
    have hq1 : q = 1 := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q <;> omega
      · exfalso
        have := Nat.mul_le_mul_left C hq2
        omega
    rw [hq1, mul_one] at hq
    -- `t₀ = C − B`
    rcases hpar with h2B | hodd
    · -- `B ≤ t₀` and `ψ_A(t₀) = B + t₀ ≤ 2t₀`
      have hBt : B ≤ t₀ := by omega
      have hle : ψ hA t₀ ≤ 2 * t₀ := by show yn hA t₀ ≤ 2 * t₀; rw [← hC]; omega
      have ht₀2 : t₀ ≤ 2 := le_two_of_ψ_le hA hle
      have ht₀2' : t₀ = 2 := by omega
      have hψ2 : yn hA 2 = 2 * A := ψ_two hA
      rw [ht₀2', hψ2] at hC
      -- `B = 2A − 2 ≤ 2` gives `A = 2`, `B = 2`
      have hB2 : B = 2 := by omega
      rw [hB2, hC]; exact hψ2.symm
    · -- parity: `C = ψ_A(t₀) ≡ t₀ (mod 2)` but `C = B + t₀` with `B` odd
      exfalso
      have h2 : yn hA t₀ ≡ t₀ [MOD 2] := yn_modEq_two hA t₀
      rw [← hC] at h2
      have h3 := Nat.odd_iff.1 hodd
      unfold Nat.ModEq at h2
      omega

/-- (P5) in the form `G = A + F²(D² − A)`: `1 < G`, `G ≡ A (mod F)` and `C ∣ G − 1`
(from `D² = (A²−1)C² + 1`, `F² = (A²−1)E² + 1`, `E = iC²`). -/
theorem G_facts_D {A C D E F G i : ℕ} (hA : 1 < A) (hC : 1 ≤ C)
    (P2 : D ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1) (P3 : E = i * C ^ 2)
    (P4 : F ^ 2 = (A ^ 2 - 1) * E ^ 2 + 1) (P5 : G = A + F ^ 2 * (D ^ 2 - A)) :
    1 < G ∧ A ≡ G [MOD F] ∧ C ∣ G - 1 := by
  have hA2 : A + 1 ≤ A ^ 2 := by nlinarith
  have hDA : A ≤ D ^ 2 := by
    rw [P2]
    have : A ^ 2 - 1 ≤ (A ^ 2 - 1) * C ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  refine ⟨by omega, ?_, ?_⟩
  · refine (Nat.modEq_iff_dvd' (by omega)).2 ?_
    rw [P5, Nat.add_sub_cancel_left, pow_two, mul_assoc]
    exact dvd_mul_right _ _
  · -- in `ℤ`: `G − 1 = C² (F²(A²−1) − (A−1)(A²−1)i²C²)`
    have hG1 : 1 ≤ G := by omega
    rw [← Int.natCast_dvd_natCast]
    push_cast [Nat.cast_sub hG1]
    have e5 : (G : ℤ) = A + F ^ 2 * (D ^ 2 - A) := by rw [P5]; push_cast [Nat.cast_sub hDA]; ring
    have e2 : (D : ℤ) ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1 := by
      rw [← Nat.cast_pow, P2]; push_cast [Nat.cast_sub (by omega : 1 ≤ A ^ 2)]; ring
    have e4 : (F : ℤ) ^ 2 = (A ^ 2 - 1) * E ^ 2 + 1 := by
      rw [← Nat.cast_pow, P4]; push_cast [Nat.cast_sub (by omega : 1 ≤ A ^ 2)]; ring
    have e3 : (E : ℤ) = i * C ^ 2 := by rw [P3]; push_cast; ring
    refine ⟨C * ((F : ℤ) ^ 2 * (A ^ 2 - 1) - (A - 1) * (A ^ 2 - 1) * i ^ 2 * C ^ 2), ?_⟩
    rw [e5, e2]
    linear_combination (-((A : ℤ) - 1)) * e4 + (-((A : ℤ) - 1) * (A ^ 2 - 1) * (E + i * C ^ 2)) * e3

/-- (P5) in the form `G = A + F²(F² − A)`: the same facts. -/
theorem G_facts_F {A C E F G i : ℕ} (hA : 1 < A) (hi : 1 ≤ i) (hC : 1 ≤ C) (P3 : E = i * C ^ 2)
    (P4 : F ^ 2 = (A ^ 2 - 1) * E ^ 2 + 1) (P5 : G = A + F ^ 2 * (F ^ 2 - A)) :
    1 < G ∧ A ≡ G [MOD F] ∧ C ∣ G - 1 := by
  have hA2 : A + 1 ≤ A ^ 2 := by nlinarith
  have hE : 1 ≤ E := by rw [P3]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hFA : A + 1 ≤ F ^ 2 := by
    rw [P4]
    have : A ^ 2 - 1 ≤ (A ^ 2 - 1) * E ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hCE : C ∣ E := ⟨i * C, by rw [P3]; ring⟩
  have hCF : C ∣ F ^ 2 - 1 := by
    rw [P4, Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right (dvd_pow hCE two_ne_zero) _
  refine ⟨by rw [P5]; exact helper_G_gt hA hFA, ?_, ?_⟩
  · refine (Nat.modEq_iff_dvd' (by omega)).2 ⟨F * (F ^ 2 - A), ?_⟩
    rw [P5, Nat.add_sub_cancel_left, pow_two]; ring
  · rw [P5, helper_G_sub_one hFA]
    exact hCF.mul_right _

/-! ### Lemma 2.28 -/

/-- The conditions (P1)–(P7) of Lemma 2.28, with `E, G, H, I` explicit. -/
structure PConds (A B C D E F G H I i j : ℕ) : Prop where
  P1 : I ≡ D [MOD F]
  P2 : D ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1
  P3 : E = i * C ^ 2
  P4 : F ^ 2 = (A ^ 2 - 1) * E ^ 2 + 1
  P5 : G = A + F ^ 2 * (D ^ 2 - A) ∨ G = A + F ^ 2 * (F ^ 2 - A)
  P6 : H = B + j * C
  P7 : I ^ 2 = (G ^ 2 - 1) * H ^ 2 + 1

/-- Lemma 2.28, sufficiency. -/
theorem psi_of_PConds {A B C D E F G H I i j : ℕ} (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C)
    (hpar : 2 * B ≤ C ∨ Odd B) (hi : 0 < i) (h : PConds A B C D E F G H I i j) :
    C = ψ hA B := by
  obtain ⟨P1, P2, P3, P4, P5, P6, P7⟩ := h
  have hC1 : 1 ≤ C := by omega
  obtain ⟨t₀, hD, hC⟩ := eq_pell_of_sq hA P2
  obtain ⟨t', hF, hE⟩ := eq_pell_of_sq hA P4
  have hEpos : 0 < E := by rw [P3]; positivity
  have hCE : C * C ∣ E := ⟨i, by rw [P3]; ring⟩
  obtain ⟨hG1, hGA, hGC⟩ : 1 < G ∧ A ≡ G [MOD F] ∧ C ∣ G - 1 := by
    rcases P5 with P5 | P5
    · exact G_facts_D hA hC1 P2 P3 P4 P5
    · exact G_facts_F hA hi hC1 P3 P4 P5
  obtain ⟨t'', hI, hH⟩ := eq_pell_of_sq hG1 P7
  have hHB : H ≡ B [MOD C] := by
    rw [P6]
    show (B + j * C) % C = B % C
    rw [mul_comm, Nat.add_mul_mod_self_left]
  exact psi_of_core hA hB hBC hpar hD hC hF hE hEpos hCE hG1 hGA hGC hI hH P1 hHB

/-- Lemma 2.28, necessity, for both forms of (P5): the witnesses are positive, `H > B` and
`I > D`. -/
theorem exists_PConds {A B : ℕ} (hA : 1 < A) (hB : 1 < B) (useD : Bool) :
    ∃ D E F G H I i j : ℕ, 0 < D ∧ 0 < F ∧ 0 < i ∧ 0 < j ∧ D < I ∧ B < H ∧
      (if useD then G = A + F ^ 2 * (D ^ 2 - A) else G = A + F ^ 2 * (F ^ 2 - A)) ∧
      PConds A B (ψ hA B) D E F G H I i j := by
  obtain ⟨C, hC⟩ : ∃ C, C = ψ hA B := ⟨_, rfl⟩
  rw [← hC]
  have hC1 : 1 ≤ C := by rw [hC]; exact le_trans hB.le (yn_ge_n hA B)
  have hA2 : 1 ≤ A ^ 2 - 1 := by
    have : 4 ≤ A ^ 2 := by nlinarith
    omega
  -- `D = χ_A(B)`
  obtain ⟨D, hD⟩ : ∃ D, D = xn hA B := ⟨_, rfl⟩
  have P2 : D ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1 := by
    have h := χ_sq hA B
    rw [hD, hC, sq, h, sq]; ring
  -- `E = ψ_A(t')` a positive multiple of `C²`
  obtain ⟨t', ht'pos, i, hi⟩ := exists_dvd_yn hA (by positivity : 0 < C ^ 2)
  obtain ⟨F, hF⟩ : ∃ F, F = xn hA t' := ⟨_, rfl⟩
  have hi0 : 0 < i := by
    by_contra h0
    push Not at h0
    have : i = 0 := by omega
    rw [this, mul_zero] at hi
    have := ψ_pos_of_pos hA ht'pos
    simp [ψ] at this; omega
  have P3 : yn hA t' = i * C ^ 2 := by rw [hi]; ring
  have P4 : F ^ 2 = (A ^ 2 - 1) * (yn hA t') ^ 2 + 1 := by
    have h := χ_sq hA t'
    rw [hF, sq, h, sq]; ring
  -- `G`
  obtain ⟨G, hG⟩ : ∃ G, G = if useD then A + F ^ 2 * (D ^ 2 - A) else A + F ^ 2 * (F ^ 2 - A) :=
    ⟨_, rfl⟩
  have hGform : if useD then G = A + F ^ 2 * (D ^ 2 - A) else G = A + F ^ 2 * (F ^ 2 - A) := by
    cases useD <;> simp at hG ⊢ <;> exact hG
  have P5 : G = A + F ^ 2 * (D ^ 2 - A) ∨ G = A + F ^ 2 * (F ^ 2 - A) := by
    cases useD <;> simp at hGform
    · right; exact hGform
    · left; exact hGform
  obtain ⟨hG1, hGA, hGC⟩ : 1 < G ∧ A ≡ G [MOD F] ∧ C ∣ G - 1 := by
    rcases P5 with P5 | P5
    · exact G_facts_D hA hC1 P2 P3 P4 P5
    · exact G_facts_F hA hi0 hC1 P3 P4 P5
  -- `G ≥ 2A + 1`: `F² ≥ A + 1` and `D² − A ≥ 1`, `F² − A ≥ 1`
  have hFA : A + 1 ≤ F ^ 2 := by
    rw [P4]
    have h1 : 1 ≤ yn hA t' := ψ_pos_of_pos hA ht'pos
    have : A ^ 2 - 1 ≤ (A ^ 2 - 1) * (yn hA t') ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have : A + 1 ≤ A ^ 2 := by nlinarith
    omega
  have hDA : A + 1 ≤ D ^ 2 := by
    rw [P2]
    have : A ^ 2 - 1 ≤ (A ^ 2 - 1) * C ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have : A + 1 ≤ A ^ 2 := by nlinarith
    omega
  have hG2A : 2 * A + 1 ≤ G := by
    rcases P5 with P5 | P5
    · rw [P5]
      have : A + 1 ≤ F ^ 2 * (D ^ 2 - A) := by
        calc A + 1 ≤ F ^ 2 := hFA
          _ = F ^ 2 * 1 := (mul_one _).symm
          _ ≤ F ^ 2 * (D ^ 2 - A) := Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [P5]
      have : A + 1 ≤ F ^ 2 * (F ^ 2 - A) := by
        calc A + 1 ≤ F ^ 2 := hFA
          _ = F ^ 2 * 1 := (mul_one _).symm
          _ ≤ F ^ 2 * (F ^ 2 - A) := Nat.mul_le_mul_left _ (by omega)
      omega
  -- `H = ψ_G(B)`, `I = χ_G(B)`
  obtain ⟨H, hH⟩ : ∃ H, H = yn hG1 B := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = xn hG1 B := ⟨_, rfl⟩
  have hID : I ≡ D [MOD F] := by
    rw [hI, hD]; exact ((xy_modEq_of_modEq hA hG1 hGA B).1).symm
  have hDI : D < I := by rw [hD, hI]; exact xn_lt_xn_of_base hA hG1 hG2A (by omega)
  have hHB : H ≡ B [MOD C] := by
    rw [hH]; exact Nat.ModEq.of_dvd hGC (yn_modEq_a_sub_one hG1 B)
  have hBH : B < H := by rw [hH]; exact lt_yn_of_two_le hG1 hB
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hBH.le).1 hHB.symm
  have hj0 : 0 < j := by
    by_contra h0
    push Not at h0
    have : j = 0 := by omega
    rw [this, mul_zero] at hj
    omega
  refine ⟨D, yn hA t', F, G, H, I, i, j, ?_, ?_, hi0, hj0, hDI, hBH, hGform,
    ⟨hID, P2, P3, P4, P5, by rw [mul_comm]; omega, ?_⟩⟩
  · rw [hD]; exact lt_of_lt_of_le (by positivity : 0 < A ^ B) (xn_ge_a_pow hA B)
  · rw [hF]; exact lt_of_lt_of_le (by positivity : 0 < A ^ t') (xn_ge_a_pow hA t')
  · have h := χ_sq hG1 B
    rw [hI, hH, sq, h, sq]; ring

/-- Lemma 2.28. -/
theorem lemma_2_28 {A B C : ℕ} (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C) (hpar : 2 * B ≤ C ∨ Odd B) :
    C = ψ hA B ↔ ∃ D E F G H I i j : ℕ, 0 < D ∧ 0 < F ∧ 0 < i ∧ 0 < j ∧
      PConds A B C D E F G H I i j := by
  constructor
  · rintro rfl
    obtain ⟨D, E, F, G, H, I, i, j, hD, hF, hi, hj, -, -, -, h⟩ := exists_PConds hA hB true
    exact ⟨D, E, F, G, H, I, i, j, hD, hF, hi, hj, h⟩
  · rintro ⟨D, E, F, G, H, I, i, j, -, -, hi, -, h⟩
    exact psi_of_PConds hA hB hBC hpar hi h

/-! ### Corollary 2.29 -/

/-- The conditions (Q1)–(Q3) of Corollary 2.29 ((Q3) over `ℤ`). -/
structure QConds29 (A B C D F i j o : ℕ) : Prop where
  Q1 : D ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1
  Q2 : F ^ 2 = (A ^ 2 - 1) * i ^ 2 * C ^ 4 + 1
  Q3 : ((D : ℤ) + o * F) ^ 2 =
    (((A : ℤ) + F ^ 2 * (D ^ 2 - A)) ^ 2 - 1) * ((B : ℤ) + j * C) ^ 2 + 1

/-- Corollary 2.29. -/
theorem corollary_2_29 {A B C : ℕ} (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C)
    (hpar : 2 * B ≤ C ∨ Odd B) :
    C = ψ hA B ↔ ∃ D F i j o : ℕ, 0 < D ∧ 0 < F ∧ 0 < i ∧ 0 < j ∧ 0 < o ∧
      QConds29 A B C D F i j o := by
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  constructor
  · rintro rfl
    obtain ⟨D, E, F, G, H, I, i, j, hD, hF, hi, hj, hDI, hBH, hG, ⟨P1, P2, P3, P4, -, P6, P7⟩⟩ :=
      exists_PConds hA hB true
    simp only [if_true] at hG
    obtain ⟨o, ho⟩ := (Nat.modEq_iff_dvd' hDI.le).1 P1.symm
    have hDA : A ≤ D ^ 2 := by
      rw [P2]
      have : A ^ 2 - 1 ≤ (A ^ 2 - 1) * (ψ hA B) ^ 2 :=
        Nat.le_mul_of_pos_right _ (pow_pos (ψ_pos_of_pos hA (by omega)) 2)
      have : A + 1 ≤ A ^ 2 := by nlinarith
      omega
    refine ⟨D, F, i, j, o, hD, hF, hi, hj, ?_, ⟨P2, by rw [P4, P3]; ring, ?_⟩⟩
    · by_contra h0
      push Not at h0
      have : o = 0 := by omega
      rw [this, mul_zero] at ho
      omega
    · have hI : (I : ℤ) = D + o * F := by
        have : I = D + F * o := by omega
        rw [this]; push_cast; ring
      have hG' : (G : ℤ) = A + F ^ 2 * (D ^ 2 - A) := by
        rw [hG]; push_cast [Nat.cast_sub hDA]; ring
      have hG1 : 1 ≤ G ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h7 : ((I : ℤ)) ^ 2 = ((G : ℤ) ^ 2 - 1) * H ^ 2 + 1 := by
        rw [← Nat.cast_pow, P7]; push_cast [Nat.cast_sub hG1]; ring
      rw [← hI, ← hG', h7, P6]; push_cast; ring
  · rintro ⟨D, F, i, j, o, hD, hF, hi, hj, ho, ⟨Q1, Q2, Q3⟩⟩
    have hC1 : 1 ≤ C := by omega
    have hDA : A ≤ D ^ 2 := by
      rw [Q1]
      have : A ^ 2 - 1 ≤ (A ^ 2 - 1) * C ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
      have : A + 1 ≤ A ^ 2 := by nlinarith
      omega
    -- `G` as a natural number
    obtain ⟨G, hG⟩ : ∃ G, G = A + F ^ 2 * (D ^ 2 - A) := ⟨_, rfl⟩
    have hG1 : 1 < G := by omega
    have hGZ : (G : ℤ) = (A : ℤ) + F ^ 2 * (D ^ 2 - A) := by
      rw [hG]; push_cast [Nat.cast_sub hDA]; ring
    have P7 : (D + o * F) ^ 2 = (G ^ 2 - 1) * (B + j * C) ^ 2 + 1 := by
      have hG1' : 1 ≤ G ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hG1']
      rw [hGZ]
      exact Q3
    have hP4 : F ^ 2 = (A ^ 2 - 1) * (i * C ^ 2) ^ 2 + 1 := by rw [Q2]; ring
    exact psi_of_PConds hA hB hBC hpar hi
      ⟨by show (D + o * F) % F = D % F; rw [mul_comm, Nat.add_mul_mod_self_left], Q1, rfl, hP4,
        Or.inl hG, rfl, P7⟩

end Jones1982
