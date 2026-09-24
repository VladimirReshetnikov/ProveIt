import Diophantine.Paper1982.Psi

/-!
# Jones 1982, Lemma 2.27: one product-square condition for a Pell coordinate

For `1 < A`, `1 < B ≤ C`, and either `2B ≤ C` or `B` odd, the relation
`C = ψ_A(B)` is equivalent to (A1)--(A7), with positive witnesses `i, j` and
an arbitrary fixed positive integer `J`. The square condition is `D F I = □`.

The polynomial equations below move negative terms to the opposite side, so
they retain the article's integer meaning without truncated subtraction.
The condition `F ∣ H-C` is the genuine congruence `H ≡ C (mod F)`.

The proof separates the three square factors using their pairwise coprimality,
then applies the ψ form of the Pell step-down lemma. Working modulo `C`
introduces an extra index possibility, excluded by the stated size/parity
hypothesis just as in Lemma 2.28.
-/

namespace Jones1982

open Pell Diophantine JSWW1976 Jones1978

/-- The literal polynomial system (A1)--(A7), with all defined quantities explicit. -/
structure ProductPellConds (A B C J i j D E F G H I : ℕ) : Prop where
  square : IsSquare (D * F * I)
  congr : H ≡ C [MOD F]
  A2 : D + C ^ 2 = A ^ 2 * C ^ 2 + 1
  A3 : E = i * J * D * C ^ 2
  A4 : F + E ^ 2 = A ^ 2 * E ^ 2 + 1
  A5 : G + F * A = A + F * (C * D + 1)
  A6 : H = B + j * C
  A7 : I + H ^ 2 = G ^ 2 * H ^ 2 + 1

/-- The divisibility condition in (A1) is over the integers. -/
theorem productPell_congr_iff (F H C : ℕ) :
    H ≡ C [MOD F] ↔ (F : ℤ) ∣ (H : ℤ) - C := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h
  · simpa only [neg_sub] using dvd_neg.mpr h
  · simpa only [neg_sub] using dvd_neg.mpr h

/-- The formula for `G` gives `G ≡ 1` modulo any divisor of `CD` for which `F ≡ 1`. -/
theorem productPell_G_mod {A C D F G k : ℕ}
    (hG : G + F * A = A + F * (C * D + 1))
    (hF : F ≡ 1 [MOD k]) (hCD : k ∣ C * D) : G ≡ 1 [MOD k] := by
  have h0 : C * D ≡ 0 [MOD k] := Nat.modEq_zero_iff_dvd.mpr hCD
  apply Nat.ModEq.add_right_cancel' A
  calc
    G + A = G + 1 * A := by ring
    _ ≡ G + F * A [MOD k] := (Nat.ModEq.add_left G (hF.mul_right A)).symm
    _ = A + F * (C * D + 1) := hG
    _ ≡ A + 1 * (0 + 1) [MOD k] := Nat.ModEq.add_left A (hF.mul (h0.add_right 1))
    _ = 1 + A := by ring

/-- The congruence of the two Pell bases follows from (A5). -/
theorem productPell_G_base {A C D F G : ℕ}
    (hG : G + F * A = A + F * (C * D + 1)) : A ≡ G [MOD F] := by
  show A % F = G % F
  have h := congrArg (fun n : ℕ => n % F) hG
  simpa [Nat.add_mod, Nat.mul_mod] using h.symm

/-- The final index argument, including the extra residue possibility modulo `C`. -/
theorem productPell_index {A B C t₀ : ℕ} (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C)
    (hpar : 2 * B ≤ C ∨ Odd B) (hC : C = yn hA t₀)
    (hmod : B ≡ t₀ [MOD C] ∨ B + t₀ ≡ 0 [MOD C]) : C = ψ hA B := by
  have hC2 : 2 ≤ C := by omega
  have ht₀ : 2 ≤ t₀ := by
    by_contra hn
    have : C ≤ 1 := by
      rw [hC]
      calc yn hA t₀ ≤ yn hA 1 := (strictMono_y hA).monotone (by omega)
        _ = 1 := yn_one hA
    omega
  have ht₀C : t₀ ≤ C := by rw [hC]; exact yn_ge_n hA t₀
  have hψC : C < yn hA C := lt_yn_of_two_le hA hC2
  have ht₀C' : t₀ ≠ C := by intro h; rw [h] at hC; omega
  rcases hmod with h1 | h1
  · have hBC' : B ≠ C := by
      intro h
      rw [h] at h1
      have : C ∣ t₀ := (Nat.modEq_zero_iff_dvd).1
        (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
      have := Nat.le_of_dvd (by omega : 0 < t₀) this
      omega
    have : B = t₀ := Nat.ModEq.eq_of_lt_of_lt h1 (by omega) (by omega)
    rw [this, hC]
  · have hdvd : C ∣ B + t₀ := (Nat.modEq_zero_iff_dvd).1 h1
    obtain ⟨q, hq⟩ := hdvd
    have hq1 : q = 1 := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q <;> omega
      · have := Nat.mul_le_mul_left C hq2
        omega
    rw [hq1, mul_one] at hq
    rcases hpar with h2B | hodd
    · have hle : ψ hA t₀ ≤ 2 * t₀ := by
        show yn hA t₀ ≤ 2 * t₀
        rw [← hC]
        omega
      have ht₀2 := le_two_of_ψ_le hA hle
      have ht₀eq : t₀ = 2 := by omega
      have hψ2 : yn hA 2 = 2 * A := ψ_two hA
      rw [ht₀eq, hψ2] at hC
      have hB2 : B = 2 := by omega
      rw [hB2, hC]
      exact hψ2.symm
    · exfalso
      have h2 : yn hA t₀ ≡ t₀ [MOD 2] := yn_modEq_two hA t₀
      rw [← hC] at h2
      have h3 := Nat.odd_iff.1 hodd
      unfold Nat.ModEq at h2
      omega

set_option maxHeartbeats 1000000 in
/-- Sufficiency of the product-square Pell system. -/
theorem psi_of_ProductPellConds {A B C J i j D E F G H I : ℕ}
    (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C) (hpar : 2 * B ≤ C ∨ Odd B)
    (hJ : 0 < J) (hi : 0 < i) (hS : ProductPellConds A B C J i j D E F G H I) :
    C = ψ hA B := by
  obtain ⟨hsq, hHC, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hS
  have hA1 : 1 ≤ A * A := by nlinarith
  have hC2 : 2 ≤ C := by omega
  have hD : D = (A * A - 1) * C ^ 2 + 1 := helper_D_eq hA1 hA2
  have hDA : A + 1 ≤ D := hD ▸ helper_F_ge hA hC2
  have hD0 : 0 < D := by omega
  have hE0 : 0 < E := by rw [hA3]; positivity
  have hF : F = (A * A - 1) * E ^ 2 + 1 := helper_D_eq hA1 hA4
  have hF1 : 1 ≤ F := by omega
  have hCDA : A ≤ C * D + 1 := by
    have : D ≤ C * D := Nat.le_mul_of_pos_left D (by omega)
    omega
  have hG : G = A + F * (C * D + 1 - A) := by
    zify [hCDA] at hA5 ⊢
    linear_combination hA5
  have hG1 : 1 < G := by rw [hG]; omega
  have hG1n : 1 ≤ G * G := by nlinarith
  have hI : I = (G * G - 1) * H ^ 2 + 1 := helper_D_eq hG1n hA7
  have hDE : D ∣ E := ⟨i * J * C ^ 2, by rw [hA3]; ring⟩
  have hCCE : C * C ∣ E := ⟨i * J * D, by rw [hA3]; ring⟩
  have hCE : C ∣ E := ⟨i * J * D * C, by rw [hA3]; ring⟩
  have hEF1 : E ∣ F - 1 := ⟨(A * A - 1) * E, by rw [hF, Nat.add_sub_cancel]; ring⟩
  have hFD : F ≡ 1 [MOD D] :=
    ((Nat.modEq_iff_dvd' hF1).2 (hDE.trans hEF1)).symm
  have hFC : F ≡ 1 [MOD C] :=
    ((Nat.modEq_iff_dvd' hF1).2 (hCE.trans hEF1)).symm
  have hGD := productPell_G_mod hA5 hFD (dvd_mul_left D C)
  have hGCmod := productPell_G_mod hA5 hFC (dvd_mul_right C D)
  have hGC : C ∣ G - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ G)).1 hGCmod.symm
  have hGA := productPell_G_base hA5
  have hcopDF : Nat.Coprime D F := by
    have := hFD.gcd_eq
    simp only [Nat.gcd_one_left] at this
    exact Nat.Coprime.symm this
  have hID : I ≡ 1 [MOD D] := by
    have h1 : G ^ 2 * H ^ 2 + 1 ≡ 1 * H ^ 2 + 1 [MOD D] :=
      Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ (hGD.pow 2))
    have h2 : I + H ^ 2 ≡ 1 + H ^ 2 [MOD D] := by
      rw [hA7]
      simpa only [one_mul, add_comm 1] using h1
    exact Nat.ModEq.add_right_cancel' _ h2
  have hcopDI : Nat.Coprime D I := by
    have := hID.gcd_eq
    simp only [Nat.gcd_one_left] at this
    exact Nat.Coprime.symm this
  have hIF : I ≡ D [MOD F] := by
    have h1 : G ^ 2 * H ^ 2 + 1 ≡ A ^ 2 * C ^ 2 + 1 [MOD F] :=
      Nat.ModEq.add_right _ (Nat.ModEq.mul (hGA.symm.pow 2) (hHC.pow 2))
    have h2 : I + H ^ 2 ≡ D + H ^ 2 [MOD F] := by
      rw [hA7]
      refine h1.trans ?_
      rw [← hA2]
      exact Nat.ModEq.add_left _ (hHC.pow 2).symm
    exact Nat.ModEq.add_right_cancel' _ h2
  have hcopFI : Nat.Coprime F I := by
    have := hIF.gcd_eq
    rw [Nat.Coprime.gcd_eq_one hcopDF] at this
    exact Nat.Coprime.symm this
  have hsq' : IsSquare (D * (F * I)) := by rwa [mul_assoc] at hsq
  have hsqD : IsSquare D := IsSquare.of_coprime_mul (hcopDF.mul_right hcopDI) hsq'
  have hsqFI : IsSquare (F * I) :=
    IsSquare.of_coprime_mul (hcopDF.mul_right hcopDI).symm (by rwa [mul_comm] at hsq')
  have hsqF : IsSquare F := IsSquare.of_coprime_mul hcopFI hsqFI
  have hsqI : IsSquare I := IsSquare.of_coprime_mul hcopFI.symm (by rwa [mul_comm] at hsqFI)
  obtain ⟨t₀, ht₀⟩ := exists_eq_ψ_of_square hA (hD ▸ hsqD)
  obtain ⟨t', ht'⟩ := exists_eq_ψ_of_square hA (hF ▸ hsqF)
  obtain ⟨t'', ht''⟩ := exists_eq_ψ_of_square hG1 (hI ▸ hsqI)
  have hy0 : yn hA t₀ = C := ht₀.symm
  have hy1 : yn hA t' = E := ht'.symm
  have hy2 : yn hG1 t'' = H := ht''.symm
  have ht₀pos : 1 ≤ t₀ := by
    rcases Nat.eq_zero_or_pos t₀ with h | h
    · rw [h] at ht₀; simp [ψ, yn_zero] at ht₀; omega
    · exact h
  have ht₀C : t₀ ≤ C := by rw [ht₀]; exact yn_ge_n hA t₀
  have ht'pos : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with h | h
    · rw [h] at ht'; simp [ψ, yn_zero] at ht'; omega
    · exact h
  have hCt' : C ∣ t' := by
    have : yn hA t₀ * yn hA t₀ ∣ yn hA t' := by rw [hy1, hy0]; exact hCCE
    rw [← hy0]; exact dvd_of_ysq_dvd hA this
  have ht'2 : 2 ≤ t' := le_trans hC2 (Nat.le_of_dvd ht'pos hCt')
  have ht₀t' : t₀ ≤ t' := ht₀C.trans (Nat.le_of_dvd ht'pos hCt')
  have hFχ : F = χ hA t' * χ hA t' := by
    rw [hF, ← hy1, χ_sq hA t', pow_two, mul_assoc]
  have h1 : yn hA t'' ≡ yn hG1 t'' [MOD F] := (xy_modEq_of_modEq hA hG1 hGA t'').2
  have h2 : yn hA t'' ≡ yn hA t₀ [MOD χ hA t'] := by
    have h3 : yn hA t'' ≡ yn hA t₀ [MOD F] := by
      refine h1.trans ?_
      rw [hy2, hy0]; exact hHC
    rw [hFχ] at h3
    exact Nat.ModEq.of_dvd (dvd_mul_right _ _) h3
  obtain ⟨q, hq⟩ := yn_modEq_cases hA ht'2 ht₀pos ht₀t' h2
  have hHt'' : H ≡ t'' [MOD C] := by
    rw [ht'']; exact Nat.ModEq.of_dvd hGC (yn_modEq_a_sub_one hG1 t'')
  have hHB : H ≡ B [MOD C] := by
    rw [hA6]
    show (B + j * C) % C = B % C
    simp
  have ht''B : t'' ≡ B [MOD C] := hHt''.symm.trans hHB
  have hCtq : C ∣ 2 * t' * q := by
    obtain ⟨u, hu⟩ := hCt'; exact ⟨2 * u * q, by rw [hu]; ring⟩
  apply productPell_index hA hB hBC hpar ht₀
  rcases hq with hq | hq
  · left
    have ht₀t'' : t₀ ≡ t'' [MOD C] := by
      rw [hq]
      exact (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
        (by rw [Nat.add_sub_cancel_left]; exact hCtq)
    exact ht''B.symm.trans ht₀t''.symm
  · right
    have ht''t₀ : t'' + t₀ ≡ 0 [MOD C] := by
      rw [hq]; exact Nat.modEq_zero_iff_dvd.mpr hCtq
    exact (ht''B.add_right t₀).symm.trans ht''t₀

set_option maxHeartbeats 1000000 in
/-- Necessity: both freely quantified witnesses are positive, for every positive `J`. -/
theorem exists_ProductPellConds {A B : ℕ} (hA : 1 < A) (hB : 1 < B) {J : ℕ} (hJ : 0 < J) :
    ∃ i j D E F G H I : ℕ, 0 < i ∧ 0 < j ∧
      ProductPellConds A B (ψ hA B) J i j D E F G H I := by
  let C := ψ hA B
  have hC2 : 2 ≤ C := le_trans hB (yn_ge_n hA B)
  have hA1 : 1 ≤ A * A := by nlinarith
  let D := (A * A - 1) * C ^ 2 + 1
  have hD : D = (A * A - 1) * C ^ 2 + 1 := rfl
  have hDsq : D = χ hA B * χ hA B := by rw [hD]; dsimp [C]; rw [χ_sq]; ring
  have hDA : A + 1 ≤ D := hD ▸ helper_F_ge hA hC2
  let m := J * D * C ^ 2
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨t', ht'pos, i, hi⟩ := exists_dvd_yn hA hm
  have hEpos : 0 < yn hA t' := ψ_pos_of_pos hA ht'pos
  have hi0 : 0 < i := by
    by_contra hn
    have : i = 0 := by omega
    rw [this, mul_zero] at hi; omega
  let E := yn hA t'
  have hE : E = i * J * D * C ^ 2 := by dsimp [E]; rw [hi]; dsimp [m]; ring
  let F := (A * A - 1) * E ^ 2 + 1
  have hF : F = (A * A - 1) * E ^ 2 + 1 := rfl
  have hFsq : F = χ hA t' * χ hA t' := by rw [hF]; dsimp [E]; rw [χ_sq]; ring
  have hF1 : 1 ≤ F := by rw [hF]; omega
  have hCDA : A ≤ C * D + 1 := by
    have : D ≤ C * D := Nat.le_mul_of_pos_left D (by omega)
    omega
  let G := A + F * (C * D + 1 - A)
  have hG : G + F * A = A + F * (C * D + 1) := by
    dsimp [G]
    zify [hCDA]
    ring
  have hG1 : 1 < G := by dsimp [G]; omega
  have hG1n : 1 ≤ G * G := by nlinarith
  have hCE : C ∣ E := ⟨i * J * D * C, by rw [hE]; ring⟩
  have hEF1 : E ∣ F - 1 := ⟨(A * A - 1) * E, by rw [hF, Nat.add_sub_cancel]; ring⟩
  have hFC : F ≡ 1 [MOD C] := ((Nat.modEq_iff_dvd' hF1).2 (hCE.trans hEF1)).symm
  have hGCmod := productPell_G_mod hG hFC (dvd_mul_right C D)
  have hGC : C ∣ G - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ G)).1 hGCmod.symm
  let H := yn hG1 B
  have hHgt : B < H := lt_yn_of_two_le hG1 hB
  have hHB : H ≡ B [MOD C] := Nat.ModEq.of_dvd hGC (yn_modEq_a_sub_one hG1 B)
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hHgt.le).1 hHB.symm
  have hj0 : 0 < j := by
    by_contra hn
    have : j = 0 := by omega
    rw [this, mul_zero] at hj; omega
  have hH : H = B + j * C := by
    have := Nat.mul_comm C j
    omega
  let I := (G * G - 1) * H ^ 2 + 1
  have hI : I = (G * G - 1) * H ^ 2 + 1 := rfl
  have hIsq : I = χ hG1 B * χ hG1 B := by rw [hI]; dsimp [H]; rw [χ_sq]; ring
  have hGA := productPell_G_base hG
  refine ⟨i, j, D, E, F, G, H, I, hi0, hj0, ?_⟩
  change ProductPellConds A B C J i j D E F G H I
  refine ⟨⟨χ hA B * χ hA t' * χ hG1 B, ?_⟩, ?_, ?_, hE, ?_, hG, hH, ?_⟩
  · rw [hDsq, hFsq, hIsq]; ring
  · exact (xy_modEq_of_modEq hA hG1 hGA B).2.symm
  · rw [hD]; exact helper_D_eq' hA1
  · rw [hF]; exact helper_D_eq' hA1
  · rw [hI]; exact helper_D_eq' hG1n

/-- **Lemma 2.27**, with arbitrary positive `J` and positive witnesses `i, j`. -/
theorem lemma_2_27 {A B C : ℕ} (hA : 1 < A) (hB : 1 < B) (hBC : B ≤ C)
    (hpar : 2 * B ≤ C ∨ Odd B) {J : ℕ} (hJ : 0 < J) :
    C = ψ hA B ↔ ∃ i j D E F G H I : ℕ, 0 < i ∧ 0 < j ∧
      ProductPellConds A B C J i j D E F G H I := by
  constructor
  · intro hC; rw [hC]; exact exists_ProductPellConds hA hB hJ
  · rintro ⟨i, j, D, E, F, G, H, I, hi, hj, h⟩
    exact psi_of_ProductPellConds hA hB hBC hpar hJ hi h

/-- The coprimality observation in the remark after Lemma 2.27. -/
theorem ProductPellConds.coprime_J {A B C J i j D E F G H I : ℕ} (hA : 1 < A)
    (h : ProductPellConds A B C J i j D E F G H I) : Nat.Coprime F J := by
  have hF : F = (A * A - 1) * E ^ 2 + 1 := helper_D_eq (by nlinarith) h.A4
  have hJE : J ∣ E := ⟨i * D * C ^ 2, by rw [h.A3]; ring⟩
  have hEF : E ∣ F - 1 := ⟨(A * A - 1) * E, by rw [hF, Nat.add_sub_cancel]; ring⟩
  have hFJ : F ≡ 1 [MOD J] :=
    ((Nat.modEq_iff_dvd' (by rw [hF]; omega : 1 ≤ F)).2 (hJE.trans hEF)).symm
  have hcop := hFJ.gcd_eq
  simpa only [Nat.gcd_one_left] using hcop

end Jones1982
