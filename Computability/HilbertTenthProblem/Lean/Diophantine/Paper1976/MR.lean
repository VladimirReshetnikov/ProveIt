import Diophantine.Common.Pell
import Diophantine.Common.PellMod
import Diophantine.Paper1976.Ineq3
import Mathlib.Tactic

/-!
# JSWW 1976, §3: Lemma 3.8 (Matijasevič–Robinson) and Pell helpers

> **Lemma 3.8** (Matijasevič–Robinson [11]). Suppose `A > 1`, `B > 1` and `C > 0`.
> For any fixed auxiliary parameter `κ ≥ 0`, `ψ_A(B) = C` iff the following system can be
> satisfied in nonnegative integers `i, j, D, E, F, G, H, I`:
> (A1) `D F I = □`, `F ∣ H − C`, `B ≤ C`; (A2) `D = (A²−1)C² + 1`;
> (A3) `E = 2(i+1)D(κ+1)C²`; (A4) `F = (A²−1)E² + 1`; (A5) `G = A + F(F−A)`;
> (A6) `H = B + 2(j+1)C`; (A7) `I = (G²−1)H² + 1`.

The article cites this lemma from Matijasevič–Robinson (1975) without proof; it is
proved here in full.  The equations are written without natural-number subtraction
(`D + C² = A²C² + 1` for (A2), `G + F A = A + F²` for (A5), …), which is their
integer meaning (`A ≥ 1`, and `F ≥ A` follows from the system).

Proof sketch.  (⇐) `D, F, I` are pairwise coprime (`F ≡ 1 (mod D)` since `D ∣ E`;
`G ≡ 1 (mod E)` gives `I ≡ 1 (mod D)`; `G ≡ A` and `H ≡ C (mod F)` give
`I ≡ D (mod F)`), so each is a square, giving `C = ψ_A(t₀)`, `E = ψ_A(t')`,
`H = ψ_G(t'')`.  From `C² ∣ E`, `C ∣ t'`.  Since `G ≡ A (mod F)`,
`ψ_A(t'') ≡ ψ_G(t'') = H ≡ C = ψ_A(t₀) (mod χ_A(t'))`, hence `t'' ≡ ±t₀ (mod 2t')`
(`yn_modEq_cases`), so modulo `2C`.  Since `G ≡ 1 (mod 2C)`, `H ≡ t'' (mod 2C)`, and
`H ≡ B (mod 2C)`; as `t₀, B ≤ C` this forces `t₀ = B` (the case `t₀ + B = 2C` would give
`C = ψ_A(C)` with `C ≥ 2`).  (⇒) take `D = χ_A(B)²`, `E = ψ_A(t')` a multiple of
`2(κ+1)DC²` (pigeonhole), `F = χ_A(t')²`, `G = A + F(F−A)`, `H = ψ_G(B)`, `I = χ_G(B)²`.
-/

namespace JSWW1976

open Pell Diophantine

/-- The Matijasevič–Robinson system (A1)–(A7) of Lemma 3.8, with parameter `κ`. -/
structure MRSystem (A B C κ i j D E F G H I : ℕ) : Prop where
  A1 : IsSquare (D * F * I) ∧ (F : ℤ) ∣ (H : ℤ) - C ∧ B ≤ C
  A2 : D + C ^ 2 = A ^ 2 * C ^ 2 + 1
  A3 : E = 2 * (i + 1) * D * (κ + 1) * C ^ 2
  A4 : F + E ^ 2 = A ^ 2 * E ^ 2 + 1
  A5 : G + F * A = A + F ^ 2
  A6 : H = B + 2 * (j + 1) * C
  A7 : I + H ^ 2 = G ^ 2 * H ^ 2 + 1

/-- A solution `y` of `(a²−1)y² + 1 = □` is a `ψ_a(t)` (Mathlib's `Pell.eq_pell`). -/
theorem exists_eq_ψ_of_square {a y : ℕ} (a1 : 1 < a) (h : IsSquare ((a * a - 1) * y ^ 2 + 1)) :
    ∃ t, y = ψ a1 t := by
  obtain ⟨z, hz⟩ := h
  have hp : z * z - (a * a - 1) * y * y = 1 := by
    have : z * z = (a * a - 1) * y * y + 1 := by rw [← hz]; ring
    omega
  obtain ⟨t, -, ht⟩ := Pell.eq_pell a1 hp
  exact ⟨t, ht⟩

/-- Lemma 2.2, as used in §3: if `ψ_a(t) ≡ c (mod a−1)` with `c < a − 1`, then
`t = c + p'·(a−1)` for some `p'`. -/
theorem index_eq_of_modEq {a t c : ℕ} (a1 : 1 < a) (hc : c < a - 1)
    (h : ψ a1 t ≡ c [MOD a - 1]) : ∃ p', t = c + p' * (a - 1) := by
  have h1 : t ≡ c [MOD a - 1] := (ψ_modEq a1 t).symm.trans h
  have hmod : t % (a - 1) = c := by
    have := h1
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hc]
  refine ⟨t / (a - 1), ?_⟩
  have := Nat.div_add_mod t (a - 1)
  rw [hmod] at this
  linarith [this]

/-- `ψ_a(t) ≥ (2a−1)^(t−1)` for `t ≥ 1` (Lemma 2.1, lower half, reindexed). -/
theorem pow_le_ψ {a t : ℕ} (a1 : 1 < a) (ht : 1 ≤ t) : (2 * a - 1) ^ (t - 1) ≤ ψ a1 t := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact pow_le_ψ_succ a1 t'

/-- `ψ_a(t) ≤ (2a)^(t−1)` for `t ≥ 1` (Lemma 2.1, upper half, reindexed). -/
theorem ψ_le_pow {a t : ℕ} (a1 : 1 < a) (ht : 1 ≤ t) : ψ a1 t ≤ (2 * a) ^ (t - 1) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact ψ_succ_le_pow a1 t'

/-- The square condition `(a²−1)ψ_a(t)² + 1 = χ_a(t)²`. -/
theorem square_of_ψ {a : ℕ} (a1 : 1 < a) (t : ℕ) :
    IsSquare ((a * a - 1) * ψ a1 t ^ 2 + 1) := by
  refine ⟨χ a1 t, ?_⟩
  have := χ_sq a1 t
  rw [this]; ring

theorem ψ_pos_of_pos {a t : ℕ} (a1 : 1 < a) (ht : 0 < t) : 0 < ψ a1 t := by
  have := strictMono_y a1 ht
  simpa [ψ, yn_zero] using this


/-! ### Small arithmetic helpers (kept outside the main proof to keep contexts small) -/

theorem helper_F_ge {A E : ℕ} (hA : 1 < A) (hE : 2 ≤ E) : A + 1 ≤ (A * A - 1) * E ^ 2 + 1 := by
  have hAA : A + 1 ≤ A * A := by nlinarith
  have h4 : 4 ≤ E ^ 2 := by nlinarith
  have : (A * A - 1) * 4 ≤ (A * A - 1) * E ^ 2 := Nat.mul_le_mul_left _ h4
  omega

theorem helper_G_gt {A F : ℕ} (hA : 1 < A) (hF : A + 1 ≤ F) : 1 < A + F * (F - A) := by
  have : 1 ≤ F - A := by omega
  have : F ≤ F * (F - A) := Nat.le_mul_of_pos_right _ this
  omega

theorem helper_G_sub_one {A F : ℕ} (hF : A + 1 ≤ F) :
    A + F * (F - A) - 1 = (F - 1) * (F - A + 1) := by
  have h1 : A ≤ F := by omega
  have h2 : 1 ≤ F := by omega
  have h3 : 1 ≤ A + F * (F - A) := by
    have : 1 ≤ F - A := by omega
    have : F ≤ F * (F - A) := Nat.le_mul_of_pos_right _ this
    omega
  zify [h1, h2, h3]
  ring

theorem helper_G_eq {A F G : ℕ} (hF : A + 1 ≤ F) (h : G + F * A = A + F ^ 2) :
    G = A + F * (F - A) := by
  zify [show A ≤ F by omega] at h ⊢
  linear_combination h

theorem helper_D_eq {A C D : ℕ} (hA : 1 ≤ A * A) (h : D + C ^ 2 = A ^ 2 * C ^ 2 + 1) :
    D = (A * A - 1) * C ^ 2 + 1 := by
  zify [hA] at h ⊢
  linear_combination h

theorem helper_D_eq' {A C : ℕ} (hA : 1 ≤ A * A) :
    (A * A - 1) * C ^ 2 + 1 + C ^ 2 = A ^ 2 * C ^ 2 + 1 := by
  zify [hA]; ring

theorem helper_G_eq' {A F : ℕ} (hF : A ≤ F) : A + F * (F - A) + F * A = A + F ^ 2 := by
  zify [hF]; ring

set_option maxHeartbeats 1000000 in
/-- **Lemma 3.8** (Matijasevič–Robinson 1975). -/
theorem lemma_3_8 {A B C : ℕ} (hA : 1 < A) (hB : 1 < B) (hC : 0 < C) (κ : ℕ) :
    ψ hA B = C ↔ ∃ i j D E F G H I, MRSystem A B C κ i j D E F G H I := by
  have hA1 : 1 ≤ A * A := by nlinarith
  constructor
  · -- (⇒)
    intro hCB
    -- D = χ_A(B)²
    obtain ⟨D, hD⟩ : ∃ D, D = (A * A - 1) * C ^ 2 + 1 := ⟨_, rfl⟩
    have hDsq : D = χ hA B * χ hA B := by
      rw [hD, ← hCB, χ_sq hA B]; ring
    have hD1 : 1 ≤ D := by omega
    -- m = 2(κ+1)DC², and E = ψ_A(t') a positive multiple of m
    obtain ⟨m, hm_def⟩ : ∃ m, m = 2 * (κ + 1) * D * C ^ 2 := ⟨_, rfl⟩
    have hm2 : 2 ≤ m := by
      have h0 : 0 < (κ + 1) * D * C ^ 2 := by positivity
      have h1 : 2 * 1 ≤ 2 * ((κ + 1) * D * C ^ 2) := Nat.mul_le_mul_left _ h0
      rw [hm_def]
      linarith [h1]
    obtain ⟨t', ht'pos, i1, hi1⟩ := exists_dvd_yn hA (by omega : 0 < m)
    have hEpos : 0 < yn hA t' := ψ_pos_of_pos hA ht'pos
    have hi1pos : 1 ≤ i1 := by
      rcases Nat.eq_zero_or_pos i1 with h | h
      · rw [h, mul_zero] at hi1; omega
      · exact h
    obtain ⟨E, hE⟩ : ∃ E, E = yn hA t' := ⟨_, rfl⟩
    have hE2 : 2 ≤ E := by
      have : m * 1 ≤ m * i1 := Nat.mul_le_mul_left _ hi1pos
      rw [hE, hi1]; omega
    obtain ⟨F, hF⟩ : ∃ F, F = (A * A - 1) * E ^ 2 + 1 := ⟨_, rfl⟩
    have hFsq : F = χ hA t' * χ hA t' := by rw [hF, hE, χ_sq hA t']; ring
    have hFA : A + 1 ≤ F := hF ▸ helper_F_ge hA hE2
    obtain ⟨G, hG⟩ : ∃ G, G = A + F * (F - A) := ⟨_, rfl⟩
    have hG1 : 1 < G := hG ▸ helper_G_gt hA hFA
    -- E ∣ G − 1
    have hEF1 : E ∣ F - 1 := ⟨(A * A - 1) * E, by rw [hF, Nat.add_sub_cancel]; ring⟩
    have hEG : E ∣ G - 1 := by rw [hG, helper_G_sub_one hFA]; exact hEF1.mul_right _
    have h2C : 2 * C ∣ E := ⟨(κ + 1) * D * C * i1, by rw [hE, hi1, hm_def]; ring⟩
    -- H = ψ_G(B)
    obtain ⟨H, hH⟩ : ∃ H, H = yn hG1 B := ⟨_, rfl⟩
    have hHB : H ≡ B [MOD 2 * C] := by
      rw [hH]
      exact Nat.ModEq.of_dvd (h2C.trans hEG) (yn_modEq_a_sub_one hG1 B)
    have hHgt : B < H := by rw [hH]; exact lt_yn_of_two_le hG1 hB
    obtain ⟨j1, hj1⟩ : ∃ j1, H = B + 2 * C * j1 := by
      obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hHgt.le).1 hHB.symm
      exact ⟨q, by omega⟩
    have hj1pos : 1 ≤ j1 := by
      rcases Nat.eq_zero_or_pos j1 with h | h
      · rw [h] at hj1; omega
      · exact h
    obtain ⟨I, hI⟩ : ∃ I, I = (G * G - 1) * H ^ 2 + 1 := ⟨_, rfl⟩
    have hIsq : I = χ hG1 B * χ hG1 B := by rw [hI, hH, χ_sq hG1 B]; ring
    have hGA : A ≡ G [MOD F] := by
      refine (Nat.modEq_iff_dvd' (by omega)).2 ⟨F - A, ?_⟩
      rw [hG, Nat.add_sub_cancel_left]
    have hG1n : 1 ≤ G * G := by nlinarith
    refine ⟨i1 - 1, j1 - 1, D, E, F, G, H, I, ?_⟩
    refine ⟨⟨⟨χ hA B * χ hA t' * χ hG1 B, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hDsq, hFsq, hIsq]; ring
    · -- F ∣ H − C: ψ_A(B) ≡ ψ_G(B) (mod F)
      have h := (Nat.modEq_iff_dvd).1 (xy_modEq_of_modEq hA hG1 hGA B).2
      rw [hH, ← hCB]
      exact h
    · rw [← hCB]; exact yn_ge_n hA B
    · rw [hD]; exact helper_D_eq' hA1
    · rw [hE, hi1, hm_def, Nat.sub_add_cancel hi1pos]; ring
    · rw [hF]; exact helper_D_eq' hA1
    · rw [hG]; exact helper_G_eq' (by omega)
    · rw [hj1, Nat.sub_add_cancel hj1pos]; ring
    · rw [hI]; exact helper_D_eq' hG1n
  · -- (⇐)
    rintro ⟨i, j, D, E, F, G, H, I, hS⟩
    obtain ⟨⟨hsq, hFHC, hBC⟩, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hS
    have hD : D = (A * A - 1) * C ^ 2 + 1 := helper_D_eq hA1 hA2
    have hD1 : 1 ≤ D := by omega
    have hE2 : 2 ≤ E := by
      have h0 : 0 < (i + 1) * D * (κ + 1) * C ^ 2 := by positivity
      have h1 : 2 * 1 ≤ 2 * ((i + 1) * D * (κ + 1) * C ^ 2) := Nat.mul_le_mul_left _ h0
      rw [hA3]
      linarith [h1]
    have hF : F = (A * A - 1) * E ^ 2 + 1 := helper_D_eq hA1 hA4
    have hFA : A + 1 ≤ F := hF ▸ helper_F_ge hA hE2
    have hG : G = A + F * (F - A) := helper_G_eq hFA hA5
    have hG1 : 1 < G := hG ▸ helper_G_gt hA hFA
    have hG1n : 1 ≤ G * G := by nlinarith
    have hI : I = (G * G - 1) * H ^ 2 + 1 := helper_D_eq hG1n hA7
    -- divisibilities and congruences
    have hDE : D ∣ E := ⟨2 * (i + 1) * (κ + 1) * C ^ 2, by rw [hA3]; ring⟩
    have hCCE : C * C ∣ E := ⟨2 * (i + 1) * D * (κ + 1), by rw [hA3]; ring⟩
    have h2C : 2 * C ∣ E := ⟨(i + 1) * D * (κ + 1) * C, by rw [hA3]; ring⟩
    have hEF1 : E ∣ F - 1 := ⟨(A * A - 1) * E, by rw [hF, Nat.add_sub_cancel]; ring⟩
    have hEG : E ∣ G - 1 := by rw [hG, helper_G_sub_one hFA]; exact hEF1.mul_right _
    have hFD : F ≡ 1 [MOD D] :=
      ((Nat.modEq_iff_dvd' (by omega : 1 ≤ F)).2 (hDE.trans hEF1)).symm
    have hcopDF : Nat.Coprime D F := by
      have := hFD.gcd_eq
      simp only [Nat.gcd_one_left] at this
      exact Nat.Coprime.symm this
    have hGD : G ≡ 1 [MOD D] :=
      ((Nat.modEq_iff_dvd' (by omega : 1 ≤ G)).2 (hDE.trans hEG)).symm
    have hID : I ≡ 1 [MOD D] := by
      have h1 : G ^ 2 * H ^ 2 + 1 ≡ 1 * H ^ 2 + 1 [MOD D] :=
        Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ (hGD.pow 2))
      have h2 : I + H ^ 2 ≡ 1 + H ^ 2 [MOD D] := by
        rw [hA7]
        have e : 1 * H ^ 2 + 1 = 1 + H ^ 2 := by ring
        rw [e] at h1
        exact h1
      exact Nat.ModEq.add_right_cancel' _ h2
    have hcopDI : Nat.Coprime D I := by
      have := hID.gcd_eq
      simp only [Nat.gcd_one_left] at this
      exact Nat.Coprime.symm this
    have hGA : A ≡ G [MOD F] := by
      refine (Nat.modEq_iff_dvd' (by omega)).2 ⟨F - A, ?_⟩
      rw [hG, Nat.add_sub_cancel_left]
    have hHC : H ≡ C [MOD F] := by
      refine (Nat.modEq_iff_dvd).2 ?_
      rw [show (C : ℤ) - H = -((H : ℤ) - C) by ring]
      exact (dvd_neg).2 hFHC
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
    -- the three squares
    have hsq' : IsSquare (D * (F * I)) := by rwa [mul_assoc] at hsq
    have hsqD : IsSquare D := IsSquare.of_coprime_mul (hcopDF.mul_right hcopDI) hsq'
    have hsqFI : IsSquare (F * I) :=
      IsSquare.of_coprime_mul (hcopDF.mul_right hcopDI).symm (by rwa [mul_comm] at hsq')
    have hsqF : IsSquare F := IsSquare.of_coprime_mul hcopFI hsqFI
    have hsqI : IsSquare I := IsSquare.of_coprime_mul hcopFI.symm (by rwa [mul_comm] at hsqFI)
    -- Pell indices
    obtain ⟨t0, ht0⟩ := exists_eq_ψ_of_square hA (hD ▸ hsqD)
    obtain ⟨t', ht'⟩ := exists_eq_ψ_of_square hA (hF ▸ hsqF)
    obtain ⟨t'', ht''⟩ := exists_eq_ψ_of_square hG1 (hI ▸ hsqI)
    have hy0 : yn hA t0 = C := ht0.symm
    have hy1 : yn hA t' = E := ht'.symm
    have hy2 : yn hG1 t'' = H := ht''.symm
    have hC2 : 2 ≤ C := by omega
    have ht0pos : 1 ≤ t0 := by
      rcases Nat.eq_zero_or_pos t0 with h | h
      · rw [h] at ht0; simp [ψ, yn_zero] at ht0; omega
      · exact h
    have ht0C : t0 ≤ C := by rw [ht0]; exact yn_ge_n hA t0
    have ht'pos : 0 < t' := by
      rcases Nat.eq_zero_or_pos t' with h | h
      · rw [h] at ht'; simp [ψ, yn_zero] at ht'; omega
      · exact h
    have hCt' : C ∣ t' := by
      have : yn hA t0 * yn hA t0 ∣ yn hA t' := by rw [hy1, hy0]; exact hCCE
      rw [← hy0]; exact dvd_of_ysq_dvd hA this
    have ht'2 : 2 ≤ t' := le_trans hC2 (Nat.le_of_dvd ht'pos hCt')
    have ht0t' : t0 ≤ t' := ht0C.trans (Nat.le_of_dvd ht'pos hCt')
    have hFχ : F = χ hA t' * χ hA t' := by rw [hF, ← hy1, χ_sq hA t', pow_two, mul_assoc]
    -- ψ_A(t'') ≡ ψ_A(t₀) (mod χ_A(t'))
    have h1 : yn hA t'' ≡ yn hG1 t'' [MOD F] := (xy_modEq_of_modEq hA hG1 hGA t'').2
    have h2 : yn hA t'' ≡ yn hA t0 [MOD χ hA t'] := by
      have h3 : yn hA t'' ≡ yn hA t0 [MOD F] := by
        have h4 : yn hG1 t'' ≡ yn hA t0 [MOD F] := by
          rw [hy2, hy0]; exact hHC
        exact h1.trans h4
      rw [hFχ] at h3
      exact Nat.ModEq.of_dvd (dvd_mul_right _ _) h3
    obtain ⟨q, hq⟩ := yn_modEq_cases hA ht'2 ht0pos ht0t' h2
    -- t'' ≡ B (mod 2C)
    have hHt'' : H ≡ t'' [MOD 2 * C] := by
      rw [ht'']
      exact Nat.ModEq.of_dvd (h2C.trans hEG) (yn_modEq_a_sub_one hG1 t'')
    have hHB : H ≡ B [MOD 2 * C] := by
      have hBH : B ≤ H := by rw [hA6]; omega
      exact ((Nat.modEq_iff_dvd' hBH).2
        ⟨j + 1, by rw [hA6, Nat.add_sub_cancel_left]; ring⟩).symm
    have ht''B : t'' ≡ B [MOD 2 * C] := hHt''.symm.trans hHB
    have h2Ct' : 2 * C ∣ 2 * t' * q := by
      obtain ⟨u, hu⟩ := hCt'; exact ⟨u * q, by rw [hu]; ring⟩
    rcases hq with hq | hq
    · -- t'' = t₀ + 2t'q
      have ht0B : t0 ≡ B [MOD 2 * C] := by
        have h5 : t0 ≡ t'' [MOD 2 * C] := by
          rw [hq]
          exact (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
            (by rw [Nat.add_sub_cancel_left]; exact h2Ct')
        exact h5.trans ht''B
      have hlt1 : t0 < 2 * C := by omega
      have hlt2 : B < 2 * C := by omega
      have heq := Nat.ModEq.eq_of_lt_of_lt ht0B hlt1 hlt2
      rw [← heq]
      exact hy0
    · -- t'' + t₀ = 2t'q, so 2C ∣ t₀ + B, forcing t₀ = B = C and C = ψ_A(C)
      exfalso
      have hsum : 2 * C ∣ t0 + B := by
        have e1 : t0 + t'' ≡ 0 [MOD 2 * C] := by
          rw [add_comm, hq]; exact (Nat.modEq_zero_iff_dvd).2 h2Ct'
        have e2 : t0 + B ≡ t0 + t'' [MOD 2 * C] := Nat.ModEq.add_left _ ht''B.symm
        exact (Nat.modEq_zero_iff_dvd).1 (e2.trans e1)
      have heq : t0 + B = 2 * C := by
        obtain ⟨u, hu⟩ := hsum
        have hu1 : u = 1 := by
          rcases Nat.lt_or_ge u 2 with hu2 | hu2
          · interval_cases u <;> omega
          · exfalso
            have : 2 * C * 2 ≤ 2 * C * u := Nat.mul_le_mul_left _ hu2
            omega
        rw [hu, hu1, mul_one]
      have ht0eq : t0 = C := by omega
      rw [ht0eq] at hy0
      have := lt_yn_of_two_le hA hC2
      rw [hy0] at this
      exact lt_irrefl _ this

end JSWW1976
