import DiophantineConsistency.ModelProductPell

/-! # The saturated positive ProductPell certificate in every model of `𝗜𝚺₁`

Package 101's nine-variable finalizer (`inherited/SATURATED_POSITIVE_PELL_AUDIT.md`)
replaces Jones's `F = (A² − 1)(iJDC²)² + 1` of Lemma 2.27 by

  `F = (A² − 1)·D·(iJC²)² + 1`,   `H = C + F(B + (j − 1)C)`,

with `D = (A² − 1)C² + 1`, `G = A + F(CD + 1 − A)`, `I = (G² − 1)H² + 1`, and asks
for `DFI` to be a square. Here, for the base `A = b + 2`:

* `psi_of_sat` (soundness): `C = ψ_A(B)`. It is
  `ModelProductPell.psi_of_ProductPellConds` with two changes: `F ≡ 1 (mod DC)`
  and `H ≡ C (mod F)` are read off the new polynomials directly, and once
  `D = s²` the Pell ordinate is `E = s·iJC²`, still a multiple of `C²`;
* `exists_sat` (completeness): for `C = ψ_A(B)` and every positive `J`, positive
  `i, j` exist. The witnesses are `i = χ_A(B)·i_old` from the internal pigeonhole
  lemma, so `F` and `G` are Jones's, and `H = ψ_G(B)`, which is `≡ C (mod F)`,
  `≡ B (mod C)` and at least `C + FB`.

The congruences are `%` in `V`; subtractions are moved across, so `SatConds`
uses only `+` and `*`; `H + FC = C + F(B + jC)` is `H = C + F(B + (j − 1)C)`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Nine121.SatPell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticGcdNormalization ModelProductPell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The saturated system, with negative terms moved across. -/
structure SatConds (A B C J i j D F G H I : V) : Prop where
  square : ∃ r : V, D * F * I = r * r
  A2 : D + C * C = A * A * C * C + 1
  A4 : F + D * (i * J * C * C) * (i * J * C * C) = A * A * D * (i * J * C * C) * (i * J * C * C) + 1
  A5 : G + F * A = A + F * (C * D + 1)
  A6 : H + F * C = C + F * (B + j * C)
  A7 : I + H * H = G * G * H * H + 1

set_option maxHeartbeats 2000000 in
/-- **Soundness** of the saturated system. -/
theorem psi_of_sat (b B C J i j D F G H I : V)
    (hB : 1 < B) (hBC : B ≤ C) (hpar : 2 * B ≤ C ∨ B % 2 = 1) (hJ : 0 < J) (hi : 0 < i)
    (hS : SatConds (b + 2) B C J i j D F G H I) : C = ycoord B b := by
  obtain ⟨⟨r, hsq⟩, hA2, hA4, hA5, hA6, hA7⟩ := hS
  -- sizes
  have hB2 : 2 ≤ B := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hB
  have hC2 : 2 ≤ C := le_trans hB2 hBC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : V) < 2) hC2
  have hD : D = 1 + delta b * C * C := pp_norm_of_literal b D C hA2
  obtain ⟨r0, hr0⟩ : ∃ r0 : V, r0 = i * J * C * C := ⟨_, rfl⟩
  rw [← hr0] at hA4
  have hF : F = 1 + delta b * D * r0 * r0 := by
    have h : F + D * r0 * r0 = (1 + delta b * D * r0 * r0) + D * r0 * r0 := by
      rw [hA4]; unfold delta; ring
    exact add_right_cancel h
  have hDpos : 0 < D := by
    rw [hD]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * C * C)
  have hFpos : 0 < F := by
    rw [hF]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * D * r0 * r0)
  have hr0pos : 0 < r0 := by rw [hr0]; exact mul_pos (mul_pos (mul_pos hi hJ) hCpos) hCpos
  have hDC1 : 1 < D * C :=
    lt_of_lt_of_le (by norm_num : (1 : V) < 2)
      (le_trans hC2 (le_mul_of_one_le_left (Arithmetic.zero_le C) (pos_iff_one_le.mp hDpos)))
  have hDCpos : 0 < D * C := lt_trans (by norm_num : (0 : V) < 1) hDC1
  have hAle : b + 2 ≤ C * D + 1 :=
    le_trans (pp_base_le_CD b C D hCpos hD) (by simp : C * D ≤ C * D + 1)
  -- `F ≡ 1 (mod DC)`
  obtain ⟨q, hFq⟩ : ∃ q : V, F = 1 + D * C * q := by
    refine ⟨delta b * r0 * (i * J * C), ?_⟩
    rw [hF, hr0]; ring
  have hFD : F = 1 + D * (C * q) := by rw [hFq]; ring
  -- `G ≡ 1 (mod DC)`
  have hGlin : G + D * C * (q * (b + 2)) = 1 + D * C * (F + q) := by
    have h : G + D * C * (q * (b + 2)) + (b + 2) = 1 + D * C * (F + q) + (b + 2) := by
      calc G + D * C * (q * (b + 2)) + (b + 2) = G + (1 + D * C * q) * (b + 2) := by ring
        _ = G + F * (b + 2) := by rw [← hFq]
        _ = b + 2 + F * (C * D + 1) := hA5
        _ = b + 2 + F * (C * D) + (1 + D * C * q) := by rw [← hFq]; ring
        _ = 1 + D * C * (F + q) + (b + 2) := by ring
    exact add_right_cancel h
  have hGmod : G % (D * C) = 1 % (D * C) := by
    have h : (G + D * C * (q * (b + 2))) % (D * C) = (1 + D * C * (F + q)) % (D * C) := by
      rw [hGlin]
    rwa [mod_add_mul' G (q * (b + 2)) hDCpos, mod_add_mul' 1 (F + q) hDCpos] at h
  obtain ⟨m, hGm⟩ : ∃ m : V, G = 1 + D * C * m :=
    ⟨G / (D * C), pp_eq_one_add_of_mod G (D * C) hDC1 hGmod⟩
  -- `G ≥ 2`, so `G` is a Pell base `g + 2`
  have hG2 : 2 ≤ G := by
    by_contra hn
    have hGlt : G < 2 := not_le.mp hn
    have hFmul : F * (b + 2) ≤ F * (C * D + 1) :=
      mul_le_mul_of_nonneg_left hAle (Arithmetic.zero_le F)
    have hlt : G + F * (b + 2) < b + 2 + F * (C * D + 1) :=
      lt_of_lt_of_le (add_lt_add_of_lt_of_le hGlt (le_refl (F * (b + 2))))
        (_root_.add_le_add (by simp : (2 : V) ≤ b + 2) hFmul)
    rw [hA5] at hlt
    exact _root_.lt_irrefl _ hlt
  obtain ⟨g, hGg⟩ : ∃ g : V, G = g + 2 := ⟨G - 2, (tsub_add_cancel_of_le hG2).symm⟩
  have hI : I = 1 + delta g * H * H := pp_norm_of_literal g I H (by rw [← hGg]; exact hA7)
  -- `H ≡ C (mod F)`
  have hHC : H % F = C % F := by
    have h : (H + F * C) % F = (C + F * (B + j * C)) % F := by rw [hA6]
    rwa [mod_add_mul' H C hFpos, mod_add_mul' C (B + j * C) hFpos] at h
  -- `I ≡ 1 (mod D)`
  have hID0 : I = 1 + D * ((2 * C * m + D * C * C * m * m) * H * H) := by
    have h : I + H * H = (1 + D * ((2 * C * m + D * C * C * m * m) * H * H)) + H * H := by
      rw [hA7, hGm]; ring
    exact add_right_cancel h
  obtain ⟨kI, hID⟩ : ∃ k : V, I = 1 + D * k := ⟨_, hID0⟩
  -- `I ≡ D (mod F)`
  have hGF : G % F = (b + 2) % F := by
    have h : (G + F * (b + 2)) % F = (b + 2 + F * (C * D + 1)) % F := by rw [hA5]
    rwa [mod_add_mul' G (b + 2) hFpos, mod_add_mul' (b + 2) (C * D + 1) hFpos] at h
  have hHHF : (H * H) % F = (C * C) % F := pp_mod_mul hFpos hHC hHC
  have hGGF : (G * G * H * H) % F = ((b + 2) * (b + 2) * C * C) % F :=
    pp_mod_mul hFpos (pp_mod_mul hFpos (pp_mod_mul hFpos hGF hGF) hHC) hHC
  have hIF : I % F = D % F := by
    apply ArithmeticPellResidueClasses.mod_add_cancel I D (C * C) F hFpos
    calc (I + C * C) % F = (I + H * H) % F := pp_mod_add hFpos rfl hHHF.symm
      _ = (G * G * H * H + 1) % F := by rw [hA7]
      _ = ((b + 2) * (b + 2) * C * C + 1) % F := pp_mod_add hFpos hGGF rfl
      _ = (D + C * C) % F := by rw [hA2]
  -- pairwise unit certificates
  have bDF : Bez D F 1 := by rw [hFD]; exact pp_bez_one_add D (C * q)
  have bDFI : Bez D (F * I) 1 := by
    have h : F * I = 1 + D * (C * q + kI + D * (C * q) * kI) := by rw [hFD, hID]; ring
    rw [h]; exact pp_bez_one_add D _
  have bIF : Bez I F 1 := by
    have hI' : I = F * (I / F) + D % F := by
      calc I = F * (I / F) + I % F := (div_add_mod I F).symm
        _ = F * (I / F) + D % F := by rw [hIF]
    exact pp_bez_transfer bDF (div_add_mod D F).symm hI'
  have bFI : Bez F I 1 := pp_bez_symm bIF
  -- each factor is a square
  obtain ⟨s, hDs⟩ := pp_square_of_coprime D (F * I) r bDFI (by rw [← hsq]; ring)
  obtain ⟨r1, hr1⟩ := pp_square_of_coprime (F * I) D r (pp_bez_symm bDFI) (by rw [← hsq]; ring)
  obtain ⟨f, hFf⟩ := pp_square_of_coprime F I r1 bFI hr1
  obtain ⟨u, hIu⟩ := pp_square_of_coprime I F r1 bIF (by rw [← hr1]; ring)
  -- the saturated ordinate `E = s·iJC²`
  obtain ⟨E, hEdef⟩ : ∃ E : V, E = s * r0 := ⟨_, rfl⟩
  have hFE : F = 1 + delta b * E * E := by rw [hF, hDs, hEdef]; ring
  have hspos : 0 < s := by
    rcases (Arithmetic.zero_le s).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hDs; exact absurd hDs (ne_of_gt hDpos)
  have hEpos : 0 < E := by rw [hEdef]; exact mul_pos hspos hr0pos
  -- Pell indices
  obtain ⟨t₀, -, -, hyt₀⟩ :=
    ArithmeticPellClassification.solution_index b s C (by rw [← hDs]; exact hD)
  obtain ⟨t', -, hxt', hyt'⟩ :=
    ArithmeticPellClassification.solution_index b f E (by rw [← hFf]; exact hFE)
  obtain ⟨t'', -, -, hyt''⟩ :=
    ArithmeticPellClassification.solution_index g u H (by rw [← hIu]; exact hI)
  -- the index `t₀`
  have hy1 : ycoord 1 b = 1 := by simpa using y_succ (0 : V) b
  have ht₀pos : 0 < t₀ := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0, y_zero] at hyt₀
    rw [← hyt₀] at hC2
    exact absurd hC2 (by norm_num)
  have ht₀2 : 2 ≤ t₀ := by
    have hne1 : t₀ ≠ 1 := by
      intro h1
      rw [h1, hy1] at hyt₀
      rw [← hyt₀] at hC2
      exact absurd hC2 (by norm_num)
    have h1lt : 1 < t₀ := lt_of_le_of_ne (pos_iff_one_le.mp ht₀pos) (Ne.symm hne1)
    simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp h1lt
  have h2t₀ : 2 * t₀ ≤ C := by rw [← hyt₀]; exact pp_two_mul_le_y b t₀ ht₀2
  have ht₀C : t₀ < C := lt_of_lt_of_le (pp_lt_two_mul t₀ ht₀pos) h2t₀
  -- the index `t'`: `C ∣ t'`
  have ht'pos : 0 < t' := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0, y_zero] at hyt'
    rw [← hyt'] at hEpos
    exact _root_.lt_irrefl _ hEpos
  have hCE : C ∣ E := ⟨s * i * J * C, by rw [hEdef, hr0]; ring⟩
  have hCCE : C * C ∣ delta b * E := ⟨delta b * (s * i * J), by rw [hEdef, hr0]; ring⟩
  have ht₀t' : t₀ ∣ t' :=
    (ArithmeticPellStrongDivisibility.y_dvd_iff b t₀ t').mp (by rw [hyt₀, hyt']; exact hCE)
  have hCt' : C ∣ t' := by
    have h := ArithmeticPellIndexDivisibility.ordinate_divides_index b t₀ t' ht₀t'
      (by rw [hyt₀, hyt']; exact hCCE)
    rwa [hyt₀] at h
  have h2t₀t' : 2 * t₀ ≤ t' := le_trans h2t₀ (le_of_dvd ht'pos hCt')
  -- `ψ(t'') ≡ ψ(t₀) (mod χ(t'))`, then the doubled step-down lemma
  have hbase : (b + 2) % F = (g + 2) % F := by rw [← hGg]; exact hGF.symm
  have hxpos : 0 < xcoord t' b := lt_of_lt_of_le (by norm_num : (0 : V) < 1) (one_le_x t' b)
  have hxF : xcoord t' b ∣ F := ⟨xcoord t' b, by rw [hxt']; exact hFf⟩
  have hyF : ycoord t'' b % F = ycoord t₀ b % F := by
    calc ycoord t'' b % F = ycoord t'' g % F := (pp_base_transfer b g F hFpos hbase t'').2
      _ = H % F := by rw [hyt'']
      _ = C % F := hHC
      _ = ycoord t₀ b % F := by rw [hyt₀]
  have hyx : ycoord t'' b % xcoord t' b = ycoord t₀ b % xcoord t' b := by
    calc ycoord t'' b % xcoord t' b = (ycoord t'' b % F) % xcoord t' b :=
          (ArithmeticPellResidueClasses.mod_reduce _ _ _ hxpos hxF).symm
      _ = (ycoord t₀ b % F) % xcoord t' b := by rw [hyF]
      _ = ycoord t₀ b % xcoord t' b := ArithmeticPellResidueClasses.mod_reduce _ _ _ hxpos hxF
  have hstep := ArithmeticPellResidueClasses.doubled_step_down b t' t₀ t'' ht₀pos h2t₀t'
    (Or.inl (pp_double_x_mod b t'' t₀ (xcoord t' b) hxpos hyx))
  have hred : t'' % C = t₀ % C ∨ (t'' + t₀) % C = 0 := by
    rcases hstep with h | h
    · left
      calc t'' % C = (t'' % t') % C :=
            (ArithmeticPellResidueClasses.mod_reduce t'' C t' hCpos hCt').symm
        _ = (t₀ % t') % C := by rw [h]
        _ = t₀ % C := ArithmeticPellResidueClasses.mod_reduce t₀ C t' hCpos hCt'
    · right
      calc (t'' + t₀) % C = ((t'' + t₀) % t') % C :=
            (ArithmeticPellResidueClasses.mod_reduce _ C t' hCpos hCt').symm
        _ = 0 % C := by rw [h]
        _ = 0 := zero_mod C
  -- `t'' ≡ B (mod C)`, since `C ∣ G − 1` and `H ≡ B (mod C)`
  have hCg : C ∣ g + 1 := by
    refine ⟨D * m, ?_⟩
    have h : g + 1 + 1 = C * (D * m) + 1 := by
      calc g + 1 + 1 = g + 2 := by ring
        _ = G := hGg.symm
        _ = 1 + D * C * m := hGm
        _ = C * (D * m) + 1 := by ring
    exact add_right_cancel h
  have hHBC : H % C = B % C := by
    have e2 : C + F * (B + j * C) = B + C * (1 + j + D * q * (B + j * C)) := by rw [hFq]; ring
    have h : (H + F * C) % C = (B + C * (1 + j + D * q * (B + j * C))) % C := by
      rw [← e2, hA6]
    rwa [mod_add_mul H F hCpos, mod_add_mul' B _ hCpos] at h
  have hHB : t'' % C = B % C := by
    have h1 : ycoord t'' g % C = t'' % C :=
      (ArithmeticPellCongruences.residue_mod t'' g C hCg hCpos).2
    rw [hyt''] at h1
    rw [← h1, hHBC]
  -- the final index argument
  have ht₀mod : t₀ % C = t₀ := mod_eq_self_of_lt ht₀C
  rcases hred with h | h
  · have hBt : B % C = t₀ := by rw [← hHB, h, ht₀mod]
    rcases lt_or_eq_of_le hBC with hlt | heq
    · rw [mod_eq_self_of_lt hlt] at hBt
      rw [hBt]
      exact hyt₀.symm
    · exfalso
      rw [heq, mod_self] at hBt
      exact (pos_iff_ne_zero.mp ht₀pos) hBt.symm
  · have hBt0 : (B + t₀) % C = 0 := by
      have h' : (t'' + t₀) % C = (B + t₀) % C := pp_mod_add hCpos hHB rfl
      rw [← h']
      exact h
    have hsum : B + t₀ = C := by
      have hle : C ≤ B + t₀ := by
        by_contra hn
        have hlt : B + t₀ < C := not_le.mp hn
        rw [mod_eq_self_of_lt hlt] at hBt0
        have hpos : 0 < B + t₀ :=
          lt_of_lt_of_le (lt_trans (by norm_num : (0 : V) < 1) hB) (by simp : B ≤ B + t₀)
        rw [hBt0] at hpos
        exact _root_.lt_irrefl _ hpos
      obtain ⟨w, hw⟩ : ∃ w : V, B + t₀ = w + C := ⟨B + t₀ - C, (tsub_add_cancel_of_le hle).symm⟩
      have hwC : w < C := by
        have h' : w + C < C + C := by
          rw [← hw]; exact add_lt_add_of_le_of_lt hBC ht₀C
        exact lt_of_add_lt_add_right h'
      rw [hw, mod_add_remove_right hCpos, mod_eq_self_of_lt hwC] at hBt0
      rw [hw, hBt0, zero_add]
    rcases hpar with h2B | hodd
    · have h1 : B ≤ t₀ := by
        have h' : B + B ≤ B + t₀ := by rw [hsum, ← two_mul]; exact h2B
        exact le_of_add_le_add_left h'
      have h2 : t₀ ≤ B := by
        have h' : t₀ + t₀ ≤ B + t₀ := by rw [hsum, ← two_mul]; exact h2t₀
        exact le_of_add_le_add_right h'
      have hBt : B = t₀ := le_antisymm h1 h2
      rw [hBt]
      exact hyt₀.symm
    · exfalso
      obtain ⟨q2, hq2⟩ := (pp_parity b t₀).1
      have e : B + 2 * t₀ = 2 * q2 := by
        rw [← hq2, hyt₀, ← hsum]; ring
      have h1 : (B + 2 * t₀) % 2 = B % 2 := mod_add_mul' B t₀ (by norm_num : (0 : V) < 2)
      rw [e, mod_mul_self_right, hodd] at h1
      exact absurd h1 (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **Completeness** of the saturated system. -/
theorem exists_sat (b B J : V) (hB : 1 < B) (hJ : 0 < J) :
    ∃ i j D F G H I : V, 0 < i ∧ 0 < j ∧ SatConds (b + 2) B (ycoord B b) J i j D F G H I := by
  have hB2 : 2 ≤ B := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hB
  have hBpos : 0 < B := lt_trans (by norm_num : (0 : V) < 1) hB
  obtain ⟨C, hC⟩ : ∃ C : V, C = ycoord B b := ⟨_, rfl⟩
  rw [← hC]
  have h2BC : 2 * B ≤ C := by rw [hC]; exact pp_two_mul_le_y b B hB2
  have hBC : B < C := lt_of_lt_of_le (pp_lt_two_mul B hBpos) h2BC
  have hCpos : 0 < C := lt_trans hBpos hBC
  -- `D = χ_A(B)²`
  obtain ⟨D, hD⟩ : ∃ D : V, D = 1 + delta b * C * C := ⟨_, rfl⟩
  have hDs : D = xcoord B b * xcoord B b := by
    rw [ArithmeticPellRecurrence.norm, ← hC]; exact hD
  have hDpos : 0 < D := by
    rw [hD]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * C * C)
  -- `E = ψ_A(t')`, a positive multiple of `J D C²`
  have hN : 0 < J * D * C * C := mul_pos (mul_pos (mul_pos hJ hDpos) hCpos) hCpos
  obtain ⟨t', ht'pos, i0, hi0⟩ := ArithmeticPellPigeonhole.ordinate_dvd b (J * D * C * C) hN
  obtain ⟨E, hE⟩ : ∃ E : V, E = ycoord t' b := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact lt_of_lt_of_le ht'pos (time_le_y t' b)
  have hA3 : E = i0 * J * D * C * C := by rw [hE, hi0]; ring
  have hi0pos : 0 < i0 := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0] at hA3
    rw [hA3] at hEpos
    simp only [zero_mul] at hEpos
    exact _root_.lt_irrefl _ hEpos
  -- the saturated witness `i = χ_A(B)·i0`
  obtain ⟨i, hidef⟩ : ∃ i : V, i = xcoord B b * i0 := ⟨_, rfl⟩
  have hxB : 0 < xcoord B b := lt_of_lt_of_le (by norm_num : (0 : V) < 1) (one_le_x B b)
  have hipos : 0 < i := by rw [hidef]; exact mul_pos hxB hi0pos
  have hEi : D * (i * J * C * C) * (i * J * C * C) = E * E := by
    rw [hA3, hidef, hDs]; ring
  -- `F = χ_A(t')²`
  obtain ⟨F, hF⟩ : ∃ F : V, F = 1 + delta b * E * E := ⟨_, rfl⟩
  have hFs : F = xcoord t' b * xcoord t' b := by
    rw [ArithmeticPellRecurrence.norm, ← hE]; exact hF
  have hFpos : 0 < F := by
    rw [hF]
    exact lt_of_lt_of_le (by norm_num : (0 : V) < 1) (by simp : (1 : V) ≤ 1 + delta b * E * E)
  obtain ⟨k, hFk⟩ : ∃ k : V, F = 1 + C * k := by
    refine ⟨delta b * E * (i0 * J * D * C), ?_⟩
    calc F = 1 + delta b * E * E := hF
      _ = 1 + delta b * E * (i0 * J * D * C * C) := by rw [← hA3]
      _ = 1 + C * (delta b * E * (i0 * J * D * C)) := by ring
  -- `G = A + F (CD + 1 − A) = g + 2`
  have hle : b + 2 ≤ C * D + 1 :=
    le_trans (pp_base_le_CD b C D hCpos hD) (by simp : C * D ≤ C * D + 1)
  obtain ⟨w, hw⟩ : ∃ w : V, w + (b + 2) = C * D + 1 :=
    ⟨C * D + 1 - (b + 2), tsub_add_cancel_of_le hle⟩
  obtain ⟨g, hg⟩ : ∃ g : V, g = b + F * w := ⟨_, rfl⟩
  have hA5 : g + 2 + F * (b + 2) = b + 2 + F * (C * D + 1) := by
    rw [hg, ← hw]; ring
  have hCg : C ∣ g + 1 := by
    refine ⟨D + k * w, ?_⟩
    have h : g + 1 + 1 = C * (D + k * w) + 1 := by
      calc g + 1 + 1 = (w + (b + 2)) + C * k * w := by rw [hg, hFk]; ring
        _ = (C * D + 1) + C * k * w := by rw [hw]
        _ = C * (D + k * w) + 1 := by ring
    exact add_right_cancel h
  -- `w ≥ C`, so `G ≥ FC`
  have hwC : C ≤ w := by
    have hDb : b + 2 ≤ D := le_trans (pp_base_le_delta b) (by
      rw [hD]; exact le_trans (pp_le_mul_sq (delta b) C hCpos) le_add_self)
    have h1 : C + (b + 2) ≤ C * D + 1 := by
      calc C + (b + 2) ≤ C + D := add_le_add (le_refl C) hDb
        _ ≤ C * D + 1 := by
          have hC1 : 1 ≤ C := pos_iff_one_le.mp hCpos
          have hD1 : 1 ≤ D := pos_iff_one_le.mp hDpos
          obtain ⟨c', rfl⟩ : ∃ c', C = c' + 1 := ⟨C - 1, (tsub_add_cancel_of_le hC1).symm⟩
          obtain ⟨d', rfl⟩ : ∃ d', D = d' + 1 := ⟨D - 1, (tsub_add_cancel_of_le hD1).symm⟩
          calc c' + 1 + (d' + 1) = (c' + 1 + d') + 1 := by ring
            _ ≤ (c' + 1 + d' + c' * d') + 1 := by simp
            _ = (c' + 1) * (d' + 1) + 1 := by ring
    rw [← hw] at h1
    exact le_of_add_le_add_right h1
  -- `H = ψ_G(B)`
  obtain ⟨H, hH⟩ : ∃ H : V, H = ycoord B g := ⟨_, rfl⟩
  have hbase : (g + 2) % F = (b + 2) % F := by
    rw [hg, show b + F * w + 2 = b + 2 + F * w by ring]
    exact mod_add_mul' (b + 2) w hFpos
  have hHF : H % F = C % F := by
    rw [hH, hC]
    exact (pp_base_transfer g b F hFpos hbase B).2
  have hHmod : H % C = B := by
    rw [hH, (ArithmeticPellCongruences.residue_mod B g C hCg hCpos).2]
    exact mod_eq_self_of_lt hBC
  -- `H ≥ 2G ≥ C`
  have hCH : C ≤ H := by
    have h2 : ycoord 2 g ≤ ycoord B g := (ArithmeticPellCongruences.y_strictMono g).monotone hB2
    rw [ArithmeticPellHalfIndex.y_two, ← hH] at h2
    have hF1 : 1 ≤ F := pos_iff_one_le.mp hFpos
    have hCg : C ≤ g + 2 := by
      calc C ≤ w := hwC
        _ ≤ F * w := le_mul_of_one_le_left (Arithmetic.zero_le _) hF1
        _ ≤ F * w + (b + 2) := le_self_add
        _ = g + 2 := by rw [hg]; ring
    calc C ≤ g + 2 := hCg
      _ ≤ 2 * (g + 2) := le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)
      _ ≤ H := h2
  -- `H = C + FQ`
  obtain ⟨Q, hQ⟩ : ∃ Q : V, H = C + F * Q := by
    have h0 : (H - C) % F = 0 := by
      have e := tsub_add_cancel_of_le hCH
      have h' : (H - C + C) % F = (0 + C) % F := by rw [e, zero_add]; exact hHF
      exact (ArithmeticPellResidueClasses.mod_add_cancel _ _ C F hFpos h').trans (zero_mod F)
    obtain ⟨Q, hQ⟩ := mod_eq_zero_iff_dvd.mp h0
    exact ⟨Q, by rw [← hQ]; exact (add_tsub_cancel_of_le hCH).symm⟩
  have hQmod : Q % C = B := by
    have h1 : H % C = (C + F * Q) % C := by rw [← hQ]
    have h2 : (C + F * Q) % C = Q % C := by
      rw [hFk, show C + (1 + C * k) * Q = Q + C * (1 + k * Q) by ring, mod_add_mul' Q _ hCpos]
    rw [← h2, ← h1, hHmod]
  obtain ⟨j', hj'⟩ : ∃ j' : V, Q = B + j' * C := by
    refine ⟨Q / C, ?_⟩
    have h := div_add_mod Q C
    rw [hQmod] at h
    calc Q = C * (Q / C) + B := h.symm
      _ = B + Q / C * C := by ring
  -- `I = χ_G(B)²`
  obtain ⟨I, hI⟩ : ∃ I : V, I = 1 + delta g * H * H := ⟨_, rfl⟩
  have hIs : I = xcoord B g * xcoord B g := by
    rw [ArithmeticPellRecurrence.norm, ← hH]; exact hI
  refine ⟨i, j' + 1, D, F, g + 2, H, I, hipos, lt_of_lt_of_le (by simp) le_add_self, ⟨?_, ?_, ?_, hA5, ?_, ?_⟩⟩
  · exact ⟨xcoord B b * xcoord t' b * xcoord B g, by rw [hDs, hFs, hIs]; ring⟩
  · rw [hD]; unfold delta; ring
  · rw [show (b + 2) * (b + 2) * D * (i * J * C * C) * (i * J * C * C) =
        (b + 2) * (b + 2) * (D * (i * J * C * C) * (i * J * C * C)) by ring, hEi, hF]
    unfold delta; ring
  · rw [hQ, hj']; ring
  · rw [hI]; unfold delta; ring

end Nine121.SatPell

#print axioms Nine121.SatPell.psi_of_sat
#print axioms Nine121.SatPell.exists_sat