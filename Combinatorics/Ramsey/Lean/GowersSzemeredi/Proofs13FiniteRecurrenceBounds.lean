import GowersSzemeredi.Proofs13PhaseSelection
import GowersSzemeredi.Proofs13SingletonRecurrence
import GowersSzemeredi.Proofs05QuadraticFamilyScale

/-! Quadratic recurrence in the printed large case, with improved length
and density. Finite localization avoids an asymptotic Weyl threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem stage135AmbientQuadratic_polynomial {N : Nat} [NeZero N] (a b : ZMod N) :
    PolynomialOn 2 Finset.univ (stage135AmbientQuadratic a b) := by
  have heq : stage135AmbientQuadratic a b = stage135Quadratic (modInterval N 0 N) a b := by
    funext t
    simp [stage135AmbientQuadratic, stage135Quadratic, modInterval]
  rw [heq]
  exact stage135Quadratic_polynomial (modInterval N 0 N) a b

theorem modAP_step_ne_zero_of_proper_length {N : Nat} [NeZero N]
    (Q : ModAP N) (hQ : Q.IsProper) (hlen : 2 ≤ Q.length) : Q.step != 0 := by
  apply bne_iff_ne.mpr
  intro hz
  have hc : Q.carrier.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro x y hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    simp [hz]
  rw [hQ] at hc
  omega

theorem lemma_13_5_prime_large_case {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hlargeCase : 2 < (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      Nat.floor ((D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤ E.Q.length ∧
      S.alpha ^ 32 * E.Q.length / 16 ≤ (criticalHeights S D E).card := by
  classical
  have hsmall := not_le.mpr hlargeCase
  have hq : 1 ≤ D.q := h134.1
  have hP : D.P.IsProper := h134.2.2.1
  have hPpos : 0 < D.P.length := by
    by_contra hz
    have hzero : D.P.length = 0 := by omega
    simp only [hzero, Nat.cast_zero, Real.zero_rpow (by positivity :
      (1 : Real) / 2 ^ (12 * D.q) ≠ 0)] at hsmall
    norm_num at hsmall
  have hPr : (1 : Real) ≤ D.P.length := by exact_mod_cast hPpos
  have h12 : (2 : Real) ^ (12 * D.q) = (4096 : Real) ^ D.q := by rw [pow_mul]; norm_num
  have h11 : (2 : Real) ^ (11 * D.q) = (2048 : Real) ^ D.q := by rw [pow_mul]; norm_num
  have hlarge : 2 < (D.P.length : Real) ^ ((4096 : Real) ^ D.q)⁻¹ := by
    simpa only [h12, one_div] using lt_of_not_ge hsmall
  let U := Nat.floor ((D.P.length : Real) ^ ((2048 : Real) ^ D.q)⁻¹)
  obtain ⟨hUfour, hbudgetR, hlength, hscale⟩ := quadratic_family_floor_scale hPr hq hlarge
  change 4 ≤ U at hUfour
  change (quadraticFamilyBudget D.q U : Real) ≤ D.P.length at hbudgetR
  have hbudget : quadraticFamilyBudget D.q U ≤ D.P.length := Nat.cast_le.mp hbudgetR
  have hPN : D.P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using Finset.card_le_univ D.P.carrier
  have hUL : U ≤ D.P.length := (quadraticFamilyBudget_ge D.q U).trans hbudget
  have hodd : N != 2 := by apply bne_iff_ne.mpr; omega
  obtain ⟨M, Q, hpart, hQ⟩ := quadratic_family_phase_localization D.P
    (fun i => stage135AmbientQuadratic (D.a i) (D.b i)) U hP
    (fun i => stage135AmbientQuadratic_polynomial (D.a i) (D.b i)) (by omega) hbudget
  have hM : 0 < M := by
    have hcard : 0 < D.P.carrier.card := by rw [hP]; exact hPpos
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
    obtain ⟨i, _⟩ := (hpart.1 x).mp hx
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨j, hj⟩ := stage135_select_weighted_cell S D Q hM hP h134.2.2.2.1
    hpart (fun j => (hQ j).1) h134.2.2.2.2.2.2.2.1
  have hselected := stage135_of_phase_cell hprime hodd S D (Q j) (hQ j).1
    (modAP_step_ne_zero_of_proper_length _ (hQ j).1 (by have := (hQ j).2.1; omega))
    (hpart.cell_subset j) (by have := (hQ j).2.1; omega) U (by omega) (by
      rw [h12, one_div]
      exact hlength.trans (Nat.cast_le.mpr (hQ j).2.1))
      (by simpa only [h11, one_div] using hscale) hj (by
        intro i
        obtain ⟨z, _, hz⟩ := (hQ j).2.2 i
        exact ⟨z, hz⟩)
  refine ⟨⟨Q j⟩, hselected.1, ?_, hselected.2⟩
  simpa only [h11, one_div] using (hQ j).2.1

/-- In the printed large case, improve the length exponent from 12q to 11q
and the critical-height density denominator from 20 to 16 simultaneously. -/
theorem lemma_13_5_prime_large_improved {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hlarge : 2 < (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q)) / 2 ≤ E.Q.length ∧
      S.alpha ^ 32 * E.Q.length / 16 ≤ (criticalHeights S D E).card := by
  obtain ⟨E, hE, hfloor, hcount⟩ := lemma_13_5_prime_large_case hprime S D theta h134 hlarge
  have hL : 1 ≤ D.P.length := by
    by_contra hz
    have hzero : D.P.length = 0 := by omega
    simp only [hzero, Nat.cast_zero, Real.zero_rpow (by positivity :
      (1 : Real) / 2 ^ (12 * D.q) ≠ 0)] at hlarge
    norm_num at hlarge
  let W := (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q))
  have hw : 2 < W := hlarge.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hL) (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) (by omega))))
  have hf : 2 ≤ Nat.floor W := (Nat.le_floor_iff (by positivity)).mpr hw.le
  have hfr : (2 : Real) ≤ Nat.floor W := by exact_mod_cast hf
  have hround := Nat.lt_floor_add_one W
  have hlen : (Nat.floor W : Real) ≤ E.Q.length := Nat.cast_le.mpr hfloor
  refine ⟨E, hE, ?_, hcount⟩
  change W / 2 ≤ (E.Q.length : Real)
  linarith only [hround, hfr, hlen]

end LeanProofs.GowersSzemeredi
