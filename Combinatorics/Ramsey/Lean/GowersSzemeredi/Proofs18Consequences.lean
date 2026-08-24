import GowersSzemeredi.Sections17_18

/-!
# Elementary consequences of the quantitative Szemeredi theorem

This module isolates the finite-coloring argument at the end of the paper.
It proves Corollary 18.7 from Theorem 18.2 without importing any unproved
statement as an axiom.  Once the quantitative theorem has a proof, the
wrapper below immediately supplies the exact numbered corollary.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

private theorem exists_two_color_class_half (N : Nat)
    (color : Nat → Fin 2) :
    ∃ c : Fin 2,
      (N : Real) / 2 ≤
        (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) := by
  classical
  let S := Finset.Icc 1 N
  let A0 := S.filter fun x => color x = (0 : Fin 2)
  let A1 := S.filter fun x => color x = (1 : Fin 2)
  have hnot : S.filter (fun x => ¬ color x = (0 : Fin 2)) = A1 := by
    ext x
    simp only [Finset.mem_filter, A1]
    constructor
    · rintro ⟨hx, hne⟩
      refine ⟨hx, ?_⟩
      apply Fin.ext
      have hlt := (color x).isLt
      have hneval : (color x).val ≠ 0 := by
        intro hv
        apply hne
        apply Fin.ext
        simpa using hv
      omega
    · rintro ⟨hx, hone⟩
      refine ⟨hx, ?_⟩
      simp [hone]
  have hsumNat : A0.card + A1.card = S.card := by
    simpa [A0, hnot] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (fun x => color x = (0 : Fin 2)))
  have hScard : S.card = N := by simp [S]
  have hsum : (A0.card : Real) + A1.card = N := by
    exact_mod_cast hsumNat.trans hScard
  by_cases h0 : (N : Real) / 2 ≤ A0.card
  · exact ⟨0, by simpa [A0, S] using h0⟩
  · refine ⟨1, ?_⟩
    have h0lt : (A0.card : Real) < (N : Real) / 2 := lt_of_not_ge h0
    have h1 : (N : Real) / 2 ≤ A1.card := by linarith
    simpa [A1, S] using h1

private theorem szemeredi_half_threshold_le_two_color (k : Nat) :
    szemerediThreshold (1 / 2 : Real) k ≤ twoColorThreshold k := by
  simp only [szemerediThreshold, twoColorThreshold]
  norm_num

/-- The quantitative Szemeredi theorem implies the paper's two-color
corollary with the displayed five-level tower. -/
theorem corollary_18_7_holds_of_theorem_18_2
    (h18 : theorem_18_2) : corollary_18_7 := by
  intro k N hk hN color
  obtain ⟨c, hc⟩ := exists_two_color_class_half N color
  let A := (Finset.Icc 1 N).filter fun x => color x = c
  have hthreshold : szemerediThreshold (1 / 2 : Real) k ≤ N :=
    (szemeredi_half_threshold_le_two_color k).trans hN
  have hAsub : A ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hAcard : (1 / 2 : Real) * N ≤ A.card := by
    simpa [A, div_eq_mul_inv, mul_comm] using hc
  obtain ⟨a, d, hd, hmem⟩ :=
    h18 (1 / 2 : Real) k N (by norm_num) (by norm_num) hk
      hthreshold A hAsub hAcard
  refine ⟨a, d, c, hd, ?_⟩
  intro i hi
  have hai := hmem i hi
  have haiA : a + i * d ∈ A := hai
  have hfilter := Finset.mem_filter.mp haiA
  exact ⟨hfilter.1, hfilter.2⟩

/-- The quantitative theorem also implies the qualitative headline version.
For densities above one half we simply apply it at density one half. -/
theorem theorem_1_2_holds_of_theorem_18_2
    (h18 : theorem_18_2) : theorem_1_2 := by
  intro k delta hk hdelta
  let delta0 : Real := min delta (1 / 2)
  have hdelta0 : 0 < delta0 := by
    exact lt_min hdelta (by norm_num)
  have hdelta0le : delta0 ≤ 1 / 2 := min_le_right _ _
  obtain ⟨N, hN⟩ :=
    exists_nat_ge (max 1 (szemerediThreshold delta0 k))
  have hNone : (1 : Real) ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hNone)
  have hthreshold : szemerediThreshold delta0 k ≤ N :=
    (le_max_right _ _).trans hN
  refine ⟨N, hNpos, ?_⟩
  intro A hAsub hAcard
  have hdelta0delta : delta0 ≤ delta := min_le_left _ _
  have hdelta0card : delta0 * N ≤ A.card := by
    calc
      delta0 * (N : Real) ≤ delta * N := by
        gcongr
      _ ≤ A.card := hAcard
  exact h18 delta0 k N hdelta0 hdelta0le hk hthreshold A hAsub hdelta0card

end LeanProofs.GowersSzemeredi
