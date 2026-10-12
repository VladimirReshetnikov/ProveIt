import GowersSzemeredi.Proofs18ColorClass

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

private theorem exists_two_color_class_half (N : Nat) (color : Nat → Fin 2) :
    ∃ c : Fin 2,
      (N : Real) / 2 ≤
        (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) :=
  exists_color_class_ge (by decide) N color

private theorem szemeredi_half_threshold_le_two_color (k : Nat) :
    szemerediThreshold (1 / 2 : Real) k ≤ twoColorThreshold k := by
  simp only [szemerediThreshold, twoColorThreshold]
  norm_num

/-- Corollary 18.7 at a single length `k`, from Theorem 18.2 at that length
and density one half. The two thresholds coincide at density one half. -/
theorem corollary_18_7_at_of_half_density {k : Nat}
    (h : ∀ N : Nat, szemerediThreshold (1 / 2 : Real) k ≤ N →
      ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → (1 / 2 : Real) * N ≤ A.card →
        HasNatAP A k) :
    ∀ N : Nat, twoColorThreshold k ≤ N →
      ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k := by
  intro N hN color
  obtain ⟨c, hc⟩ := exists_two_color_class_half N color
  let A := (Finset.Icc 1 N).filter fun x => color x = c
  have hthreshold : szemerediThreshold (1 / 2 : Real) k ≤ N :=
    (szemeredi_half_threshold_le_two_color k).trans hN
  have hAsub : A ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hAcard : (1 / 2 : Real) * N ≤ A.card := by
    simpa [A, div_eq_mul_inv, mul_comm] using hc
  obtain ⟨a, d, hd, hmem⟩ := h N hthreshold A hAsub hAcard
  refine ⟨a, d, c, hd, ?_⟩
  intro i hi
  have hai := hmem i hi
  have haiA : a + i * d ∈ A := hai
  have hfilter := Finset.mem_filter.mp haiA
  exact ⟨hfilter.1, hfilter.2⟩

/-- The quantitative theorem gives the printed two-color bound by applying
its single-length consequence at density one half. -/
theorem corollary_18_7_holds_of_theorem_18_2
    (h18 : theorem_18_2) : corollary_18_7 := by
  intro k N hk hN color
  exact corollary_18_7_at_of_half_density
    (fun M hM A hA hcard => h18 (1 / 2) k M (by norm_num) (by norm_num) hk hM A hA hcard)
    N hN color

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
