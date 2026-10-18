import GowersSzemeredi.Proofs18Consequences

/-! Declarations of `Proofs18Consequences` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

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
  have hdelta0 : 0 < delta0 := lt_min hdelta (by norm_num)
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
