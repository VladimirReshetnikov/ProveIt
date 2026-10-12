import GowersSzemeredi.Proofs18CoverSharperShortLengths

/-! **Van der Waerden numbers with `r` colours** (Notes L.15g).

Corollary 18.7 is Theorem 18.2 at density one half, for two colours. With
`r ≥ 2` colours one class has density at least `1/r`, so Theorem 18.2 at
`δ = 1/r` gives a monochromatic `k`-term progression in every `r`-colouring
of `[1, N]` once `N ≥ szemerediThresholdAt c (1/r) k = 2^(2^(r^(2^(2^(k+c)))))`.
This is Gowers's van der Waerden bound `W(k, r) ≤ 2^2^r^2^2^(k+9)` at
`c = 9`; with Theorem 18.2 at `L + 5` it holds with `k + 5`
(`van_der_waerden_L5`, in `Proofs18CoverSharperAllDegrees`).
* `exists_color_class_ge`: some colour class of `[1, N]` has at least
  `N/r` elements;
* `Theorem182AtSharp.van_der_waerden`. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace LeanProofs.GowersSzemeredi

/-- Some colour class of `[1, N]` has at least `N/r` elements. -/
theorem exists_color_class_ge {r : Nat} (hr : 0 < r) (N : Nat) (color : Nat → Fin r) :
    ∃ c : Fin r, (N : Real) / r ≤ (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) := by
  classical
  have hsum : ((Finset.Icc 1 N).card : Real) =
      ∑ c : Fin r, (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.Icc 1 N) (t := Finset.univ)
      (f := color) (fun _ _ => Finset.mem_univ _)
    exact_mod_cast h
  have hN : ((Finset.Icc 1 N).card : Real) = N := by simp
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩
  have hle : ∑ _c : Fin r, (N : Real) / r ≤
      ∑ c : Fin r, (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ hrR.ne', ← hsum, hN]
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le hne hle
  exact ⟨c, hc⟩

/-- **Theorem 18.2 gives van der Waerden numbers for `r` colours.** -/
theorem Theorem182AtSharp.van_der_waerden {c k : Nat} (h : Theorem182AtSharp c k) {r : Nat}
    (hr : 2 ≤ r) (N : Nat) (hN : szemerediThresholdAt c (1 / (r : Real)) k ≤ N)
    (color : Nat → Fin r) : HasMonochromaticAP N r color k := by
  classical
  obtain ⟨col, hcol⟩ := exists_color_class_ge (by omega) N color
  let A := (Finset.Icc 1 N).filter fun x => color x = col
  have hrR : (2 : Real) ≤ r := by exact_mod_cast hr
  have hδ : 0 < 1 / (r : Real) := by positivity
  have hδ2 : 1 / (r : Real) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hrR
  have hAcard : 1 / (r : Real) * N ≤ A.card := by
    have : 1 / (r : Real) * N = (N : Real) / r := by ring
    rw [this]; exact hcol
  obtain ⟨a, d, hd, hmem⟩ := h (1 / (r : Real)) N hδ hδ2 hN A (Finset.filter_subset _ _) hAcard
  refine ⟨a, d, col, hd, fun i hi => ?_⟩
  have hai : a + i * d ∈ A := hmem i hi
  exact Finset.mem_filter.mp hai

end LeanProofs.GowersSzemeredi
