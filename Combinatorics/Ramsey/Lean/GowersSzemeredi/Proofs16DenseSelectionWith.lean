import GowersSzemeredi.Proofs16Lemma5With
import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16CommonBase

/-! **The dense induced selection and Lemma 16.7 with `(θ₁, ζ)` as
parameters** (Notes L.16d).

* `section16_dense_induced_selection_with`: the corpus's
  `section16_dense_induced_selection_of_arrangements` with
  `section16ThetaOne θ γ k ↦ t1` and `section16Zeta θ γ k ↦ zeta`. It
  assumes `0 < t1/4 ≤ 1/36`, `ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6`, and
  `0 < ζ`, and runs through `Proofs16Lemma5With`.
* `lemma_16_7_with`: Lemma 16.7 for any `t1 ≥ 0` and any `zeta`. The
  corpus proof never uses the printed formulas beyond `θ₁ ≥ 0`.

The induced-selection proof uses the free parameters directly. The common-base
argument is imported from `Proofs16CommonBase` and shared with the printed theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_dense_induced_selection_with {N k : Nat} [NeZero N]
    (hprime : N.Prime) (t1 zeta : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hz0 : 0 < zeta)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ phiPrime : Point N k → ZMod N → ZMod N,
          t1 / 4 * (N : Real) ^ k ≤ H.card ∧
          (∀ h ∈ H, t1 / 4 * (N : Real) ^ (k + 1) ≤
            (section16CubeDomain B h).card) ∧
          (∀ h ∈ H, (2 : Real) ^ (-(27 : Real)) * (t1) ^ 6 *
            (section16CubeDomain B h).card ≤ (Y h).card) ∧
          Section16InducedSelection B phi H Y
            (fun h => section16LargeSpectrum B h (section16Delta (t1)))
            (zeta) phiPrime := by
  obtain ⟨H, hmass, hgood⟩ :=
    section16_good_sidelengths_with t1 B phi (by linarith) hB
  have hex : ∀ h : Point N k,
      ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
        h ∈ H →
          (2 : Real) ^ (-(27 : Real)) * (t1) ^ 6 *
            (section16CubeDomain B h).card ≤ Y.card ∧
          HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
            (section16InducedCubeMap B h phi)
            (section16LargeSpectrum B h (section16Delta (t1)))
            (zeta) Y psi := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨Y, psi, hY⟩ := section16_selected_side_model_with t1 zeta B phi h ha0 haS hzeta
        (hgood h hh).1 (hgood h hh).2
      exact ⟨Y, psi, fun _ => hY⟩
    · exact ⟨∅, fun _ => 0, fun hh' => (hh hh').elim⟩
  choose Y psi hY using hex
  obtain ⟨phiPrime, hselection⟩ := section16_inducedSelection_exists B phi H Y _ _ psi hprime
    hz0.le (fun h hh => (hY h hh).2)
  exact ⟨H, Y, phiPrime, section16_sidelength_card_of_mass B H _ hmass,
    fun h hh => section16_cube_card_lower B h _ (hgood h hh).1,
    fun h hh => (hY h hh).1, hselection⟩



end LeanProofs.GowersSzemeredi
