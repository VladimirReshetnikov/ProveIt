import GowersSzemeredi.Proofs16InducedSelection

/-! Retain the domain densities of the actual Lemma 16.5 construction.
These witnesses are shared by the spectrum restriction and Lemma 16.7.

`section16_dense_induced_selection_with` is the selection with `(t1, ζ)` as
parameters; the printed one is its instance.

`section16_dense_induced_selection` and
`section16_dense_induced_selection_of_arrangements` are in
`Proofs16DenseSelectionSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_arrangement_at_side_upper {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    section16ArrangementCountAtSide 8 B h ≤ N ^ (16 * k + 15) := by
  have hu := domainAdditiveTupleCount_eight_linear_le
    (section16CubeMultifunctionDomain B h) (section16CubeMultifunctionDomain_fibre_card_le B h)
  rw [section16_domainAdditiveTupleCount_eq_arrangementCountAtSide, section16CubeElement_card] at hu
  calc
    _ ≤ (section16CubeDomain B h).card * (N ^ k) ^ 15 * N ^ 14 := hu
    _ ≤ N ^ (k + 1) * (N ^ k) ^ 15 * N ^ 14 := by
      gcongr
      exact section16_cube_card_le B h
    _ = _ := by ring

/-- The selected sidelengths have the required density; the weighted
arrangement mass cannot be concentrated beyond the full fixed-side count. -/
theorem section16_sidelength_card_of_mass {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k)) (a : Real)
    (hm : a * (N : Real) ^ (17 * k + 15) ≤
      ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real)) :
    a * (N : Real) ^ k ≤ H.card := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hu : (∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real)) ≤
      (H.card : Real) * (N : Real) ^ (16 * k + 15) := by
    calc
      _ ≤ ∑ _h ∈ H, (N : Real) ^ (16 * k + 15) := by
        apply Finset.sum_le_sum
        intro h _
        exact_mod_cast section16_arrangement_at_side_upper B h
      _ = _ := by simp
  apply (mul_le_mul_iff_left₀ (pow_pos hN (16 * k + 15))).mp
  calc
    (a * (N : Real) ^ k) * (N : Real) ^ (16 * k + 15) =
        a * (N : Real) ^ (17 * k + 15) := by ring
    _ ≤ _ := hm.trans hu

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
