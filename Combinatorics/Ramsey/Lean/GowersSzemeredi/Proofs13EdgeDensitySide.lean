import GowersSzemeredi.Proofs13EdgeDensity

/-! Declarations of `Proofs13EdgeDensity` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Strong-height Bohr models with the corrected Stage 13.6 set-size bound.
The density range used by the checked Theorem 10.13 remains explicit, and
the spectrum and radius use the actual edge density. -/
theorem section13_strong_height_bohr_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hαsixth : S.alpha ≤ 1 / 6) :
    let beta := section13EdgeDensity S h
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  have hbounds := section13_edge_density_bounds S h hh
  obtain ⟨Y, psi, hsub, hmass, hmodel⟩ := section13_good_height_bohr_model S h hh.2
    (section13EdgeDensity S h) hbounds.1 (hbounds.2.2.trans hαsixth)
    (section13_edge_density_card S h)
  refine ⟨Y, psi, hsub, ?_, hmodel⟩
  let a : Real := S.alpha ^ 32 / 16
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow : a ^ 6 ≤ section13EdgeDensity S h ^ 6 :=
    pow_le_pow_left₀ ha hbounds.2.1 6
  have hedge : a * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card :=
    section13_strong_height_edge_density S h hh
  have hproduct : a ^ 6 * (a * (N : Real) ^ 2) ≤
      section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card :=
    mul_le_mul hpow hedge (by positivity) (by positivity)
  have hpower : a ^ 6 * a = S.alpha ^ 224 / (2 : Real) ^ 28 := by
    dsimp only [a]
    ring
  calc
    _ ≤ (S.alpha ^ 224 / (2 : Real) ^ 28) * (N : Real) ^ 2 / 20000 := by
      norm_num [zpow_neg]
      have hnonneg : 0 ≤ S.alpha ^ 224 * (N : Real) ^ 2 :=
        mul_nonneg (pow_nonneg S.alpha_pos.le 224) (sq_nonneg _)
      nlinarith only [hnonneg]
    _ = a ^ 6 * (a * (N : Real) ^ 2) / 20000 := by rw [← hpower]; ring
    _ ≤ section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card / 20000 :=
      div_le_div_of_nonneg_right hproduct (by norm_num)
    _ ≤ Y.card := hmass

end LeanProofs.GowersSzemeredi
