import GowersSzemeredi.Proofs13UniformEdgeModels

/-! Adaptive fibre normalization removes the ambient density restriction
from the Section 13 Bohr models without changing their quantitative output. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above density 1/6, the adaptive integer cap keeps the normalized density
between 1/12 and 1/6. -/
theorem section13_dense_normalization {beta : Real} (hβ : 1 / 6 < beta) :
    let k := Nat.ceil (6 * beta)
    0 < k ∧ (1 : Real) / 12 ≤ beta / k ∧ beta / k ≤ 1 / 6 := by
  dsimp only
  have hk : 0 < Nat.ceil (6 * beta) := Nat.ceil_pos.mpr (by positivity)
  have hkreal : (0 : Real) < Nat.ceil (6 * beta) := by exact_mod_cast hk
  have hlower := Nat.le_ceil (6 * beta)
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ 6 * beta by positivity)
  refine ⟨hk, (le_div_iff₀ hkreal).mpr ?_, (div_le_iff₀ hkreal).mpr ?_⟩ <;>
    linarith only [hβ, hlower, hupper]

/-- A selected mass `b ^ 6 * |E| / 20000` with `alpha ^ 32 / 16 ≤ b` is at least
`2^-43 alpha^224 N^2`. -/
private theorem section13_edge_model_mass {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) {b : Real}
    (hb : S.alpha ^ 32 / 16 ≤ b) :
    (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤
      b ^ 6 * (verticalEdgeDomain S.A h).card / 20000 := by
  calc (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2
      ≤ (S.alpha ^ 32 / 16) ^ 6 * (S.alpha ^ 32 / 16 * (N : Real) ^ 2) / 20000 := by
        rw [zpow_neg, zpow_ofNat]
        linarith [(by positivity : (0 : Real) ≤ S.alpha ^ 224 * (N : Real) ^ 2)]
    _ ≤ _ := by
        gcongr
        exact section13_strong_height_edge_density S h hh

/-- Uniform strong-height Bohr models for every ambient density at most one.
The spectrum, radius, and selected mass are unchanged from the small-density
construction. -/
theorem section13_uniform_height_model_all_densities {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) :
    let a := S.alpha ^ 32 / 16
    let K := domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta a) Y psi := by
  have hbounds := section13_edge_density_bounds S h hh
  have ha : 0 < S.alpha ^ 32 / 16 := div_pos (pow_pos S.alpha_pos _) (by norm_num)
  obtain ⟨k, hk, hab, hb6⟩ : ∃ k : Nat, 0 < k ∧
      S.alpha ^ 32 / 16 ≤ section13EdgeDensity S h / k ∧ section13EdgeDensity S h / k ≤ 1 / 6 := by
    by_cases hsmall : section13EdgeDensity S h ≤ 1 / 6
    · exact ⟨1, one_pos, by simpa using hbounds.2.1, by simpa using hsmall⟩
    obtain ⟨hk, hbmin, hbmax⟩ := section13_dense_normalization (lt_of_not_ge hsmall)
    refine ⟨_, hk, le_trans ?_ hbmin, hbmax⟩
    linarith [pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one (n := 32)]
  have hb : 0 < section13EdgeDensity S h / k := ha.trans_le hab
  have hcap : N ≤ k * N := Nat.le_mul_of_pos_left N hk
  obtain ⟨Y, psi, hY, hmass, hmodel⟩ := section13_good_height_model_with_cap S h hh.2 (k * N)
    hcap _ hb hb6 (by rw [section13_edge_density_card]; push_cast; field_simp)
  refine ⟨Y, psi, hY, (section13_edge_model_mass S h hh hab).trans hmass,
    bohr_difference_model_restrict _ _ _ _ _ _ _ _ hmodel (bohr_domain_mono (fun r hr => ?_)
      (section10Zeta_mono ha hab (hb6.trans (by norm_num))))⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans ?_ (Finset.mem_filter.mp hr).2⟩
  unfold section10Lambda
  gcongr

end LeanProofs.GowersSzemeredi
