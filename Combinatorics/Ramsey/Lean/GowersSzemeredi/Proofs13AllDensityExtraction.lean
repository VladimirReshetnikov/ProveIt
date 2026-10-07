import GowersSzemeredi.Proofs13DenseEdgeModels
import GowersSzemeredi.Proofs13LargeScaleBudgets

/-! Stage 13.6 without an ambient-density restriction. Adaptive edge fibre
normalization preserves every previously checked constant and exponent. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Construct Stage 13.6 from the initial stages and numerical budgets at
all densities allowed by Section13Context. -/
theorem lemma_13_6_from_initial_stages_all_densities {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  let K : ZMod N → Finset (ZMod N) := fun h ↦
    domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
  have hex : ∀ h : ZMod N, ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      h ∈ criticalHeights S D E →
        Y ⊆ verticalEdgeDomain S.A h ∧
        (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
        HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
          (K h) (section10Zeta a) Y psi := by
    intro h
    by_cases hh : h ∈ criticalHeights S D E
    · obtain ⟨Y, psi, hdata⟩ := section13_uniform_height_model_all_densities S h
        (Finset.mem_filter.mp hh).2
      exact ⟨Y, psi, fun _ ↦ hdata⟩
    · exact ⟨∅, fun _ ↦ 0, fun hh' ↦ (hh hh').elim⟩
  choose Y psi hdata using hex
  apply lemma_13_6_of_bohr_models S (section10Lambda a) (section10Zeta a) D E m Y K psi
    h134 h135 hm hsize hupper hlower
    (fun h hh ↦ ⟨(hdata h hh).1, (hdata h hh).2.1⟩) ?_ hbudget
    (fun h hh ↦ (hdata h hh).2.2)
  intro h hh r hr
  have hthreshold := (Finset.mem_filter.mp hr).2
  change section10Lambda a * N * N ≤
    ‖fourier (domainFibreCountFunction (section13VerticalDomain S.A h)) r‖ at hthreshold
  rw [section13_vertical_fibre_function] at hthreshold
  convert hthreshold using 1 <;> ring

/-- For every fixed positive density at most one, the numerical budgets
are automatic at sufficiently large prime moduli. -/
theorem lemma_13_6_large_N_all_densities {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N),
      S.alpha = alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      IsStage135Data S D E →
      ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_integer_budgets hα hαone
  refine ⟨N₀, fun N _ S D E hS hN h134 h135 => ?_⟩
  have hb := hN₀ N hN D.q D.m D.P.length E.Q.length h134.1
    (by simpa only [hS] using h134.2.2.2.2.1)
    (by simpa only [hS] using h134.2.2.2.2.2.1)
    h134.2.2.2.2.2.2.1 h135.2.2.2.1
  rw [← hS] at hb
  obtain ⟨m, hm, hsize, hupper, hlower, hbudget, _⟩ := hb
  exact lemma_13_6_from_initial_stages_all_densities S D E m
    h134 h135 hm hsize hupper hlower hbudget

end LeanProofs.GowersSzemeredi
