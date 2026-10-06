import GowersSzemeredi.Proofs13EdgeDensity

/-! Uniform Bohr models for all strong heights. Actual edge densities vary;
monotonicity permits a common lower density parameter without pretending
that the edge cardinalities equal their lower bound. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The rounded spectrum parameter decreases as density increases. -/
theorem section10SpectrumParameter_antitone {a b : Real}
    (ha : 0 < a) (hab : a ≤ b) :
    section10SpectrumParameter b ≤ section10SpectrumParameter a := by
  apply Nat.ceil_mono
  unfold section10SpectrumBound
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos ha hab (by norm_num)) (by positivity)

/-- The corrected Bohr radius increases with the density, including the
rounded spectrum parameter and its denominator. -/
theorem section10Zeta_mono {a b : Real} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    section10Zeta a ≤ section10Zeta b := by
  have hbpos : 0 < b := ha.trans_le hab
  have hka : 0 < section10SpectrumParameter a := by
    apply Nat.ceil_pos.mpr
    unfold section10SpectrumBound
    positivity
  have hkb : 0 < section10SpectrumParameter b := by
    apply Nat.ceil_pos.mpr
    unfold section10SpectrumBound
    positivity
  have hk := section10SpectrumParameter_antitone ha hab
  have hkReal : (section10SpectrumParameter b : Real) ≤ section10SpectrumParameter a :=
    by exact_mod_cast hk
  have hp : a ^ (18 * section10SpectrumParameter a) ≤
      b ^ (18 * section10SpectrumParameter b) := by
    calc
      _ ≤ b ^ (18 * section10SpectrumParameter a) := pow_le_pow_left₀ ha.le hab _
      _ ≤ _ := pow_le_pow_of_le_one hbpos.le hb (Nat.mul_le_mul_left 18 hk)
  have htwo : (2 : Real) ^ (-(155 : Real) * section10SpectrumParameter a) ≤
      (2 : Real) ^ (-(155 : Real) * section10SpectrumParameter b) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  unfold section10Zeta
  apply div_le_div₀
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (pow_nonneg hbpos.le _))
    (mul_le_mul htwo hp (pow_nonneg ha.le _) (Real.rpow_nonneg (by norm_num) _))
    (by exact_mod_cast hkb) hkReal

/-- More frequencies and a smaller radius give a smaller Bohr domain. -/
theorem bohr_domain_mono {N : Nat} [NeZero N] {K L : Finset (ZMod N)} {r s : Real}
    (hK : K ⊆ L) (hrs : r ≤ s) : bohr L r ⊆ bohr K s := by
  classical
  intro d hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro k hk
  exact ((Finset.mem_filter.mp hd).2 k (hK hk)).trans
    (mul_le_mul_of_nonneg_right hrs (Nat.cast_nonneg _))

/-- Restrict a Bohr difference model to any smaller Bohr domain. -/
theorem bohr_difference_model_restrict {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (K L : Finset (ZMod N)) (r s : Real) (Y : Finset X) (psi : ZMod N → ZMod N)
    (hmodel : HasBohrDifferenceModel D phi K r Y psi)
    (hsub : bohr L s ⊆ bohr K r) : HasBohrDifferenceModel D phi L s Y psi := by
  refine ⟨IsAddFreimanHom.subset hsub hmodel.1 (Set.mapsTo_univ _ _), ?_⟩
  intro v hv w hw hdiff
  exact hmodel.2 v hv w hw (hsub hdiff)

/-- All strong heights have models at the same lower-density threshold and
radius, retaining the corrected set-size bound. -/
theorem section13_uniform_height_bohr_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hαsixth : S.alpha ≤ 1 / 6) :
    let a := S.alpha ^ 32 / 16
    let K := domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta a) Y psi := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  have ha : 0 < a := by dsimp [a]; have := S.alpha_pos; positivity
  have hbounds := section13_edge_density_bounds S h hh
  have hβone : section13EdgeDensity S h ≤ 1 := hbounds.2.2.trans S.alpha_at_most_one
  have hzeta := section10Zeta_mono ha hbounds.2.1 hβone
  have hlam : section10Lambda a ≤ section10Lambda (section13EdgeDensity S h) := by
    unfold section10Lambda
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ha.le hbounds.2.1 (by norm_num)) (by positivity)
  obtain ⟨Y, psi, hY, hmass, hmodel⟩ := section13_strong_height_bohr_model S h hh hαsixth
  refine ⟨Y, psi, hY, hmass, ?_⟩
  apply bohr_difference_model_restrict _ _ _ _ _ _ _ _ hmodel
  apply bohr_domain_mono ?_ hzeta
  intro r hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans
      (Finset.mem_filter.mp hr).2

/-- Stage 13.6 from the preceding stages and explicit numerical budgets.
All row subsets and Bohr models are constructed; only the density range and
integer/radius inequalities remain as hypotheses. The upper progression
length is preserved for the later coefficient extraction. -/
theorem lemma_13_6_from_initial_stages {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (hαsixth : S.alpha ≤ 1 / 6)
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
    · obtain ⟨Y, psi, hdata⟩ := section13_uniform_height_bohr_model S h
        (Finset.mem_filter.mp hh).2 hαsixth
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

end LeanProofs.GowersSzemeredi
