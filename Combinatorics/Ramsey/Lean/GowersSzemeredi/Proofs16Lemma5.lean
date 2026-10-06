import GowersSzemeredi.Proofs16ArrangementSelection
import GowersSzemeredi.Proofs16RadiusComparison
import GowersSzemeredi.Proofs10Main

/-! # Extracting Bohr difference models on many fixed-side cube domains -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A difference model restricts to any smaller Bohr neighborhood. -/
theorem HasBohrDifferenceModel.restrict_bohr {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] {D : MultifunctionDomain N X}
    {phi : X → ZMod N} {K L : Finset (ZMod N)} {r s : Real}
    {Y : Finset X} {psi : ZMod N → ZMod N}
    (h : HasBohrDifferenceModel D phi K r Y psi) (hsub : bohr L s ⊆ bohr K r) :
    HasBohrDifferenceModel D phi L s Y psi := by
  refine ⟨IsAddFreimanHom.subset hsub h.1 (Set.mapsTo_univ _ _), ?_⟩
  intro y hy z hz hd
  exact h.2 y hy z hz (hsub hd)

/-- Apply Theorem 10.13 to a single selected sidelength, including exact
density normalization, the spectrum inclusion, and the radius comparison. -/
theorem section16_selected_side_model {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (h : Point N k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hcount : section16ThetaOne theta gamma k / 4 * (N : Real) ^ (16 * k + 15) ≤
      section16ArrangementCountAtSide 8 B h)
    (happrox : DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
      (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8) :
    ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
      (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
          (section16CubeDomain B h).card ≤ Y.card ∧
      HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
        (section16InducedCubeMap B h phi) (section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
        (section16Zeta theta gamma k) Y psi := by
  classical
  let a := section16ThetaOne theta gamma k / 4
  let D := section16CubeMultifunctionDomain B h
  obtain ⟨ha, haSmall⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  have hlow := section16_cube_card_lower B h a hcount
  have hhigh := section16_cube_card_le B h
  have hN : 0 < N := NeZero.pos N
  obtain ⟨L, hML, _, hL, alpha, halpha, halpha0, halpha1, hcard⟩ :=
    domain_density_reparameterize (Fintype.card (Section16CubeElement B h)) N (N ^ k)
      hN (pow_pos hN k) a ha haSmall
      (by simpa only [section16CubeElement_card, pow_succ, Nat.cast_pow, mul_assoc] using hlow)
      (by exact_mod_cast (by simpa only [section16CubeElement_card, pow_succ] using hhigh :
        Fintype.card (Section16CubeElement B h) ≤ N ^ k * N))
  obtain ⟨_, _, Y, psi, hY, hmodel⟩ := theorem_10_13_holds N L
    (Section16CubeElement B h) D (section16InducedCubeMap B h phi) alpha
    halpha0 halpha1 hL (fun s => (section16CubeMultifunctionDomain_fibre_card_le B h s).trans hML)
    hcard happrox
  have htheta1 : 0 ≤ section16ThetaOne theta gamma k := by
    unfold section16ThetaOne; positivity
  have hc : (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 ≤ alpha ^ 6 / 20000 := by
    calc
      _ ≤ ((1 / 4 : Real) ^ (6 : Nat) / 20000) * (section16ThetaOne theta gamma k) ^ 6 :=
        mul_le_mul_of_nonneg_right (by norm_num [Real.rpow_neg, Real.rpow_ofNat]) (pow_nonneg htheta1 6)
      _ = a ^ 6 / 20000 := by dsimp [a]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ ha.le halpha 6) (by norm_num)
  refine ⟨Y, psi, ?_, ?_⟩
  · rw [← section16CubeElement_card] at ⊢
    calc
      _ ≤ (alpha ^ 6 / 20000) * Fintype.card (Section16CubeElement B h) :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ = alpha ^ 6 * Fintype.card (Section16CubeElement B h) / 20000 := by ring
      _ ≤ Y.card := hY
  · have hlam : section16Delta (section16ThetaOne theta gamma k) ≤ section10Lambda alpha := by
      change (2 : Real) ^ (-(37 : Real)) * a ^ ((11 : Real) / 2) ≤ _
      unfold section10Lambda
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le halpha (by norm_num)) (by positivity)
    have hthreshold : section16Delta (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1) ≤
        section10Lambda alpha * L * N := by
      rw [pow_succ, ← mul_assoc]
      have hMLr : (N : Real) ^ k ≤ L := by exact_mod_cast hML
      have hlam0 : 0 ≤ section16Delta (section16ThetaOne theta gamma k) := by
        unfold section16Delta; positivity
      gcongr
      exact hlam0.trans hlam
    have hK : domainLargeSpectrum D (section10Lambda alpha * L * N) ⊆
        section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)) := by
      rw [section16_spectrum_eq_domain]
      intro r hr
      simp only [domainLargeSpectrum, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hthreshold.trans hr
    apply hmodel.restrict_bohr
    intro d hd
    simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    intro r hr
    exact (hd r (hK hr)).trans (mul_le_mul_of_nonneg_right
      (section16_zeta_le_section10Zeta k ht ht1 hg hg1 halpha halpha1) (Nat.cast_nonneg N))

/-- Exact companion for Lemma 16.5. -/
theorem lemma_16_5_holds : lemma_16_5 := by
  classical
  intro N k _ theta gamma B phi ht ht1 hg hg1 hB
  dsimp only
  obtain ⟨H, hmass, hgood⟩ := section16_good_sidelengths theta gamma B phi ht hg hB
  refine ⟨H, hmass, ?_⟩
  have hex : ∀ h : Point N k,
      ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
        h ∈ H →
        (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
            (section16CubeDomain B h).card ≤ Y.card ∧
        HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) (section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
          (section16Zeta theta gamma k) Y psi := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨Y, psi, hY⟩ := section16_selected_side_model theta gamma B phi h ht ht1 hg hg1
        (hgood h hh).1 (hgood h hh).2
      exact ⟨Y, psi, fun _ => hY⟩
    · exact ⟨∅, fun _ => 0, fun hmem => (hh hmem).elim⟩
  choose Y psi hY using hex
  exact ⟨Y, psi, hY⟩

end LeanProofs.GowersSzemeredi
