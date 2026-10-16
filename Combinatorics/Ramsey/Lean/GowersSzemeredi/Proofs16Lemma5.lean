import GowersSzemeredi.Proofs16ArrangementSelection
import GowersSzemeredi.Proofs16RadiusComparison
import GowersSzemeredi.Proofs10Main

/-! # Extracting Bohr difference models on many fixed-side cube domains

`section16_selected_side_model_with` and `lemma_16_5_with` take the density
and the radius `(t1, ζ)` as parameters, under `0 < t1/4 ≤ 1/36` and
`ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6` (Notes L.16d). The printed values
satisfy these (`lemma_16_5_with_printed_hyps`), and the printed results are
the instances. -/
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

/-- The printed parameters satisfy the hypotheses: `lemma_16_5_with` contains
the printed Lemma 16.5's conclusion. -/
theorem lemma_16_5_with_printed_hyps {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k / 4 ∧ section16ThetaOne theta gamma k / 4 ≤ 1 / 36 ∧
      ∀ alpha : Real, section16ThetaOne theta gamma k / 4 ≤ alpha → alpha ≤ 1 / 6 →
        section16Zeta theta gamma k ≤ section10Zeta alpha := by
  obtain ⟨h0, h1⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  exact ⟨h0, h1, fun alpha ha ha1 => section16_zeta_le_section10Zeta k ht ht1 hg hg1 ha ha1⟩

theorem section16_selected_side_model_with {N k : Nat} [NeZero N]
    (t1 zeta : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (h : Point N k)
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hcount : t1 / 4 * (N : Real) ^ (16 * k + 15) ≤
      section16ArrangementCountAtSide 8 B h)
    (happrox : DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
      (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8) :
    ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
      (2 : Real) ^ (-(27 : Real)) * (t1) ^ 6 *
          (section16CubeDomain B h).card ≤ Y.card ∧
      HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
        (section16InducedCubeMap B h phi) (section16LargeSpectrum B h (section16Delta (t1)))
        (zeta) Y psi := by
  let a := t1 / 4
  let D := section16CubeMultifunctionDomain B h
  have ha : 0 < a := ha0
  have haSmall : a ≤ 1 / 36 := haS
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
  have htheta1 : 0 ≤ t1 := by linarith
  have hc : (2 : Real) ^ (-(27 : Real)) * (t1) ^ 6 ≤ alpha ^ 6 / 20000 := by
    calc
      _ ≤ ((1 / 4 : Real) ^ (6 : Nat) / 20000) * (t1) ^ 6 :=
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
  · have hlam : section16Delta (t1) ≤ section10Lambda alpha := by
      change (2 : Real) ^ (-(37 : Real)) * a ^ ((11 : Real) / 2) ≤ _
      unfold section10Lambda
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le halpha (by norm_num)) (by positivity)
    have hthreshold : section16Delta (t1) * (N : Real) ^ (k + 1) ≤
        section10Lambda alpha * L * N := by
      rw [pow_succ, ← mul_assoc]
      have hMLr : (N : Real) ^ k ≤ L := by exact_mod_cast hML
      have hlam0 : 0 ≤ section16Delta (t1) := by
        unfold section16Delta; positivity
      gcongr
      exact hlam0.trans hlam
    have hK : domainLargeSpectrum D (section10Lambda alpha * L * N) ⊆
        section16LargeSpectrum B h (section16Delta (t1)) := by
      rw [section16_spectrum_eq_domain]
      intro r hr
      simp only [domainLargeSpectrum, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hthreshold.trans hr
    apply hmodel.restrict_bohr
    intro d hd
    simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    intro r hr
    exact (hd r (hK hr)).trans (mul_le_mul_of_nonneg_right
      (hzeta alpha halpha halpha1) (Nat.cast_nonneg N))

/-- **Lemma 16.5 with parameters**: from the arrangement conditions at density
`t1`, many sidelengths carry a Bohr difference model at radius `zeta`. -/
theorem lemma_16_5_with {N k : Nat} [NeZero N] (t1 zeta : Real)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤ generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      t1 / 4 * (N : Real) ^ (17 * k + 15) ≤
          ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ psi : Point N k → ZMod N → ZMod N,
          ∀ h, h ∈ H →
            (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 *
                (section16CubeDomain B h).card ≤ (Y h).card ∧
            HasBohrDifferenceModel
              (section16CubeMultifunctionDomain B h)
              (section16InducedCubeMap B h phi)
              (section16LargeSpectrum B h (section16Delta t1)) zeta (Y h) (psi h) := by
  have ht1 : 0 ≤ t1 := by linarith
  obtain ⟨H, hmass, hgood⟩ := section16_good_sidelengths_with t1 B phi ht1 hB
  refine ⟨H, hmass, ?_⟩
  have hex : ∀ h : Point N k,
      ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
        h ∈ H →
        (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 * (section16CubeDomain B h).card ≤ Y.card ∧
        HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) (section16LargeSpectrum B h (section16Delta t1))
          zeta Y psi := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨Y, psi, hY⟩ := section16_selected_side_model_with t1 zeta B phi h ha0 haS hzeta
        (hgood h hh).1 (hgood h hh).2
      exact ⟨Y, psi, fun _ => hY⟩
    · exact ⟨∅, fun _ => 0, fun hmem => (hh hmem).elim⟩
  choose Y psi hY using hex
  exact ⟨Y, psi, hY⟩

/-- Exact companion for Lemma 16.5. -/
theorem lemma_16_5_holds : lemma_16_5 := by
  intro N k _ theta gamma B phi ht ht1 hg hg1 hB
  have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1
  exact lemma_16_5_with _ _ B phi hp.1 hp.2.1 hp.2.2 hB.2

end LeanProofs.GowersSzemeredi
