import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs16TightRadius

/-! **Lemma 16.5 with the arrangement density and the Bohr radius as
parameters** (Notes L.16d).

The proof of Lemma 16.5 (`Proofs16Lemma5`, `Proofs16ArrangementSelection`)
uses the printed `θ₁ = section16ThetaOne θ γ k` and
`ζ = section16Zeta θ γ k` only through:
* `0 < θ₁/4 ≤ 1/36`, for the density reparameterization;
* `ζ ≤ section10Zeta α` for every `θ₁/4 ≤ α ≤ 1/6`, for the radius
  comparison with Theorem 10.13.

Here both are parameters `(t1, zeta)`. The two proof steps are the corpus
proofs verbatim, with `section16ThetaOne θ γ k ↦ t1` and
`section16Zeta θ γ k ↦ zeta`:
* `section16_good_sidelengths_with`;
* `section16_selected_side_model_with`.

`lemma_16_5_with` assembles them. Its instances are the printed pair
(`lemma_16_5_with_printed`), and the Fejér density with the tight radius
`tightZeta (t1/4)` (`tightZeta_condition`), which is the input the
propagation of Notes L.16 needs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_good_sidelengths_with {N k : Nat} [NeZero N]
    (t1 : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ht1 : 0 ≤ t1)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      t1 / 4 * (N : Real) ^ (17 * k + 15) ≤
        ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∀ h ∈ H,
        t1 / 4 * (N : Real) ^ (16 * k + 15) ≤
          section16ArrangementCountAtSide 8 B h ∧
        DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8 := by
  classical
  let eta : Real := (2 : Real) ^ (-(44 : Real))
  let t : Real := t1 / 4 * (N : Real) ^ (16 * k + 15)
  let C (h : Point N k) : Real := section16ArrangementCountAtSide 8 B h
  let G (h : Point N k) : Real := section16RespectedArrangementCountAtSide 8 B phi h
  let H := Finset.univ.filter fun h => (1 - 2 * eta) * C h ≤ G h ∧ t ≤ C h
  have heta : 0 < eta := by dsimp [eta]; positivity
  have ht : 0 ≤ t := by dsimp [t]; exact mul_nonneg (div_nonneg ht1 (by norm_num)) (by positivity)
  have hC : (∑ h, C h) = generalArrangementCount 8 B := by
    dsimp [C]
    rw [← Nat.cast_sum, section16_sum_arrangementCountAtSide]
  have hG : (∑ h, G h) = respectedGeneralArrangementCount 8 B phi := by
    dsimp [G]
    rw [← Nat.cast_sum, section16_sum_respectedArrangementCountAtSide]
  have hGC (h : Point N k) : G h ≤ C h := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    exact ⟨hR.1, hR.2.1⟩
  have hrespect : (1 - eta) * ∑ h, C h ≤ ∑ h, G h := by
    rw [hC, hG]
    exact hB.2
  have hmass := weighted_good_large_mass C G eta t heta ht hGC hrespect
  have htotal : t1 * (N : Real) ^ (17 * k + 15) ≤ ∑ h, C h := by
    rw [hC]
    exact hB.1
  have hcard : Fintype.card (Point N k) = N ^ k := by simp [Point, ZMod.card]
  have hbudget : (Fintype.card (Point N k) : Real) * t =
      t1 / 4 * (N : Real) ^ (17 * k + 15) := by
    rw [hcard, Nat.cast_pow]
    dsimp [t]
    rw [show 17 * k + 15 = k + (16 * k + 15) by omega, pow_add]
    ring
  refine ⟨H, ?_, ?_⟩
  · change _ ≤ ∑ h ∈ H, C h
    simp only [H, Finset.sum_filter]
    rw [hbudget] at hmass
    linarith
  · intro h hh
    have hgood : (1 - 2 * eta) * C h ≤ G h ∧ t ≤ C h := by simpa [H] using hh
    refine ⟨hgood.2, section16_domainApproxHomOfOrder_of_arrangementCounts B h phi _ ?_⟩
    have he : 2 * eta = (2 : Real) ^ (-(43 : Real)) := by norm_num [eta, Real.rpow_neg]
    rw [← he]
    exact hgood.1


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
  classical
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
  classical
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

/-- The printed parameters satisfy the hypotheses: `lemma_16_5_with` contains
the printed Lemma 16.5's conclusion. -/
theorem lemma_16_5_with_printed_hyps {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k / 4 ∧ section16ThetaOne theta gamma k / 4 ≤ 1 / 36 ∧
      ∀ alpha : Real, section16ThetaOne theta gamma k / 4 ≤ alpha → alpha ≤ 1 / 6 →
        section16Zeta theta gamma k ≤ section10Zeta alpha := by
  obtain ⟨h0, h1⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  exact ⟨h0, h1, fun alpha ha ha1 => section16_zeta_le_section10Zeta k ht ht1 hg hg1 ha ha1⟩

/-- The tight radius `tightZeta (t1/4)` satisfies the radius hypothesis for
every density `t1`. -/
theorem tightZeta_condition {t1 : Real} (ha0 : 0 < t1 / 4) :
    ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → tightZeta (t1 / 4) ≤ section10Zeta alpha :=
  fun _ ha ha1 => tightZeta_le_section10Zeta ha0 ha ha1

end LeanProofs.GowersSzemeredi
