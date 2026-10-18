import GowersSzemeredi.Proofs16ArrangementSelection
import GowersSzemeredi.Proofs10Main
import GowersSzemeredi.Proofs16DomainBounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Extracting Bohr difference models on many fixed-side cube domains

`section16_selected_side_model_with` and `lemma_16_5_with` take the density
and the radius `(t1, ζ)` as parameters, under `0 < t1/4 ≤ 1/36` and
`ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6` (Notes L.16d). The printed values
satisfy these (`lemma_16_5_with_printed_hyps`), and the printed results are
the instances.

`lemma_16_5_holds`, `lemma_16_5_with` and `lemma_16_5_with_printed_hyps` are in
`Proofs16Lemma5Side`, outside the final route. -/
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
  let D := section16CubeMultifunctionDomain B h
  have hN : 0 < N := NeZero.pos N
  obtain ⟨L, hML, _, hL, alpha, halpha, halpha0, halpha1, hcard⟩ :=
    domain_density_reparameterize (Fintype.card (Section16CubeElement B h)) N (N ^ k)
      hN (pow_pos hN k) _ ha0 haS
      (by simpa only [section16CubeElement_card, pow_succ, Nat.cast_pow, mul_assoc] using
        section16_cube_card_lower B h _ hcount)
      (by exact_mod_cast (by simpa only [section16CubeElement_card, pow_succ] using
        section16_cube_card_le B h : Fintype.card (Section16CubeElement B h) ≤ N ^ k * N))
  obtain ⟨_, _, Y, psi, hY, hmodel⟩ := theorem_10_13_holds N L
    (Section16CubeElement B h) D (section16InducedCubeMap B h phi) alpha
    halpha0 halpha1 hL (fun s => (section16CubeMultifunctionDomain_fibre_card_le B h s).trans hML)
    hcard happrox
  have htheta1 : 0 ≤ t1 := by linarith
  have hc : (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 ≤ alpha ^ 6 / 20000 := calc
    _ ≤ (1 / 4 : Real) ^ 6 / 20000 * t1 ^ 6 := by
        gcongr; norm_num [Real.rpow_neg, Real.rpow_ofNat]
    _ = (t1 / 4) ^ 6 / 20000 := by ring
    _ ≤ _ := by gcongr
  refine ⟨Y, psi, ?_, ?_⟩
  · rw [← section16CubeElement_card]
    exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans
      (by rw [div_mul_eq_mul_div]; exact hY)
  · have hlam : section16Delta t1 ≤ section10Lambda alpha :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha0.le halpha (by norm_num)) (by positivity)
    have hthreshold :
        section16Delta t1 * (N : Real) ^ (k + 1) ≤ section10Lambda alpha * L * N := by
      have hMLr : (N : Real) ^ k ≤ L := by exact_mod_cast hML
      have hlam0 : 0 ≤ section16Delta t1 := by unfold section16Delta; positivity
      rw [pow_succ, ← mul_assoc]
      gcongr
      exact hlam0.trans hlam
    have hK : domainLargeSpectrum D (section10Lambda alpha * L * N) ⊆
        section16LargeSpectrum B h (section16Delta t1) := fun r hr => by
      simp only [section16_spectrum_eq_domain, domainLargeSpectrum, Finset.mem_filter,
        Finset.mem_univ, true_and] at hr ⊢
      exact hthreshold.trans hr
    refine hmodel.restrict_bohr fun d hd => ?_
    simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact fun r hr => (hd r (hK hr)).trans
      (mul_le_mul_of_nonneg_right (hzeta alpha halpha halpha1) (Nat.cast_nonneg N))

end LeanProofs.GowersSzemeredi
