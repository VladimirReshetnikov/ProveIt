import GowersSzemeredi.Proofs16PolynomialMultilinearCover
import GowersSzemeredi.Proofs16VarietyFamilyLiftControls
import GowersSzemeredi.Proofs16VarietyFamilySlices

/-! Pure-power three-dimensional covers from bounded families of variety pieces on slices.
The polynomial line recurrence and the joint variety cover yield a
quartic candidate count. Spectrum structure, selection, remainder cover,
and a cover of every slice by Q variety pieces remain inputs.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every slice family supplies its simultaneous cover; the final
power exponent uses the uniform sample ceiling and explicit polynomial
variety controls. -/
theorem exists_polynomial_variety_family_power_cover :
  ∃ C p Cv pv : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime],
    ∀ (theta gamma rho : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < rho → rho ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb (rho / 8) → 0 < Eb (rho / 8) →
      Eb (rho / 8) ≤ 1 →
    ∀ (B : Finset (Point N 3))
      (phi : Point N 3 → ZMod N)
      (H Jbase H1 : Finset (Point N 2))
      (Y : (h : Point N 2) → Finset (Section16CubeElement B h))
      (phiPrime : Point N 2 → ZMod N → ZMod N) (x0 : Point N 2),
    let theta1 := section16ThetaOne theta gamma 2
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma 2
    let r := section16Lemma9R theta gamma 2
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    ∀ (D Q : Nat) (c : Real), 0 < Q → 0 < c → c ≤ 1 →
    Section16FinalStackable Q (section16VarietyPieceClass N D c) B phi →
    ∀ P : Box N 3, P.IsProper → m ≤ P.width →
      let sigma := rho / 4
      let qD := Nat.floor (Qb (rho / 8))
      let z := zeta / (4 * ((C * (qD + 1) : Nat) : Real))
      let e := (((multipleC (sigma / (2 * r)) gamma 3) ^ r) * Eb (rho / 8)) /
        (4 * ((2 * (p * (qD + 1) ^ (2 * (2 ^ 3))) : Nat) : Real))
      let R := section16UniformSampleCount sigma theta gamma 2
      let a := section16PolynomialJointVarietyExponent Cv pv (R * Q) D c
      ∀ b : Real, b < e * a / 2 →
        section16RoundedExponentThreshold z e a b ≤ (m : Real) →
        ∃ (n : Nat) (E : Finset (Point N 3)) (M : Nat)
          (S : Fin M → Box N 3)
          (mu : Fin M → Fin n → Point N 3 → ZMod N),
          (n : Real) ≤ 81 * (R : Real) ^ 4 * (Q : Real)^2 ∧
          E ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ E.card ∧
          IsBoxPartition S P ∧ (∀ j, (S j).IsProper) ∧
          (∀ j, (m : Real) ^ b ≤ (S j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j x, x ∈ (S j).carrier → x ∈ B1 → x ∈ E →
            ∃ i, section16PhiOne phi x0 x = mu j i x := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_all_scale_polynomial_multilinear_cover 2
  obtain ⟨Cv, pv, hCv, hpv, hprovider⟩ := exists_variety_family_good_domain_slice_provider
  refine ⟨C, p, Cv, pv, hC, hp, hCv, hpv, ?_⟩
  intro N m _ _ theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem D Q c hQpieces hc hc1 hpiece P hP hm
    b hb hlarge
  let sigma := rho / 4
  let qD := Nat.floor (Qb (rho / 8))
  let z := section16Zeta theta gamma 2 / (4 * ((C * (qD + 1) : Nat) : Real))
  let e := (((multipleC (sigma / (2 * section16Lemma9R theta gamma 2)) gamma 3) ^
    section16Lemma9R theta gamma 2) * Eb (rho / 8)) /
    (4 * ((2 * (p * (qD + 1) ^ (2 * (2 ^ 3))) : Nat) : Real))
  let R := section16UniformSampleCount sigma theta gamma 2
  let a := section16PolynomialJointVarietyExponent Cv pv (R * Q) D c
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have ha' : 0 < a := section16PolynomialJointVarietyExponent_pos Cv (R * Q) D hpv hc hc1
  have hzeta := (section16Zeta_pos_le_half 2 ht ht1 hg hg1).1
  have hCpos : 0 < C := by omega
  have hz : 0 < z := by dsimp [z]; positivity
  have hr : 0 < section16Lemma9R theta gamma 2 := by
    have hn : (0 : Real) < ((2 ^ 2 - 1 : Nat) : Real) :=
      by norm_num
    unfold section16Lemma9R multipleS
    positivity
  have hmc := multipleC_pos 3 (div_pos hs (mul_pos (by norm_num : (0 : Real) < 2) hr)) hg
  have he : 0 < e :=
    div_pos (mul_pos (Real.rpow_pos_of_pos hmc _) ha) (by positivity)
  obtain ⟨hslice, hranges⟩ := hprovider N D Q c hQpieces hc hc1 B phi hpiece H1 Y x0
  obtain ⟨qG, hqG, n, E, M, S, mu, hn, hE, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
    hcover N m (by decide) theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ ha ha1
      B phi H Jbase H1 Y phiPrime x0 hH1 hML hselection hidentity hrem _ _
      hslice hranges P hP hm
  obtain ⟨haLower, hbudget⟩ :=
    section16_variety_family_uniform_lift_controls Cv D hpv hQpieces hc hc1 hs hqG
  refine ⟨n, E, M, S, mu, hn.trans hbudget,
    hE, hmass, hpart, hproper, ?_, hmu, hcov⟩
  have hl : z * (m : Real) ^ e ≤
      section16PolynomialLinearityWidth m 2 C p qD
        (((multipleC (sigma / (2 * section16Lemma9R theta gamma 2)) gamma 3) ^
          section16Lemma9R theta gamma 2) * Eb (rho / 8)) (section16Zeta theta gamma 2) := le_rfl
  obtain ⟨hbase, hpower⟩ := section16_rounded_power_width_of_exponent hz he ha' hb hl hlarge
  intro j
  exact hpower.trans ((div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt (Real.rpow_le_rpow_of_exponent_le hbase haLower))
    (by norm_num)).trans (hw j))

end LeanProofs.GowersSzemeredi
