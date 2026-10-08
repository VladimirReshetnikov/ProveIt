import GowersSzemeredi.Proofs16PolynomialMultilinearCover
import GowersSzemeredi.Proofs16CubicUniformControls

/-! Pure-power multilinear covers with polynomial spectrum-count loss.

The threshold absorbs the rounded affine lift. Cubic slice controls give
an input-box-independent quartic candidate budget. Spectrum structure,
selection, remainder cover, and the cubic slice provider remain premises.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Retain any exponent below half the product of the polynomial line
exponent and the uniform cubic slice exponent, above an explicit threshold. -/
theorem exists_polynomial_cubic_power_cover (k : Nat) :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma rho : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < rho → rho ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb (rho / 8) → 0 < Eb (rho / 8) →
      Eb (rho / 8) ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    ∀ q : Nat, 0 < q →
    Section16SliceProvider B1 (section16PhiOne phi x0)
      (fun t _ => ((3 * (max 1 t * q) : Nat) : Real))
      (fun t => cubicBaseExponent (max 1 t * q)) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      let sigma := rho / 4
      let qD := Nat.floor (Qb (rho / 8))
      let z := zeta / (4 * ((C * (qD + 1) : Nat) : Real))
      let e := (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (rho / 8)) /
        (4 * ((2 * (p * (qD + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real))
      let R := section16UniformSampleCount sigma theta gamma k
      let a := cubicBaseExponent (R * q) sigma
      ∀ b : Real, b < e * a / 2 →
        section16RoundedExponentThreshold z e a b ≤ (m : Real) →
        ∃ (n : Nat) (E : Finset (Point N (k + 1))) (M : Nat)
          (S : Fin M → Box N (k + 1))
          (mu : Fin M → Fin n → Point N (k + 1) → ZMod N),
          (n : Real) ≤ 9 * (R : Real) ^ 4 * (q : Real) ^ 2 ∧
          E ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ E.card ∧
          IsBoxPartition S P ∧ (∀ j, (S j).IsProper) ∧
          (∀ j, (m : Real) ^ b ≤ (S j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j x, x ∈ (S j).carrier → x ∈ B1 → x ∈ E →
            ∃ i, section16PhiOne phi x0 x = mu j i x := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_all_scale_polynomial_multilinear_cover k
  refine ⟨C, p, hC, hp, ?_⟩
  intro N m _ _ hk theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem q hq hslice P hP hm
    b hb hlarge
  let sigma := rho / 4
  let qD := Nat.floor (Qb (rho / 8))
  let z := section16Zeta theta gamma k / (4 * ((C * (qD + 1) : Nat) : Real))
  let e := (((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
    section16Lemma9R theta gamma k) * Eb (rho / 8)) /
    (4 * ((2 * (p * (qD + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real))
  let R := section16UniformSampleCount sigma theta gamma k
  let a := cubicBaseExponent (R * q) sigma
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hR : 0 < R := section16UniformSampleCount_pos k hs
  have ha' : 0 < a := cubicBaseExponent_pos (Nat.mul_pos hR hq) hs
  have hzeta := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
  have hCpos : 0 < C := by omega
  have hz : 0 < z := by dsimp [z]; positivity
  have hr : 0 < section16Lemma9R theta gamma k := by
    have htwo : 1 < (2 : Nat) ^ k := one_lt_pow₀ (by norm_num) (by omega : k ≠ 0)
    have hn : (0 : Real) < ((2 ^ k - 1 : Nat) : Real) :=
      by exact_mod_cast (show 0 < 2 ^ k - 1 by omega)
    unfold section16Lemma9R multipleS
    positivity
  have hmc := multipleC_pos (k + 1) (div_pos hs (mul_pos (by norm_num : (0 : Real) < 2) hr)) hg
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨qG, hqG, n, E, M, S, mu, hn, hE, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
    hcover N m hk theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ ha ha1
      B phi H Jbase H1 Y phiPrime x0 hH1 hML hselection hidentity hrem _ _
      hslice (section16_cubic_slice_provider_ranges hq) P hP hm
  obtain ⟨haLower, hbudget⟩ := section16_cubic_uniform_lift_controls hq hs hqG
  have hquartic :
      max (((3 * (R * q) : Nat) : Real))
        ((R.choose 2 : Real) * ((3 * (R * q) : Nat) : Real) * ((3 * (R * q) : Nat) : Real)) ≤
      9 * (R : Real) ^ 4 * (q : Real) ^ 2 := by
    have h := section16_cubic_candidate_count_le_quartic (r := R) hq
    unfold section16CompressedCandidateCount at h
    rw [show max 1 R = R from max_eq_right hR] at h
    exact_mod_cast h
  refine ⟨n, E, M, S, mu, (hn.trans hbudget).trans hquartic,
    hE, hmass, hpart, hproper, ?_, hmu, hcov⟩
  have hl : z * (m : Real) ^ e ≤
      section16PolynomialLinearityWidth m k C p qD
        (((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
          section16Lemma9R theta gamma k) * Eb (rho / 8)) (section16Zeta theta gamma k) := le_rfl
  obtain ⟨hbase, hpower⟩ := section16_rounded_power_width_of_exponent hz he ha' hb hl hlarge
  intro j
  exact hpower.trans ((div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt (Real.rpow_le_rpow_of_exponent_le hbase haLower))
    (by norm_num)).trans (hw j))

end LeanProofs.GowersSzemeredi
