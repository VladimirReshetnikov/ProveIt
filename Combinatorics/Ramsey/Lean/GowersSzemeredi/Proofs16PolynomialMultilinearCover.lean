import GowersSzemeredi.Proofs16PolynomialAllScaleLemma9
import GowersSzemeredi.Proofs16WithLift

/-! Multilinear extraction with the polynomial spectrum-count recurrence.

The rounded affine lift retains the new width at every input scale. The
candidate count and mass losses are those of the existing lift. Spectrum
structure, induced selection, remainder cover, and a slice provider remain
explicit hypotheses; no higher-dimensional structure theorem is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The statement of `exists_all_scale_polynomial_multilinear_cover` at fixed constants. -/
def AllScalePolynomialMultilinearCoverAt (k : Nat) (C p : Nat) : Prop :=
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
    ∀ (Pb Es : Nat → Real → Real),
    Section16SliceProvider B1 (section16PhiOne phi x0) Pb Es →
    Section16SliceProviderRanges Pb Es →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      let sigma := rho / 4
      let l := section16PolynomialLinearityWidth m k C p (Nat.floor (Qb (rho / 8)))
        (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (rho / 8)) zeta
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        let samples := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
        ∃ (n : Nat) (E : Finset (Point N (k + 1))) (M : Nat)
          (R : Fin M → Box N (k + 1))
          (mu : Fin M → Fin n → Point N (k + 1) → ZMod N),
          (n : Real) ≤ max (Pb samples sigma)
            ((samples.choose 2 : Real) * Pb samples sigma * Pb samples sigma) ∧
          E ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ E.card ∧
          IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
          (∀ j, Real.sqrt (((Nat.floor l : Real) / 8) ^ (Es samples sigma)) / 4 ≤ (R j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j z, z ∈ (R j).carrier → z ∈ B1 → z ∈ E →
            ∃ i, section16PhiOne phi x0 z = mu j i z

/-- `exists_all_scale_polynomial_multilinear_cover` at the constants of its input. -/
theorem allScalePolynomialMultilinearCoverAt_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hlemma9 : AllScalePolynomialLemma169At k C p) : AllScalePolynomialMultilinearCoverAt k C p := by
  unfold AllScalePolynomialMultilinearCoverAt
  intro N m _ _ hk theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem Pb Es hslice hranges P hP hm
  let sigma := rho / 4
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hhalf : sigma / 2 = rho / 8 := by dsimp [sigma]; ring
  obtain ⟨qGamma, hqGamma, hcover⟩ := hlemma9 N m hk theta gamma sigma ht ht1 hg hg1 hs hs1
    Qb Eb (by simpa only [hhalf] using hQ) (by simpa only [hhalf] using ha)
    (by simpa only [hhalf] using ha1) B phi H Jbase H1 Y phiPrime x0
    hH1 hML hselection hidentity hrem P hP hm
  rw [hhalf] at hcover
  refine ⟨qGamma, hqGamma, ?_⟩
  have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1.le
  have hl : 0 ≤ section16PolynomialLinearityWidth m k C p (Nat.floor (Qb (rho / 8)))
      (((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
        section16Lemma9R theta gamma k) * Eb (rho / 8)) (section16Zeta theta gamma k) := by
    unfold section16PolynomialLinearityWidth
    positivity
  have hresult := hcover.global_affine_lift_rounded_with hslice hranges hk hl
    sigma sigma hs hs1 hs hs1
  have hmass : 1 - sigma - 2 * sigma - sigma = 1 - rho := by dsimp [sigma]; ring
  simpa only [hmass] using hresult

/-- The improved all-scale line cover followed by arbitrary slice controls. -/
theorem exists_all_scale_polynomial_multilinear_cover (k : Nat) :
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
    ∀ (Pb Es : Nat → Real → Real),
    Section16SliceProvider B1 (section16PhiOne phi x0) Pb Es →
    Section16SliceProviderRanges Pb Es →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      let sigma := rho / 4
      let l := section16PolynomialLinearityWidth m k C p (Nat.floor (Qb (rho / 8)))
        (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (rho / 8)) zeta
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        let samples := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
        ∃ (n : Nat) (E : Finset (Point N (k + 1))) (M : Nat)
          (R : Fin M → Box N (k + 1))
          (mu : Fin M → Fin n → Point N (k + 1) → ZMod N),
          (n : Real) ≤ max (Pb samples sigma)
            ((samples.choose 2 : Real) * Pb samples sigma * Pb samples sigma) ∧
          E ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ E.card ∧
          IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
          (∀ j, Real.sqrt (((Nat.floor l : Real) / 8) ^ (Es samples sigma)) / 4 ≤ (R j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j z, z ∈ (R j).carrier → z ∈ B1 → z ∈ E →
            ∃ i, section16PhiOne phi x0 z = mu j i z := by
  obtain ⟨C, p, hC, hp, hlemma9⟩ := exists_all_scale_polynomial_lemma_16_9 k
  exact ⟨C, p, hC, hp, allScalePolynomialMultilinearCoverAt_of k hC hp hlemma9⟩

end LeanProofs.GowersSzemeredi
