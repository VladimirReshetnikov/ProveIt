import GowersSzemeredi.Proofs16GlobalLiftParameters

/-! A positive replacement interface for the two packaged Lemma 16.10
premises. It retains the graph count and width actually delivered by the
sampling and interpolation argument, with total exceptional mass rho.
No comparison with the refuted unit-parameter control is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem Section16AllBoxLineCovers.explicit_multilinear_cover {N k : Nat} [Fact N.Prime]
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma s : Real}
    (hline : Section16AllBoxLineCovers theta gamma B phi)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hk : 0 < k) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N (k + 1)) (hP : P.IsProper) (hm : m ≤ P.width) :
    let sigma := rho / 4
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    ∃ qGamma qDelta : Nat,
      (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
      (qDelta : Real) ≤ section16Lemma9DeltaQBound sigma delta theta1 k ∧
      let l := section16Lemma9Width m qDelta k sigma theta gamma delta theta1 zeta
      let r := Nat.ceil (6 * (max 1 qGamma : Real) / sigma)
      let b := (multipleQ (((r : Real) * s)⁻¹ * sigma) gamma k) ^ ((r : Real) * s)
      ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
        (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
        (n : Real) ≤ max b ((r.choose 2 : Real) * b * b) ∧
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, Real.sqrt (((Nat.floor l : Real) / 8) ^
          ((multipleC (((r : Real) * s)⁻¹ * sigma) gamma k) ^ ((r : Real) * s))) / 4 ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  let sigma := rho / 4
  have hσ : 0 < sigma := by dsimp [sigma]; positivity
  have hσ1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  obtain ⟨qGamma, qDelta, hqG, hqD, hcover⟩ := hline sigma hσ hσ1 m P hP hm
  refine ⟨qGamma, qDelta, hqG, hqD, ?_⟩
  have hl : 0 ≤ section16Lemma9Width m qDelta k sigma theta gamma
      (section16Delta (section16ThetaOne theta gamma k))
      (section16ThetaOne theta gamma k) (section16Zeta theta gamma k) := by
    unfold section16Lemma9Width section16Zeta
    positivity
  have hresult := hcover.global_affine_lift_rounded hsections hk hg hg1 hs hl
    sigma sigma hσ hσ1 hσ hσ1
  have hmass : 1 - sigma - 2 * sigma - sigma = 1 - rho := by dsimp [sigma]; ring
  simpa only [hmass, Nat.cast_max, Nat.cast_one] using hresult

end LeanProofs.GowersSzemeredi
