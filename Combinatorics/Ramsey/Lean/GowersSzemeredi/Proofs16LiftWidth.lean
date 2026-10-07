import GowersSzemeredi.Proofs16LocalAffineLift

/-! # An explicit rounded width for synchronized affine lifting -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Choose the integer tiling scale without hiding either rounding loss.
For refined base width w>=16, the final box width is at least sqrt(w)/4. -/
theorem section16_lift_width_rounding {w : ℝ} (hw : 16 ≤ w) :
    ∃ v : Nat, 1 ≤ v ∧ (v : ℝ) ^ 2 + 1 ≤ w ∧
      Real.sqrt w / 4 ≤ (v - 1 : Nat) := by
  have hw0 : 0 ≤ w := by linarith
  have hs0 := Real.sqrt_nonneg w
  have hs2 := Real.sq_sqrt hw0
  have hs4 : 4 ≤ Real.sqrt w := by nlinarith
  let v := Nat.floor (Real.sqrt w / 2) + 1
  have hfloor := Nat.floor_le (show 0 ≤ Real.sqrt w / 2 by positivity)
  have hvupper : (v : ℝ) ≤ Real.sqrt w / 2 + 1 := by
    dsimp [v]
    push_cast
    linarith
  obtain ⟨_, hlower⟩ := floor_half_lower (show 2 ≤ Real.sqrt w / 2 by linarith)
  refine ⟨v, by dsimp [v]; omega, ?_, ?_⟩
  · have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    have hsquare : (v : ℝ) ^ 2 ≤ (Real.sqrt w / 2 + 1) ^ 2 := by nlinarith
    nlinarith
  · simp only [v, Nat.add_sub_cancel]
    linarith

theorem section16_local_affine_lift_sqrt {N k q r m : Nat} [Fact N.Prime]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width)
    (B D : Finset (Point N (k + 1))) (hD : D ⊆ B)
    (phi : Point N (k + 1) → ZMod N) (gamma s : ℝ)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi) (hs : 1 ≤ s)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hcover : ∀ h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D →
      ∃ i, phi (appendCoordinate h x) = ell h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ)
    (hw : 16 ≤ ((m : ℝ) / 8) ^
      ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧
      (∀ j, (S j).IsProper ∧ Real.sqrt (((m : ℝ) / 8) ^
        ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) / 4 ≤ (S j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ ij, phi z = nu j ij z := by
  obtain ⟨v, hv, hvscale, hvwidth⟩ := section16_lift_width_rounding hw
  obtain ⟨p, G, L, S, nu, hp, hG, hGm, hpart, hproper, hnu, hc⟩ :=
    section16_local_affine_lift P hP hk hm hmP B D hD phi gamma s hsections hs
      ell hell hcover τ ε hq hτ hτ1 hε hε1 hr hv hvscale
  refine ⟨p, G, L, S, nu, hp, hG, hGm, hpart, ?_, hnu, hc⟩
  intro j
  refine ⟨(hproper j).1, hvwidth.trans ?_⟩
  exact_mod_cast (hproper j).2

end LeanProofs.GowersSzemeredi
