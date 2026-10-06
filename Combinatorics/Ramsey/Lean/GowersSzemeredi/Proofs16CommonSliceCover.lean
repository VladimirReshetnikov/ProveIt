import GowersSzemeredi.Proofs16AnchoredCover
import GowersSzemeredi.Proofs16BaseCaseUnion

/-! # A common base partition for the sampled cross-sections

The existing finite-union theorem supplies a single partition and a common
pool of slice candidates. The interpolation step then uses that partition
once. The resulting objects here are base boxes; synchronizing their steps
with the final coordinate remains a separate geometric obligation.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem FinalCoordinateSectionsMultiplyLinear.common_cover {N k r : Nat} [NeZero N]
    {gamma s : ℝ} {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (sample : Fin r → ZMod N) (hr : 0 < r) (hs : 1 ≤ s)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (T : Box N k) (hT : T.IsProper) :
    ∃ (p : Nat) (H : Finset (Point N k)) (M : Nat) (Q : Fin M → Box N k)
      (mu : Fin M → Fin p → Point N k → ZMod N),
      H ⊆ T.carrier ∧ (1 - ε) * (T.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q T ∧ (∀ j, (Q j).IsProper) ∧
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      (∀ j, (T.width : ℝ) ^ ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^
        ((r : ℝ) * s)) ≤ (Q j).width) ∧
      (∀ j u, IsMultilinear (mu j u)) ∧
      ∀ j h, h ∈ (Q j).carrier → h ∈ H → ∀ i,
        appendCoordinate h (sample i) ∈ B →
        ∃ u, phi (appendCoordinate h (sample i)) = mu j u h := by
  classical
  let Gamma := fun i : Fin r => partialGraph (section16FinalCoordinateSection B (sample i))
    (section16FinalCoordinateRestriction phi (sample i))
  have hGamma : ∀ i, ProperMultiplyLinear gamma s (Gamma i) := fun i => hsections (sample i)
  have hML := BaseCase.properMultiplyLinear_finsetUnion gamma s hs Gamma hr hGamma
  obtain ⟨M, p, H, Q, mu, hH, hm, hQ, hproper, hp, hw, hmu, hc⟩ := hML ε hε hε1 T hT
  refine ⟨p, H, M, Q, mu, hH, hm, hQ, hproper, hp, hw, hmu, ?_⟩
  intro j h hj hh i hB
  apply hc j h hj hh (phi (appendCoordinate h (sample i)))
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨h, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩

/-- The common slice partition and the anchor identity give a multilinear
cover on each refined base cell, retaining the explicit base width and
candidate bounds. No assertion about synchronized product-box widths is
implicit in this conclusion. -/
theorem Section16AnchoredOn.common_slice_cover {N k r : Nat} [NeZero N]
    {gamma s : ℝ} {B D F : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {sample : Fin r → ZMod N}
    (ha : Section16AnchoredOn D phi sample F) (hD : D ⊆ B)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hr : 0 < r) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (T : Box N k) (hT : T.IsProper) :
    ∃ (p : Nat) (H : Finset (Point N k)) (M : Nat) (Q : Fin M → Box N k)
      (nu : Fin M → (Fin r × Fin r × Fin p × Fin p) → Point N (k + 1) → ZMod N),
      H ⊆ T.carrier ∧ (1 - ε) * (T.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q T ∧ (∀ j, (Q j).IsProper) ∧
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      (∀ j, (T.width : ℝ) ^ ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^
        ((r : ℝ) * s)) ≤ (Q j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j h, h ∈ (Q j).carrier → h ∈ H → ∀ x,
        appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
        ∃ ij, phi (appendCoordinate h x) = nu j ij (appendCoordinate h x) := by
  classical
  obtain ⟨p, H, M, Q, mu, hH, hm, hQ, hproper, hp, hw, hmu, hc⟩ :=
    hsections.common_cover sample hr hs ε hε hε1 T hT
  have hj : ∀ j, ∃ nu : (Fin r × Fin r × Fin p × Fin p) → Point N (k + 1) → ZMod N,
      (∀ ij, IsMultilinear (nu ij)) ∧
      ∀ h ∈ H ∩ (Q j).carrier, ∀ x, appendCoordinate h x ∈ D →
        appendCoordinate h x ∈ F → ∃ ij, phi (appendCoordinate h x) = nu ij (appendCoordinate h x) := by
    intro j
    apply ha.multilinear_cover (H ∩ (Q j).carrier) (fun _ => mu j) (fun _ => hmu j)
    intro h hh i hi _
    obtain ⟨hhH, hhQ⟩ := Finset.mem_inter.mp hh
    exact hc j h hhQ hhH i (hD hi)
  choose nu hnu hcov using hj
  refine ⟨p, H, M, Q, nu, hH, hm, hQ, hproper, hp, hw, hnu, ?_⟩
  intro j h hhQ hhH x hxD hxF
  exact hcov j h (Finset.mem_inter.mpr ⟨hhH, hhQ⟩) x hxD hxF

end LeanProofs.GowersSzemeredi
