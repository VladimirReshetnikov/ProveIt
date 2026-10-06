import GowersSzemeredi.Proofs16ShortColumns

/-! # Slice lifting with both short- and long-column recovery

The good subset has the sum of the sampling and base-refinement losses.
The conclusion keeps base cells separate from the final-coordinate set:
it does not silently treat a rectangular product as a common-step box.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem Section16SampledOrAnchoredOn.product_slice_cover {N k r : Nat} [NeZero N]
    {gamma s : ℝ} {B D F : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {sample : Fin r → ZMod N}
    (ha : Section16SampledOrAnchoredOn D phi sample F) (hD : D ⊆ B)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hr : 0 < r) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (T : Box N k) (hT : T.IsProper) (J : Finset (ZMod N))
    (η : ℝ) (hF : F ⊆ lastProductSet T.carrier J)
    (hFm : (1 - η) * ((lastProductSet T.carrier J).card : ℝ) ≤ F.card) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (M : Nat) (Q : Fin M → Box N k)
      (nu : Fin M → ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) →
        Point N (k + 1) → ZMod N),
      G ⊆ F ∧ (1 - η - ε) * ((lastProductSet T.carrier J).card : ℝ) ≤ G.card ∧
      IsBoxPartition Q T ∧ (∀ j, (Q j).IsProper) ∧
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      (∀ j, (T.width : ℝ) ^ ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^
        ((r : ℝ) * s)) ≤ (Q j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j h, h ∈ (Q j).carrier → ∀ x,
        appendCoordinate h x ∈ D → appendCoordinate h x ∈ G →
        ∃ ij, phi (appendCoordinate h x) = nu j ij (appendCoordinate h x) := by
  classical
  obtain ⟨p, H, M, Q, mu, hH, hm, hQ, hproper, hp, hw, hmu, hc⟩ :=
    hsections.common_cover sample hr hs ε hε hε1 T hT
  have hj : ∀ j, ∃ nu : ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) →
      Point N (k + 1) → ZMod N,
      (∀ ij, IsMultilinear (nu ij)) ∧
      ∀ h ∈ H ∩ (Q j).carrier, ∀ x, appendCoordinate h x ∈ D →
        appendCoordinate h x ∈ F → ∃ ij, phi (appendCoordinate h x) = nu ij (appendCoordinate h x) := by
    intro j
    apply ha.multilinear_cover (H ∩ (Q j).carrier) (fun _ => mu j) (fun _ => hmu j)
    intro h hh i hi _
    obtain ⟨hhH, hhQ⟩ := Finset.mem_inter.mp hh
    exact hc j h hhQ hhH i (hD hi)
  choose nu hnu hcov using hj
  have hprod := lastProductSet_good_mass T.carrier H J ε hH hm
  have hmass := good_intersection_mass (lastProductSet T.carrier J) F
    (lastProductSet H J) η ε hF hprod.1 hFm hprod.2
  refine ⟨p, F ∩ lastProductSet H J, M, Q, nu, Finset.inter_subset_left, hmass,
    hQ, hproper, hp, hw, hnu, ?_⟩
  intro j h hhQ x hxD hxG
  obtain ⟨hxF, hxH⟩ := Finset.mem_inter.mp hxG
  have hhH := ((mem_lastProductSet_append H J h x).mp hxH).1
  exact hcov j h (Finset.mem_inter.mpr ⟨hhH, hhQ⟩) x hxD hxF

end LeanProofs.GowersSzemeredi
