import GowersSzemeredi.Proofs16ProductAnchors

/-! # Anchored interpolation on the cells of a Section 16 line cover -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Each surviving domain point is interpolated from two distinct sampled
columns, with both anchors in the domain and in the surviving set. -/
def Section16AnchoredOn {N k r : Nat}
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))) : Prop :=
  ∀ h x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
    ∃ i j, appendCoordinate h (sample i) ∈ D ∧ appendCoordinate h (sample j) ∈ D ∧
      appendCoordinate h (sample i) ∈ F ∧ appendCoordinate h (sample j) ∈ F ∧
      sample i ≠ sample j ∧
      phi (appendCoordinate h x) = (sample i - sample j)⁻¹ *
        ((phi (appendCoordinate h (sample i)) + (-1) * phi (appendCoordinate h (sample j))) * x +
          ((-sample j) * phi (appendCoordinate h (sample i)) +
            sample i * phi (appendCoordinate h (sample j))))

theorem section16_box_anchored_good_set {N k q r : Nat} [Fact N.Prime]
    (S : Box N (k + 1)) (T : Box N k) (J : ModAP N)
    (hprod : IsLastCoordinateBoxProduct S T J)
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h ∈ T.carrier, ∀ t, LinearOn Finset.univ (ell h t))
    (hcover : ∀ h ∈ T.carrier, ∀ x ∈ J.carrier, appendCoordinate h x ∈ D →
      ∃ t, phi (appendCoordinate h x) = ell h t x)
    (τ : ℝ) (hq : 0 < q) (hτ : 0 < τ)
    (hlong : 2 * (q : ℝ) ≤ τ * J.carrier.card)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ ^ 2) :
    ∃ (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))),
      (∀ i, sample i ∈ J.carrier) ∧ F ⊆ S.carrier ∧
      (1 - 2 * τ) * (S.carrier.card : ℝ) ≤ F.card ∧ Section16AnchoredOn D phi sample F := by
  have hc : S.carrier = lastProductSet T.carrier J.carrier := hprod.1
  obtain ⟨sample, F, hs, hF, hm, ha⟩ := section16_product_anchored_good_set
    T.carrier J.carrier D phi ell hell hcover τ hq hτ hlong hr
  exact ⟨sample, F, hs, hc ▸ hF, hc ▸ hm, ha⟩

/-- Lemma 16.9's partition carries a common anchor sample and a good set
on every sufficiently long final-coordinate cell. The original exceptional
set E is retained in the interpolation domain B1 intersect E. -/
theorem Section16LineCover.anchored_cells {N k q r : Nat} [Fact N.Prime]
    {P : Box N (k + 1)} {B1 : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {σ l : ℝ}
    (hline : Section16LineCover P B1 phi σ l q)
    (τ : ℝ) (hq : 0 < q) (hτ : 0 < τ)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ ^ 2) :
    ∃ (E : Finset (Point N (k + 1))) (M : Nat)
      (S : Fin M → Box N (k + 1)) (T : Fin M → Box N k) (J : Fin M → ModAP N),
      E ⊆ P.carrier ∧ (1 - σ) * (P.carrier.card : ℝ) ≤ E.card ∧
      IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
      (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (J u)) ∧
      (∀ u, l ≤ (S u).width) ∧
      ∀ u, 2 * (q : ℝ) ≤ τ * (J u).carrier.card →
        ∃ (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))),
          (∀ i, sample i ∈ (J u).carrier) ∧ F ⊆ (S u).carrier ∧
          (1 - 2 * τ) * ((S u).carrier.card : ℝ) ≤ F.card ∧
          Section16AnchoredOn (B1 ∩ E) phi sample F := by
  classical
  obtain ⟨E, M, S, T, J, ell, hE, hm, hp, hproper, hprod, hw, hell, hc⟩ := hline
  refine ⟨E, M, S, T, J, hE, hm, hp, hproper, hprod, hw, ?_⟩
  intro u hlong
  apply section16_box_anchored_good_set (S u) (T u) (J u) (hprod u)
    (B1 ∩ E) phi (ell u) (fun h _ t => hell u h t) ?_ τ hq hτ hlong hr
  intro h hh x hx hz
  obtain ⟨hB, hE⟩ := Finset.mem_inter.mp hz
  apply hc u h x hh hB hE
  rw [appendCoordinate_eq_snoc]
  exact ((hprod u).mem_snoc h x).mpr ⟨hh, hx⟩

/-- On a common good base domain, slice covers supply a simultaneous
multilinear cover of every point certified by the anchor identity. -/
theorem Section16AnchoredOn.multilinear_cover {N k r p : Nat} [NeZero N]
    {D F : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {sample : Fin r → ZMod N} (ha : Section16AnchoredOn D phi sample F)
    (H : Finset (Point N k)) (mu : Fin r → Fin p → Point N k → ZMod N)
    (hmu : ∀ i j, IsMultilinear (mu i j))
    (hcover : ∀ h ∈ H, ∀ i, appendCoordinate h (sample i) ∈ D →
      appendCoordinate h (sample i) ∈ F →
      ∃ j, phi (appendCoordinate h (sample i)) = mu i j h) :
    ∃ M : (Fin r × Fin r × Fin p × Fin p) → Point N (k + 1) → ZMod N,
      (∀ ij, IsMultilinear (M ij)) ∧
      ∀ h ∈ H, ∀ x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
        ∃ ij, phi (appendCoordinate h x) = M ij (appendCoordinate h x) := by
  refine ⟨fun ij => section16TwoAnchorLift (sample ij.1) (sample ij.2.1)
    (mu ij.1 ij.2.2.1) (mu ij.2.1 ij.2.2.2),
    fun ij => section16TwoAnchorLift_multilinear _ _ (hmu _ _) (hmu _ _), ?_⟩
  intro h hh x hxD hxF
  obtain ⟨i, j, hiD, hjD, hiF, hjF, _, heq⟩ := ha h x hxD hxF
  obtain ⟨u, hu⟩ := hcover h hh i hiD hiF
  obtain ⟨v, hv⟩ := hcover h hh j hjD hjF
  refine ⟨(i, j, u, v), ?_⟩
  rw [heq, hu, hv]
  simp [section16TwoAnchorLift, appendCoordinate_eq_snoc]

end LeanProofs.GowersSzemeredi
