import GowersSzemeredi.Proofs16Interpolation

/-! Declarations of `Proofs16Interpolation` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- A fibre with two specified slice values agrees with the corresponding
multilinear interpolant throughout its affine domain. -/
theorem section16TwoAnchorLift_eq {N k : Nat} [Fact N.Prime]
    {A : Finset (ZMod N)} {phi : ZMod N → ZMod N} (hphi : LinearOn A phi)
    {a b x : ZMod N} (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ A) (hab : a ≠ b)
    (h : Point N k) (f g : Point N k → ZMod N)
    (hf : phi a = f h) (hg : phi b = g h) :
    phi x = section16TwoAnchorLift a b f g (appendCoordinate h x) := by
  rw [hphi.two_anchor_interpolation ha hb hx hab, hf, hg]
  simp [section16TwoAnchorLift, appendCoordinate_eq_snoc]

/-- Covers with p and q functions on two slices yield p*q candidate
multilinear functions. The affine domain and endpoint choices may vary
with the base point; the anchors themselves must be distinct. -/
theorem section16TwoAnchorLift_cover {N k p q : Nat} [Fact N.Prime]
    (a b : ZMod N) (hab : a ≠ b)
    (F : Fin p → Point N k → ZMod N) (G : Fin q → Point N k → ZMod N)
    (hF : ∀ i, IsMultilinear (F i)) (hG : ∀ j, IsMultilinear (G j)) :
    ∃ M : (Fin p × Fin q) → Point N (k + 1) → ZMod N,
      (∀ ij, IsMultilinear (M ij)) ∧
      ∀ (h : Point N k) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N),
        LinearOn A phi → a ∈ A → b ∈ A →
        (∃ i, phi a = F i h) → (∃ j, phi b = G j h) →
        ∃ ij, ∀ x ∈ A, phi x = M ij (appendCoordinate h x) := by
  refine ⟨fun ij => section16TwoAnchorLift a b (F ij.1) (G ij.2),
    fun ij => section16TwoAnchorLift_multilinear a b (hF ij.1) (hG ij.2), ?_⟩
  intro h A phi hphi ha hb hf hg
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hj⟩ := hg
  exact ⟨(i, j), fun x hx => section16TwoAnchorLift_eq hphi ha hb hx hab h _ _ hi hj⟩

/-- Simultaneous slice covers lift every anchored affine class. There are
r*r*q*q candidates, independently of the number of affine classes. A
common base domain is required for all slice covers. -/
theorem section16_sampled_slice_cover {N k r s q : Nat} [Fact N.Prime]
    (H : Finset (Point N k)) (anchors : Fin r → ZMod N)
    (A : Point N k → Fin s → Finset (ZMod N))
    (phi : Point N k → ZMod N → ZMod N)
    (F : Fin r → Fin q → Point N k → ZMod N)
    (hF : ∀ i j, IsMultilinear (F i j))
    (hcover : ∀ h ∈ H, ∀ t i, anchors i ∈ A h t →
      ∃ j, phi h (anchors i) = F i j h)
    (haffine : ∀ h ∈ H, ∀ t, LinearOn (A h t) (phi h))
    (hanchors : ∀ h ∈ H, ∀ t, (A h t).Nonempty →
      ∃ i j, anchors i ∈ A h t ∧ anchors j ∈ A h t ∧ anchors i ≠ anchors j) :
    ∃ M : (Fin r × Fin r × Fin q × Fin q) → Point N (k + 1) → ZMod N,
      (∀ ij, IsMultilinear (M ij)) ∧
      ∀ h ∈ H, ∀ t, (A h t).Nonempty →
        ∃ ij, ∀ x ∈ A h t, phi h x = M ij (appendCoordinate h x) := by
  refine ⟨fun ij => section16TwoAnchorLift (anchors ij.1) (anchors ij.2.1)
    (F ij.1 ij.2.2.1) (F ij.2.1 ij.2.2.2), ?_, ?_⟩
  · intro ij
    exact section16TwoAnchorLift_multilinear _ _ (hF _ _) (hF _ _)
  · intro h hh t ht
    obtain ⟨i, j, hi, hj, hij⟩ := hanchors h hh t ht
    obtain ⟨u, hu⟩ := hcover h hh t i hi
    obtain ⟨v, hv⟩ := hcover h hh t j hj
    exact ⟨(i, j, u, v), fun x hx =>
      section16TwoAnchorLift_eq (haffine h hh t) hi hj hx hij h _ _ hu hv⟩

end LeanProofs.GowersSzemeredi
