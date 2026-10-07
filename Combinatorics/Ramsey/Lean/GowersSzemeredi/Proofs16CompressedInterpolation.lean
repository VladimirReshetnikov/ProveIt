import GowersSzemeredi.Proofs16ShortColumns

/-! Unordered two-anchor interpolants already cover directly sampled points.
Repeated sample values are allowed. If all values coincide, one slice list
suffices. This implements the affine case of the incoming exact-local-
profiles interpolation argument without assuming sampling without replacement. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

abbrev Section16AnchorPair (r : Nat) := (j : Fin r) × Fin j.val

theorem section16AnchorPair_card (r : Nat) : Fintype.card (Section16AnchorPair r) = r.choose 2 := by
  simp only [Section16AnchorPair, Fintype.card_sigma, Fintype.card_fin]
  induction r with
  | zero => simp
  | succ r ih => simpa [Fin.sum_univ_castSucc, Nat.choose_succ_succ, Nat.add_comm] using congrArg (· + r) ih

def section16CompressedCandidateCount (r p : Nat) : Nat := max p (r.choose 2 * p * p)

theorem section16TwoAnchorLift_left {N k : Nat} [Fact N.Prime]
    {a b : ZMod N} (hab : a ≠ b) (f g : Point N k → ZMod N) (h : Point N k) :
    section16TwoAnchorLift a b f g (appendCoordinate h a) = f h := by
  simp only [section16TwoAnchorLift, appendCoordinate_eq_snoc, Fin.init_snoc, Fin.snoc_last]
  have hne := sub_ne_zero.mpr hab
  field_simp
  ring

theorem section16TwoAnchorLift_swap {N k : Nat} [Fact N.Prime]
    {a b : ZMod N} (hab : a ≠ b) (f g : Point N k → ZMod N) :
    section16TwoAnchorLift a b f g = section16TwoAnchorLift b a g f := by
  funext z
  have hne := sub_ne_zero.mpr hab
  have hne' := sub_ne_zero.mpr hab.symm
  unfold section16TwoAnchorLift
  field_simp
  ring

/-- An unordered index family includes every distinct-anchor interpolant. -/
theorem section16_sorted_interpolant {N k r p : Nat} [Fact N.Prime]
    (sample : Fin r → ZMod N) (mu : Fin r → Fin p → Point N k → ZMod N)
    {i j : Fin r} (hij : sample i ≠ sample j) (u v : Fin p) :
    ∃ c : Section16AnchorPair r × Fin p × Fin p,
      section16TwoAnchorLift (sample i) (sample j) (mu i u) (mu j v) =
        section16TwoAnchorLift (sample ⟨c.1.2.val, c.1.2.isLt.trans c.1.1.isLt⟩)
          (sample c.1.1) (mu ⟨c.1.2.val, c.1.2.isLt.trans c.1.1.isLt⟩ c.2.1) (mu c.1.1 c.2.2) := by
  have hne : i ≠ j := fun h => hij (congrArg sample h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨(⟨j, ⟨i.val, hlt⟩⟩, u, v), rfl⟩
  · exact ⟨(⟨i, ⟨j.val, hgt⟩⟩, v, u), section16TwoAnchorLift_swap hij _ _⟩

/-- A sample of r possibly repeated anchors needs at most
max(p, choose(r,2)*p^2) candidates. No direct-anchor summand is needed.
Empty slice lists cause no difficulty: then there are no certified points. -/
theorem Section16SampledOrAnchoredOn.compressed_multilinear_cover {N k r p : Nat} [Fact N.Prime]
    {D F : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {sample : Fin r → ZMod N} (ha : Section16SampledOrAnchoredOn D phi sample F) (hr : 0 < r)
    (H : Finset (Point N k)) (mu : Fin r → Fin p → Point N k → ZMod N)
    (hmu : ∀ i j, IsMultilinear (mu i j))
    (hcover : ∀ h ∈ H, ∀ i, appendCoordinate h (sample i) ∈ D →
      appendCoordinate h (sample i) ∈ F → ∃ j, phi (appendCoordinate h (sample i)) = mu i j h) :
    ∃ M : Fin (section16CompressedCandidateCount r p) → Point N (k + 1) → ZMod N,
      (∀ c, IsMultilinear (M c)) ∧
      ∀ h ∈ H, ∀ x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
        ∃ c, phi (appendCoordinate h x) = M c (appendCoordinate h x) := by
  classical
  obtain ⟨K, hK, hanchor, hrecovered⟩ := ha
  by_cases hdistinct : ∃ i j, sample i ≠ sample j
  · let C := Section16AnchorPair r × Fin p × Fin p
    let raw : C → Point N (k + 1) → ZMod N := fun c =>
      section16TwoAnchorLift (sample ⟨c.1.2.val, c.1.2.isLt.trans c.1.1.isLt⟩)
        (sample c.1.1) (mu ⟨c.1.2.val, c.1.2.isLt.trans c.1.1.isLt⟩ c.2.1) (mu c.1.1 c.2.2)
    have hraw : ∀ c, IsMultilinear (raw c) := fun c => section16TwoAnchorLift_multilinear _ _ (hmu _ _) (hmu _ _)
    have hcount : Fintype.card C ≤ section16CompressedCandidateCount r p := by
      dsimp only [C]
      rw [Fintype.card_prod, Fintype.card_prod, section16AnchorPair_card, Fintype.card_fin]
      simpa only [section16CompressedCandidateCount, mul_assoc] using (le_max_right p (r.choose 2 * p * p))
    let family := fun i => raw ((Fintype.equivFin C).symm i)
    refine ⟨padMultilinearFamily family _, padMultilinearFamily_isMultilinear _ (fun _ => hraw _), ?_⟩
    intro h hh x hxD hxF
    have hex : ∃ c : C, phi (appendCoordinate h x) = raw c (appendCoordinate h x) := by
      rcases hrecovered h x hxD hxF with hxK | ⟨i, rfl⟩
      · obtain ⟨i, j, hiD, hjD, hiK, hjK, hij, heq⟩ := hanchor h x hxD hxK
        obtain ⟨u, hu⟩ := hcover h hh i hiD (hK hiK)
        obtain ⟨v, hv⟩ := hcover h hh j hjD (hK hjK)
        obtain ⟨c, hc⟩ := section16_sorted_interpolant sample mu hij u v
        refine ⟨c, ?_⟩
        rw [heq, hu, hv]
        simpa only [raw, section16TwoAnchorLift, appendCoordinate_eq_snoc, Fin.init_snoc, Fin.snoc_last]
          using congrFun hc (appendCoordinate h x)
      · obtain ⟨u, hu⟩ := hcover h hh i hxD hxF
        obtain ⟨j, hij⟩ : ∃ j, sample i ≠ sample j := by
          obtain ⟨a, b, hab⟩ := hdistinct
          by_cases hi : sample i = sample a
          · exact ⟨b, hi ▸ hab⟩
          · exact ⟨a, hi⟩
        obtain ⟨c, hc⟩ := section16_sorted_interpolant sample mu hij u u
        exact ⟨c, hu.trans ((section16TwoAnchorLift_left hij _ _ h).symm.trans (congrFun hc _))⟩
    apply padMultilinearFamily_covers _ hcount _ _
    obtain ⟨c, hc⟩ := hex
    exact ⟨(Fintype.equivFin C) c, by simpa [family] using hc⟩
  · let i0 : Fin r := ⟨0, hr⟩
    have heq (i : Fin r) : sample i = sample i0 := by
      by_contra hne
      exact hdistinct ⟨i, i0, hne⟩
    let family : Fin p → Point N (k + 1) → ZMod N := fun u z => mu i0 u (Fin.init z)
    refine ⟨padMultilinearFamily family _, padMultilinearFamily_isMultilinear _
      (fun u => (hmu i0 u).lift_last), ?_⟩
    intro h hh x hxD hxF
    rcases hrecovered h x hxD hxF with hxK | ⟨i, rfl⟩
    · obtain ⟨i, j, _, _, _, _, hij, _⟩ := hanchor h x hxD hxK
      exact (hij ((heq i).trans (heq j).symm)).elim
    · rw [heq i] at hxD hxF ⊢
      obtain ⟨u, hu⟩ := hcover h hh i0 hxD hxF
      apply padMultilinearFamily_covers _ (le_max_left _ _) _ _
      exact ⟨u, by simpa [family, appendCoordinate_eq_snoc] using hu⟩

end LeanProofs.GowersSzemeredi
