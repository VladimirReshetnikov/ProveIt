import GowersSzemeredi.Proofs16GlobalCoverProviders

/-! Declarations of `Proofs16GlobalCoverProviders` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Classical

/-- **A function cover on a good set gives a piece provider there.** -/
theorem MultiplyLinearWith.localPieceFor {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {B J : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (restrictRelation (partialGraph B phi) J))
    (hQb : ∀ s, 0 < s → s ≤ 1 → 1 ≤ Qb s) (hEb : ∀ s, 0 < s → s ≤ 1 → 0 < Eb s) :
    LocalPieceFor (fun theta => theta / 2 / Qb (theta / 2)) (coverWidth Eb) (B ∩ J) phi := by
  intro theta hθ hθ1 P H hP hHP hHD hHc
  have hcov := hML.localRelationCoverFor hEb
  obtain ⟨R, G, q, mu, hR, hRP, hRw, hGH, hGR, hGc, hq, hmu, hGcov⟩ :=
    hcov theta hθ hθ1 P H hP hHP (fun x hx => (Finset.mem_inter.mp (hHD hx)).2) hHc
  have hQpos : (0 : Real) < Qb (theta / 2) :=
    lt_of_lt_of_le one_pos (hQb _ (by positivity) (by linarith))
  -- every point of `G` lies on one of the `q` graphs
  have hcov' : ∀ h ∈ G, ∃ i, phi h = mu i h := fun h hh =>
    hGcov h hh (phi h) (Finset.mem_image.mpr ⟨h, (Finset.mem_inter.mp (hHD (hGH hh))).1, rfl⟩)
  have hsum : (G.card : Real) ≤ ∑ i, ((G.filter fun h => phi h = mu i h).card : Real) := by
    have hsub : G ⊆ Finset.univ.biUnion fun i => G.filter fun h => phi h = mu i h := by
      intro h hh
      obtain ⟨i, hi⟩ := hcov' h hh
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hh, hi⟩⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have hG0 : (G.card : Real) ≤ 0 := by simpa using hsum
    refine ⟨R, fun _ => 0, hR, hRP, hRw, ⟨fun _ => 0, fun x => by simp⟩, ?_⟩
    have : theta / 2 * R.carrier.card ≤ 0 := hGc.trans hG0
    calc theta / 2 / Qb (theta / 2) * R.carrier.card =
        (theta / 2 * R.carrier.card) / Qb (theta / 2) := by ring
      _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hQpos.le
      _ ≤ _ := Nat.cast_nonneg _
  · have hqR : (0 : Real) < q := by exact_mod_cast hq0
    have hne : (Finset.univ : Finset (Fin q)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hq0⟩⟩
    have hle : ∑ _i : Fin q, (G.card : Real) / q ≤
        ∑ i, ((G.filter fun h => phi h = mu i h).card : Real) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ hqR.ne']
      exact hsum
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hle
    refine ⟨R, mu i, hR, hRP, hRw, hmu i, ?_⟩
    have hsub : (G.filter fun h => phi h = mu i h) ⊆
        H.filter fun x => x ∈ R.carrier ∧ phi x = mu i x := fun h hh => by
      obtain ⟨hhG, he⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨hGH hhG, hGR hhG, he⟩
    calc theta / 2 / Qb (theta / 2) * R.carrier.card ≤ (G.card : Real) / Qb (theta / 2) := by
          rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hGc hQpos.le
      _ ≤ (G.card : Real) / q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqR hq
      _ ≤ _ := hi.trans (by exact_mod_cast Finset.card_le_card hsub)

end

end LeanProofs.GowersSzemeredi
