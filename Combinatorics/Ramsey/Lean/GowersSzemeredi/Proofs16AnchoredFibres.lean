import GowersSzemeredi.Proofs16AffineClasses

/-! # From affine graph covers to a common anchored good set

This is the pruning-and-sampling part of Lemma 16.10, with the repaired
sampling budget and explicit long-column hypothesis. The final comparison
with the prescribed MultiplyLinear controls is not asserted here.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_affine_cover_anchored_good_set {N q r : Nat} [Fact N.Prime]
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (coord : α → ZMod N) (hinj : Function.Injective coord)
    (B : β → Finset α) (f : β → α → ZMod N)
    (ell : β → Fin q → ZMod N → ZMod N)
    (hell : ∀ h t, LinearOn Finset.univ (ell h t))
    (hcover : ∀ h x, x ∈ B h → ∃ t, f h x = ell h t (coord x))
    (σ : ℝ) (hq : 0 < q) (hσ : 0 < σ)
    (hlong : 2 * (q : ℝ) ≤ σ * Fintype.card α)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ) :
    ∃ (sample : Fin r → α) (E : Finset (β × α)),
      (1 - 2 * σ) * (Fintype.card β : ℝ) * Fintype.card α ≤ E.card ∧
      ∀ h x, (h, x) ∈ E → x ∈ B h →
        ∃ i j, sample i ∈ B h ∧ sample j ∈ B h ∧
          (h, sample i) ∈ E ∧ (h, sample j) ∈ E ∧ coord (sample i) ≠ coord (sample j) ∧
          f h x = (coord (sample i) - coord (sample j))⁻¹ *
            ((f h (sample i) + (-1) * f h (sample j)) * coord x +
              ((-coord (sample j)) * f h (sample i) + coord (sample i) * f h (sample j))) := by
  classical
  choose C hpart hC using fun h =>
    affine_column_cover_partition coord hq (B h) (f h) (ell h) (hell h) (hcover h)
  have hdisj : ∀ h, Pairwise (fun i j => Disjoint (C h i) (C h j)) := by
    intro h i j hij
    exact (hpart h).2 i j (bne_iff_ne.mpr hij)
  obtain ⟨sample, E, hmass, hanchors⟩ := section16_prune_and_sample_good_set
    q r (fun i => C i.1 i.2) σ hq hσ hlong hdisj hr
  refine ⟨sample, E, hmass, ?_⟩
  intro h x hxE hxB
  obtain ⟨t, hxt⟩ := ((hpart h).1 x).mp hxB
  obtain ⟨i, j, hi, hj, hij, hiE, hjE⟩ := hanchors h t x hxE hxt
  have hij' : coord (sample i) ≠ coord (sample j) := fun heq => hij (hinj heq)
  refine ⟨i, j, ((hpart h).1 _).mpr ⟨t, hi⟩, ((hpart h).1 _).mpr ⟨t, hj⟩,
    hiE, hjE, hij', ?_⟩
  obtain ⟨a, b, hab⟩ := hC h t
  have hlin : LinearOn Finset.univ (fun z : ZMod N => a * z + b) :=
    ⟨a, b, fun _ _ => rfl⟩
  have heq := hlin.two_anchor_interpolation
    (Finset.mem_univ (coord (sample i))) (Finset.mem_univ (coord (sample j)))
    (Finset.mem_univ (coord x)) hij'
  rw [hab x hxt, hab (sample i) hi, hab (sample j) hj]
  exact heq

end LeanProofs.GowersSzemeredi
