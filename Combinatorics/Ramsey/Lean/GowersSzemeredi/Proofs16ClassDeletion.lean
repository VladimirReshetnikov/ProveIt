import GowersSzemeredi.Proofs16WeightedSamplingBudget

/-! # Turning classwise losses into ambient good subsets -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Retain prescribed subclasses of a disjoint family, preserving every
ambient point outside that family. The cardinality loss is controlled by
the sum of the class losses. -/
theorem disjoint_class_deletion {X I : Type*} [DecidableEq X] [Fintype I]
    (S : Finset X) (A D : I → Finset X)
    (hA : ∀ i, A i ⊆ S) (hD : ∀ i, D i ⊆ A i)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∃ E : Finset X, E ⊆ S ∧ (∀ i, E ∩ A i = D i) ∧
      (S.card : ℝ) - ((∑ i, ((A i).card : ℝ)) - ∑ i, ((D i).card : ℝ)) ≤ E.card := by
  let bad := Finset.univ.biUnion (fun i => A i \ D i)
  have hbad : bad ⊆ S := Finset.biUnion_subset.2 fun i _ => Finset.sdiff_subset.trans (hA i)
  refine ⟨S \ bad, Finset.sdiff_subset, fun i => ?_, ?_⟩
  · ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, bad, Finset.mem_biUnion, Finset.mem_univ,
      true_and, not_exists, not_and, not_not]
    refine ⟨fun ⟨⟨_, h⟩, hx⟩ => h i hx, fun hx => ⟨⟨hA i (hD i hx), fun j hj => ?_⟩, hD i hx⟩⟩
    rcases eq_or_ne i j with rfl | hij
    · exact hx
    · exact absurd hj (Finset.disjoint_left.mp (hdisj hij) (hD i hx))
  · have h1 : ((S \ bad).card : ℝ) + bad.card = S.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hbad
    have h2 : (bad.card : ℝ) ≤ ∑ i, ((A i \ D i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : bad.card ≤ ∑ i, (A i \ D i).card)
    have h3 : ∑ i, ((A i \ D i).card : ℝ) + ∑ i, ((D i).card : ℝ) = ∑ i, ((A i).card : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card (hD i)
    linarith

/-- A fibre class viewed as a set of ambient product points. -/
def section16FibreClassSet {α β : Type*} [DecidableEq α] [DecidableEq β]
    (h : β) (C : Finset α) : Finset (β × α) := C.image (fun x => (h, x))

theorem section16FibreClassSet_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (h : β) (C : Finset α) : (section16FibreClassSet h C).card = C.card := by
  apply Finset.card_image_of_injective
  intro x y heq
  exact congrArg Prod.snd heq

theorem section16FibreClassSet_pairwise {α β : Type*} [DecidableEq α] [DecidableEq β]
    {q : Nat} (C : β × Fin q → Finset α)
    (hdisj : ∀ h, Pairwise (fun i j => Disjoint (C (h, i)) (C (h, j)))) :
    Pairwise (fun i j => Disjoint (section16FibreClassSet i.1 (C i))
      (section16FibreClassSet j.1 (C j))) := by
  rintro ⟨h, i⟩ ⟨h', j⟩ hne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hz'
  have hh := congrArg Prod.fst heq
  have hxy := congrArg Prod.snd heq
  dsimp only at hh hxy
  subst h'
  subst y
  exact Finset.disjoint_left.mp (hdisj h (by intro hij; exact hne (by cases hij; rfl))) hx hy

/-- The sum-of-class-sizes estimate yields an actual good product subset,
whose intersection with each original class is exactly its retained class. -/
theorem section16_prune_and_sample_good_set {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
    (q r : Nat) (C : β × Fin q → Finset α) (σ : ℝ) (hq : 0 < q) (hσ : 0 < σ)
    (hlong : 2 * (q : ℝ) ≤ σ * Fintype.card α)
    (hdisj : ∀ h, Pairwise (fun i j => Disjoint (C (h, i)) (C (h, j))))
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ) :
    ∃ (sample : Fin r → α) (E : Finset (β × α)),
      (1 - 2 * σ) * (Fintype.card β : ℝ) * Fintype.card α ≤ E.card ∧
      ∀ h t x, (h, x) ∈ E → x ∈ C (h, t) →
        ∃ i j, sample i ∈ C (h, t) ∧ sample j ∈ C (h, t) ∧
          sample i ≠ sample j ∧ (h, sample i) ∈ E ∧ (h, sample j) ∈ E := by
  let A := fun i : β × Fin q => section16FibreClassSet i.1 (C i)
  obtain ⟨sample, D, hD, hanchors, hloss⟩ :=
    section16_linear_prune_and_sample q r C σ hq hσ hlong hr
  obtain ⟨E, _, hED, hE⟩ := disjoint_class_deletion Finset.univ A
    (fun i => section16FibreClassSet i.1 (D i)) (fun _ => Finset.subset_univ _)
    (fun i => Finset.image_subset_image (hD i)) (section16FibreClassSet_pairwise C hdisj)
  simp only [A, section16FibreClassSet_card, Finset.card_univ, Fintype.card_prod,
    Nat.cast_mul] at hE
  refine ⟨sample, E, by nlinarith [hE, hloss], fun h t x hxE hxC => ?_⟩
  have hiff (y : α) : (h, y) ∈ E ∧ y ∈ C (h, t) ↔ y ∈ D (h, t) := by
    simpa [A, section16FibreClassSet] using Finset.ext_iff.mp (hED (h, t)) (h, y)
  obtain ⟨i, j, hi, hj, hij⟩ := hanchors (h, t) ⟨x, (hiff x).1 ⟨hxE, hxC⟩⟩
  exact ⟨i, j, hD _ hi, hD _ hj, hij, ((hiff _).2 hi).1, ((hiff _).2 hj).1⟩

end LeanProofs.GowersSzemeredi
