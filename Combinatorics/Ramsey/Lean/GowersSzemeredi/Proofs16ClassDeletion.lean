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
  classical
  let bad := Finset.univ.biUnion (fun i => A i \ D i)
  have hbad : bad ⊆ S := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hA i (Finset.mem_sdiff.mp hi).1
  have hcard := Finset.card_le_card hbad
  have hDgood : ∀ i, D i ⊆ S \ bad := by
    intro i x hx
    refine Finset.mem_sdiff.mpr ⟨hA i (hD i hx), ?_⟩
    intro hxbad
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hxbad
    obtain ⟨hja, hjd⟩ := Finset.mem_sdiff.mp hj
    by_cases hij : i = j
    · subst j
      exact hjd hx
    · exact Finset.disjoint_left.mp (hdisj hij) (hD i hx) hja
  refine ⟨S \ bad, Finset.sdiff_subset, ?_, ?_⟩
  · intro i
    ext x
    constructor
    · intro hx
      obtain ⟨hxE, hxA⟩ := Finset.mem_inter.mp hx
      by_contra hxD
      exact (Finset.mem_sdiff.mp hxE).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hxA, hxD⟩⟩)
    · intro hx
      exact Finset.mem_inter.mpr ⟨hDgood i hx, hD i hx⟩
  · have hsum : (bad.card : ℝ) ≤
        (∑ i, ((A i).card : ℝ)) - ∑ i, ((D i).card : ℝ) := by
      calc
        _ ≤ ∑ i, ((A i \ D i).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le : bad.card ≤ ∑ i, (A i \ D i).card)
        _ = _ := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.card_sdiff_of_subset (hD i), Nat.cast_sub (Finset.card_le_card (hD i))]
    rw [Finset.card_sdiff_of_subset hbad, Nat.cast_sub hcard]
    linarith

/-- A fibre class viewed as a set of ambient product points. -/
def section16FibreClassSet {α β : Type*} [DecidableEq α] [DecidableEq β]
    (h : β) (C : Finset α) : Finset (β × α) := C.image (fun x => (h, x))

theorem section16FibreClassSet_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (h : β) (C : Finset α) : (section16FibreClassSet h C).card = C.card := by
  apply Finset.card_image_of_injective
  intro x y heq
  exact congrArg Prod.snd heq

theorem section16FibreClassSet_mono {α β : Type*} [DecidableEq α] [DecidableEq β]
    (h : β) {C D : Finset α} (hsub : C ⊆ D) :
    section16FibreClassSet h C ⊆ section16FibreClassSet h D := Finset.image_subset_image hsub

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
  classical
  let A := fun i : β × Fin q => section16FibreClassSet i.1 (C i)
  have hAdisj := section16FibreClassSet_pairwise C hdisj
  obtain ⟨sample, D, hD, hanchors, hloss⟩ :=
    section16_linear_prune_and_sample q r C σ hq hσ hlong hr
  obtain ⟨E, _, hED, hE⟩ := disjoint_class_deletion Finset.univ A
    (fun i => section16FibreClassSet i.1 (D i)) (fun _ => Finset.subset_univ _)
    (fun i => section16FibreClassSet_mono _ (hD i)) hAdisj
  simp only [A, section16FibreClassSet_card, Finset.card_univ, Fintype.card_prod,
    Nat.cast_mul] at hE
  refine ⟨sample, E, by nlinarith [hE, hloss], ?_⟩
  intro h t x hxE hxC
  have hxA : (h, x) ∈ A (h, t) := Finset.mem_image.mpr ⟨x, hxC, rfl⟩
  have hxD : x ∈ D (h, t) := by
    have hp := Finset.mem_inter.mpr ⟨hxE, hxA⟩
    rw [hED (h, t)] at hp
    simpa [section16FibreClassSet] using hp
  obtain ⟨i, j, hi, hj, hij⟩ := hanchors (h, t) ⟨x, hxD⟩
  have hmem : ∀ y ∈ D (h, t), (h, y) ∈ E := by
    intro y hy
    have hp : (h, y) ∈ section16FibreClassSet h (D (h, t)) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    rw [← hED (h, t)] at hp
    exact (Finset.mem_inter.mp hp).1
  exact ⟨i, j, hD _ hi, hD _ hj, hij, hmem _ hi, hmem _ hj⟩

end LeanProofs.GowersSzemeredi
