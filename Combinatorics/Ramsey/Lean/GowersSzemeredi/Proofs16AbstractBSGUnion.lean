import GowersSzemeredi.Proofs16AbstractBSGDifferences

/-! The union graph of the abstract Balog–Szemerédi–Gowers theorem
(Milićević, arXiv:2601.01682, Theorem 4.1, printed pp. 49–50, property (20)).

`G` is a finite abelian group with no `2`-torsion (`d + d = 0 → d = 0`), as
for `ℤ/N` with `N` odd.
* `exists_antipodal_free_subset`: any finite `D` contains `D′` with
  `0 ∉ D′`, no pair `d, −d`, and `|D| − 1 ≤ 2|D′|`. Ties are broken by a
  fixed enumeration of `G`.
* `diffUnion D′ T`: the pairs `(u + d, u)` for `d ∈ D′`, `u ∈ T d`,
  together with their swaps.
* `diffUnion_same_difference`: if every `T d` is `Q 4`-coherent and `Q 4`
  has symmetry (S2), then any two pairs of the union with the same
  difference are `Q 4`-related. This is property (20).
* `diffUnion_card_ge`: the union has at least `∑_{d∈D′} |T d|` pairs.
* `diffUnion_subset`, `diffUnion_swap`: it lies in `A × A` and is
  symmetric. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **Antipodal-free representatives.** -/
theorem exists_antipodal_free_subset {G : Type*} [AddCommGroup G] [Fintype G]
    (h2 : ∀ d : G, d + d = 0 → d = 0) (D : Finset G) :
    ∃ D' ⊆ D, 0 ∉ D' ∧ (∀ d ∈ D', -d ∉ D') ∧ D.card ≤ 2 * D'.card + 1 := by
  let e := Fintype.equivFin G
  let D' := D.filter fun d => d ≠ 0 ∧ (-d ∉ D ∨ e d < e (-d))
  have hneg_ne : ∀ d : G, d ≠ 0 → -d ≠ d := by
    intro d hd h
    apply hd
    apply h2
    nth_rewrite 1 [← h]
    exact neg_add_cancel d
  refine ⟨D', Finset.filter_subset _ _, fun h => (Finset.mem_filter.mp h).2.1 rfl, ?_, ?_⟩
  · intro d hd hnd
    obtain ⟨hdD, _, hd'⟩ := Finset.mem_filter.mp hd
    obtain ⟨hndD, _, hnd'⟩ := Finset.mem_filter.mp hnd
    rw [neg_neg] at hnd'
    rcases hd' with h | h
    · exact h hndD
    · rcases hnd' with h' | h'
      · exact h' hdD
      · exact absurd (h.trans h') (lt_irrefl _)
  · have hcover : D.erase 0 ⊆ D' ∪ D'.image Neg.neg := by
      intro d hd
      obtain ⟨hd0, hdD⟩ := Finset.mem_erase.mp hd
      by_cases hmem : d ∈ D'
      · exact Finset.mem_union_left _ hmem
      · apply Finset.mem_union_right
        have hnot : ¬ (-d ∉ D ∨ e d < e (-d)) := fun h =>
          hmem (Finset.mem_filter.mpr ⟨hdD, hd0, h⟩)
        push Not at hnot
        obtain ⟨hndD, hle⟩ := hnot
        have hlt : e (-d) < e d := lt_of_le_of_ne hle (fun h => hneg_ne d hd0 (e.injective h))
        refine Finset.mem_image.mpr ⟨-d, Finset.mem_filter.mpr ⟨hndD, neg_ne_zero.mpr hd0,
          Or.inr (by rwa [neg_neg])⟩, neg_neg d⟩
    have h1 : D.card ≤ (D.erase 0).card + 1 := by
      have := Finset.pred_card_le_card_erase (s := D) (a := 0)
      omega
    have h2' := Finset.card_le_card hcover
    have h3 := Finset.card_union_le D' (D'.image Neg.neg)
    have h4 : (D'.image Neg.neg).card ≤ D'.card := Finset.card_image_le
    omega

/-- The pairs `(u + d, u)` for `d ∈ D′` and `u ∈ T d`, with their swaps. -/
def diffUnion {G : Type*} [AddCommGroup G] (D' : Finset G) (T : G → Finset G) :
    Finset (G × G) :=
  let P0 := D'.biUnion fun d => (T d).image fun u => (u + d, u)
  P0 ∪ P0.image Prod.swap

theorem mem_diffUnion {G : Type*} [AddCommGroup G] {D' : Finset G} {T : G → Finset G}
    {p : G × G} :
    p ∈ diffUnion D' T ↔ (∃ d ∈ D', ∃ u ∈ T d, p = (u + d, u)) ∨
      (∃ d ∈ D', ∃ u ∈ T d, p = (u, u + d)) := by
  unfold diffUnion
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro (⟨d, hd, u, hu, rfl⟩ | ⟨q, ⟨d, hd, u, hu, rfl⟩, rfl⟩)
    · exact Or.inl ⟨d, hd, u, hu, rfl⟩
    · exact Or.inr ⟨d, hd, u, hu, rfl⟩
  · rintro (⟨d, hd, u, hu, rfl⟩ | ⟨d, hd, u, hu, rfl⟩)
    · exact Or.inl ⟨d, hd, u, hu, rfl⟩
    · exact Or.inr ⟨(u + d, u), ⟨d, hd, u, hu, rfl⟩, rfl⟩

theorem diffUnion_swap {G : Type*} [AddCommGroup G] {D' : Finset G} {T : G → Finset G}
    {p : G × G} (hp : p ∈ diffUnion D' T) : p.swap ∈ diffUnion D' T := by
  rw [mem_diffUnion] at hp ⊢
  rcases hp with ⟨d, hd, u, hu, rfl⟩ | ⟨d, hd, u, hu, rfl⟩
  · exact Or.inr ⟨d, hd, u, hu, rfl⟩
  · exact Or.inl ⟨d, hd, u, hu, rfl⟩

theorem diffUnion_subset {G : Type*} [AddCommGroup G] {A : Finset G} {D' : Finset G}
    {T : G → Finset G} (hT : ∀ d ∈ D', ∀ u ∈ T d, u ∈ A ∧ u + d ∈ A) :
    diffUnion D' T ⊆ A ×ˢ A := by
  intro p hp
  rw [mem_diffUnion] at hp
  rcases hp with ⟨d, hd, u, hu, rfl⟩ | ⟨d, hd, u, hu, rfl⟩
  · exact Finset.mem_product.mpr ⟨(hT d hd u hu).2, (hT d hd u hu).1⟩
  · exact Finset.mem_product.mpr ⟨(hT d hd u hu).1, (hT d hd u hu).2⟩

/-- **Property (20).** -/
theorem diffUnion_same_difference {G : Type*} [AddCommGroup G] (Q : G → G → G → G → Prop)
    (hS2 : ∀ a₁ a₂ a₃ a₄, Q a₁ a₂ a₃ a₄ → Q a₂ a₁ a₄ a₃)
    {D' : Finset G} (hanti : ∀ d ∈ D', -d ∉ D') {T : G → Finset G}
    (hT : ∀ d ∈ D', ∀ u ∈ T d, ∀ v ∈ T d, Q (u + d) u (v + d) v)
    {p q : G × G} (hp : p ∈ diffUnion D' T) (hq : q ∈ diffUnion D' T)
    (hdiff : p.1 - p.2 = q.1 - q.2) : Q p.1 p.2 q.1 q.2 := by
  rw [mem_diffUnion] at hp hq
  rcases hp with ⟨d, hd, u, hu, rfl⟩ | ⟨d, hd, u, hu, rfl⟩ <;>
    rcases hq with ⟨d', hd', v, hv, rfl⟩ | ⟨d', hd', v, hv, rfl⟩ <;>
    simp only [add_sub_cancel_left, sub_add_cancel_left] at hdiff
  · subst hdiff; exact hT d hd u hu v hv
  · exact absurd (show -d ∈ D' by rw [hdiff, neg_neg]; exact hd') (hanti d hd)
  · exact absurd (show -d ∈ D' by rw [hdiff]; exact hd') (hanti d hd)
  · have hdd : d = d' := neg_inj.mp hdiff
    subst hdd
    exact hS2 _ _ _ _ (hT d hd u hu v hv)

/-- The union has at least `∑_{d∈D′} |T d|` pairs. -/
theorem diffUnion_card_ge {G : Type*} [AddCommGroup G] (D' : Finset G) (T : G → Finset G) :
    ∑ d ∈ D', (T d).card ≤ (diffUnion D' T).card := by
  have hdisj : (D' : Set G).PairwiseDisjoint fun d => (T d).image fun u => (u + d, u) := by
    intro d _ d' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hp'
    simp only [Prod.mk.injEq] at hv
    obtain ⟨h1, h2⟩ := hv
    subst h2
    exact hne (add_left_cancel h1).symm
  calc ∑ d ∈ D', (T d).card = ∑ d ∈ D', ((T d).image fun u => (u + d, u)).card := by
        refine Finset.sum_congr rfl fun d _ => (Finset.card_image_of_injective _ ?_).symm
        intro u v h
        simpa using congrArg Prod.snd h
    _ = (D'.biUnion fun d => (T d).image fun u => (u + d, u)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (diffUnion D' T).card := Finset.card_le_card Finset.subset_union_left

end LeanProofs.GowersSzemeredi
