import GowersSzemeredi.Proofs16PropNineThreeGlue

/-! Good pairs for the Proposition 9.3 assembly (J.5c).

`Comp x z a` says the quadruple `(x+a, x, z+a, z)` is compatible. A column
`x` is *well connected* for `a` (`x ∈ wellConnected Comp a`) when it is
compatible with at least `N/2` of the `z`'s. This is Milićević's set `X_a`,
and it powers "relating back". A pair `(x, y)` is *good* for `a` when it is
compatible, not a bad triple, and both columns are well connected.
* `wellConnected_compl_card_le`: if at most `ε₁N³` triples are incompatible,
  at most `2ε₁N³` triples `(x, y, a)` have `x` badly connected (and likewise
  `y`).
* `good_triples_card_ge`: with fewer than `εN³` bad triples, at least
  `(1 − 5ε₁ − ε)N³` triples are good.
* `good_pair_fibers_sum_ge`: the same, as a sum over `a` of the number of good
  pairs, which is the form `markov_large_fibers` takes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

variable {N : Nat} [NeZero N]

/-- The columns compatible with at least half of all columns, for fixed `a`. -/
def wellConnected (Comp : ZMod N → ZMod N → ZMod N → Prop) (a : ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter fun x => (N : Real) / 2 ≤ (Finset.univ.filter fun z => Comp x z a).card

/-- The incompatible triples `(x, z, a)`. -/
def incompatibleTriples (Comp : ZMod N → ZMod N → ZMod N → Prop) :
    Finset (ZMod N × ZMod N × ZMod N) :=
  Finset.univ.filter fun t => ¬ Comp t.1 t.2.1 t.2.2

/-- The badly connected pairs `(x, a)`. -/
def badlyConnected (Comp : ZMod N → ZMod N → ZMod N → Prop) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => p.1 ∉ wellConnected Comp p.2

theorem badlyConnected_card_le (Comp : ZMod N → ZMod N → ZMod N → Prop) :
    (N : Real) / 2 * (badlyConnected Comp).card ≤ (incompatibleTriples Comp).card := by
  -- fibre the incompatible triples over `(x, a)`
  have hmaps : ∀ t ∈ incompatibleTriples Comp, (t.1, t.2.2) ∈ (Finset.univ : Finset _) :=
    fun _ _ => Finset.mem_univ _
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun t : ZMod N × ZMod N × ZMod N =>
    (t.1, t.2.2)) hmaps
  have hfib : ∀ p ∈ badlyConnected Comp, (N : Real) / 2 ≤
      (((incompatibleTriples Comp).filter fun t => (t.1, t.2.2) = p).card : Real) := by
    intro p hp
    have hnot := (Finset.mem_filter.mp hp).2
    simp only [wellConnected, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
    -- the incompatible `z` for `p`
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod N)))
      (fun z => Comp p.1 z p.2)
    rw [Finset.card_univ, ZMod.card] at hsplit
    have hinc : (Finset.univ.filter fun z => ¬ Comp p.1 z p.2).card ≤
        ((incompatibleTriples Comp).filter fun t => (t.1, t.2.2) = p).card := by
      refine Finset.card_le_card_of_injOn (fun z => (p.1, z, p.2)) ?_ ?_
      · intro z hz
        have hz' := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
        have hmem : (p.1, z, p.2) ∈ (incompatibleTriples Comp).filter
            fun t => (t.1, t.2.2) = p :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz'⟩, rfl⟩
        first | exact hmem | exact Finset.mem_coe.mpr hmem
      · intro z _ z' _ h
        simp only [Prod.mk.injEq] at h
        exact h.2.1
    have h1 : ((Finset.univ.filter fun z => Comp p.1 z p.2).card : Real) +
        (Finset.univ.filter fun z => ¬ Comp p.1 z p.2).card = N := by exact_mod_cast hsplit
    have h2 : ((Finset.univ.filter fun z => ¬ Comp p.1 z p.2).card : Real) ≤
        (((incompatibleTriples Comp).filter fun t => (t.1, t.2.2) = p).card : Real) := by
      exact_mod_cast hinc
    linarith
  calc (N : Real) / 2 * (badlyConnected Comp).card = ∑ _p ∈ badlyConnected Comp, (N : Real) / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ p ∈ badlyConnected Comp,
          (((incompatibleTriples Comp).filter fun t => (t.1, t.2.2) = p).card : Real) :=
        Finset.sum_le_sum hfib
    _ ≤ ∑ p : ZMod N × ZMod N,
          (((incompatibleTriples Comp).filter fun t => (t.1, t.2.2) = p).card : Real) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.cast_nonneg _
    _ = (incompatibleTriples Comp).card := by rw [hsum]; push_cast; rfl

/-- Triples whose first or second column is badly connected. -/
theorem wellConnected_compl_card_le (Comp : ZMod N → ZMod N → ZMod N → Prop) {ε₁ : Real}
    (h : ((incompatibleTriples Comp).card : Real) ≤ ε₁ * (N : Real) ^ 3) (sel : Bool) :
    ((Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N =>
        (if sel then t.1 else t.2.1) ∉ wellConnected Comp t.2.2).card : Real) ≤
      2 * ε₁ * (N : Real) ^ 3 := by
  have hN : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hbc := badlyConnected_card_le Comp
  -- each badly connected pair gives `N` triples
  have hcount : (Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N =>
      (if sel then t.1 else t.2.1) ∉ wellConnected Comp t.2.2).card =
      ((Finset.univ : Finset (ZMod N)) ×ˢ badlyConnected Comp).card := by
    refine Finset.card_bij (fun t _ => (if sel then t.2.1 else t.1, (if sel then t.1 else t.2.1),
      t.2.2)) ?_ ?_ ?_
    · intro t ht
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
    · intro t _ t' _ h
      cases sel
      · have h' : (t.1, t.2.1, t.2.2) = (t'.1, t'.2.1, t'.2.2) := h
        simp only [Prod.mk.injEq] at h'
        exact Prod.ext h'.1 (Prod.ext h'.2.1 h'.2.2)
      · have h' : (t.2.1, t.1, t.2.2) = (t'.2.1, t'.1, t'.2.2) := h
        simp only [Prod.mk.injEq] at h'
        exact Prod.ext h'.2.1 (Prod.ext h'.1 h'.2.2)
    · intro p hp
      obtain ⟨-, hp2⟩ := Finset.mem_product.mp hp
      have hbad := (Finset.mem_filter.mp hp2).2
      cases sel
      · refine ⟨(p.1, p.2.1, p.2.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        simpa using hbad
      · refine ⟨(p.2.1, p.1, p.2.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        simpa using hbad
  rw [hcount, Finset.card_product, Finset.card_univ, ZMod.card]
  push_cast
  have : (N : Real) * (badlyConnected Comp).card ≤ 2 * (incompatibleTriples Comp).card := by
    linarith
  nlinarith

/-- The good triples for the assembly. -/
def goodTriples (Comp : ZMod N → ZMod N → ZMod N → Prop)
    (Bad4 : Finset (ZMod N × ZMod N × ZMod N)) : Finset (ZMod N × ZMod N × ZMod N) :=
  Finset.univ.filter fun t => Comp t.1 t.2.1 t.2.2 ∧ t ∉ Bad4 ∧
    t.1 ∈ wellConnected Comp t.2.2 ∧ t.2.1 ∈ wellConnected Comp t.2.2

theorem good_triples_card_ge (Comp : ZMod N → ZMod N → ZMod N → Prop)
    (Bad4 : Finset (ZMod N × ZMod N × ZMod N)) {ε ε₁ : Real}
    (h1 : ((incompatibleTriples Comp).card : Real) ≤ ε₁ * (N : Real) ^ 3)
    (h4 : (Bad4.card : Real) < ε * (N : Real) ^ 3) :
    (1 - 5 * ε₁ - ε) * (N : Real) ^ 3 ≤ (goodTriples Comp Bad4).card := by
  let BX := Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N =>
    (if true then t.1 else t.2.1) ∉ wellConnected Comp t.2.2
  let BY := Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N =>
    (if false then t.1 else t.2.1) ∉ wellConnected Comp t.2.2
  have hBX : (BX.card : Real) ≤ 2 * ε₁ * (N : Real) ^ 3 := wellConnected_compl_card_le Comp h1 true
  have hBY : (BY.card : Real) ≤ 2 * ε₁ * (N : Real) ^ 3 := wellConnected_compl_card_le Comp h1 false
  have hcover : (goodTriples Comp Bad4)ᶜ ⊆ incompatibleTriples Comp ∪ Bad4 ∪ BX ∪ BY := by
    intro t ht
    have ht' : ¬ (Comp t.1 t.2.1 t.2.2 ∧ t ∉ Bad4 ∧ t.1 ∈ wellConnected Comp t.2.2 ∧
        t.2.1 ∈ wellConnected Comp t.2.2) := by
      intro h
      exact Finset.mem_compl.mp ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp only [Finset.mem_union, incompatibleTriples, BX, BY, Finset.mem_filter,
      Finset.mem_univ, true_and, if_true]
    by_cases hc : Comp t.1 t.2.1 t.2.2
    · by_cases hb : t ∈ Bad4
      · exact Or.inl (Or.inl (Or.inr hb))
      · by_cases hx : t.1 ∈ wellConnected Comp t.2.2
        · exact Or.inr fun hy => ht' ⟨hc, hb, hx, hy⟩
        · exact Or.inl (Or.inr hx)
    · exact Or.inl (Or.inl (Or.inl hc))
  have hcard := Finset.card_le_card hcover
  have hu : (incompatibleTriples Comp ∪ Bad4 ∪ BX ∪ BY).card ≤
      (incompatibleTriples Comp).card + Bad4.card + BX.card + BY.card := by
    calc (incompatibleTriples Comp ∪ Bad4 ∪ BX ∪ BY).card
        ≤ (incompatibleTriples Comp ∪ Bad4 ∪ BX).card + BY.card := Finset.card_union_le _ _
      _ ≤ (incompatibleTriples Comp ∪ Bad4).card + BX.card + BY.card := by
          gcongr; exact Finset.card_union_le _ _
      _ ≤ _ := by gcongr; exact Finset.card_union_le _ _
  have hcompl : ((goodTriples Comp Bad4)ᶜ.card : Real) =
      (N : Real) ^ 3 - (goodTriples Comp Bad4).card := by
    rw [Finset.card_compl, Fintype.card_prod, Fintype.card_prod, ZMod.card,
      Nat.cast_sub (by
        have := Finset.card_le_univ (goodTriples Comp Bad4)
        simpa [Fintype.card_prod, ZMod.card] using this)]
    push_cast; ring
  have : ((goodTriples Comp Bad4)ᶜ.card : Real) ≤
      (incompatibleTriples Comp).card + Bad4.card + BX.card + BY.card := by
    exact_mod_cast hcard.trans hu
  linarith

/-- The good pairs for `a`. -/
def goodPairs (Comp : ZMod N → ZMod N → ZMod N → Prop)
    (Bad4 : Finset (ZMod N × ZMod N × ZMod N)) (a : ZMod N) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => (p.1, p.2, a) ∈ goodTriples Comp Bad4

theorem goodPairs_card_eq (Comp : ZMod N → ZMod N → ZMod N → Prop)
    (Bad4 : Finset (ZMod N × ZMod N × ZMod N)) (a : ZMod N) :
    (goodPairs Comp Bad4 a).card = ((goodTriples Comp Bad4).filter fun t => t.2.2 = a).card := by
  refine Finset.card_bij (fun p _ => (p.1, p.2, a)) ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2, rfl⟩
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  · intro t ht
    obtain ⟨htG, ha⟩ := Finset.mem_filter.mp ht
    refine ⟨(t.1, t.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [← ha]; exact htG
    · rw [← ha]

theorem good_pair_fibers_sum_ge (Comp : ZMod N → ZMod N → ZMod N → Prop)
    (Bad4 : Finset (ZMod N × ZMod N × ZMod N)) {ε ε₁ : Real}
    (h1 : ((incompatibleTriples Comp).card : Real) ≤ ε₁ * (N : Real) ^ 3)
    (h4 : (Bad4.card : Real) < ε * (N : Real) ^ 3) :
    (1 - (5 * ε₁ + ε)) * N * ((N : Real) ^ 2) ≤
      ∑ a : ZMod N, ((goodPairs Comp Bad4 a).card : Real) := by
  have h := good_triples_card_ge Comp Bad4 h1 h4
  have hsum := Finset.card_eq_sum_card_fiberwise (s := goodTriples Comp Bad4)
    (t := Finset.univ) (f := fun t => t.2.2) (fun _ _ => Finset.mem_univ _)
  have : ((goodTriples Comp Bad4).card : Real) =
      ∑ a : ZMod N, ((goodPairs Comp Bad4 a).card : Real) := by
    rw [hsum]; push_cast
    exact Finset.sum_congr rfl fun a _ => by rw [goodPairs_card_eq]
  rw [← this]
  calc (1 - (5 * ε₁ + ε)) * N * ((N : Real) ^ 2) = (1 - 5 * ε₁ - ε) * (N : Real) ^ 3 := by ring
    _ ≤ _ := h

end LeanProofs.GowersSzemeredi
