import GowersSzemeredi.Proofs16Corollary20Bohr

/-! Remove the distinct-point qualification in the selection iteration.
The degenerate triples cost at most four planes, each of size N². -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- At most four planes of triples have coincident evaluation points. -/
theorem nonDistinctTriple_card_le (N : Nat) [NeZero N] :
    (Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N => ¬ DistinctTriple t).card ≤ 4 * N^2 := by
  let V : Finset (ZMod N × ZMod N) := Finset.univ
  let A := V.image fun p => (p.1, p.2, p.2)
  let B := V.image fun p => ((0 : ZMod N), p.1, p.2)
  let C := V.image fun p => (p.1, p.2, p.1 + p.2)
  let D := V.image fun p => (p.1, p.1 + p.2, p.2)
  have hsub : (Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N => ¬ DistinctTriple t) ⊆
      A ∪ B ∪ C ∪ D := by
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    simp only [DistinctTriple, not_and_or, not_not] at h
    simp only [Finset.mem_union]
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Finset.mem_image.mpr
        ⟨(t.1, t.2.1), Finset.mem_univ _, by ext <;> simp_all⟩)))
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr
        ⟨(t.2.1, t.2.2), Finset.mem_univ _, by ext <;> simp_all⟩)))
    · exact Or.inl (Or.inr (Finset.mem_image.mpr
        ⟨(t.1, t.2.1), Finset.mem_univ _, by ext <;> simp_all⟩))
    · exact Or.inr (Finset.mem_image.mpr
        ⟨(t.1, t.2.2), Finset.mem_univ _, by ext <;> simp_all⟩)
  have hmap (f : ZMod N × ZMod N → ZMod N × ZMod N × ZMod N) : (V.image f).card ≤ N^2 := by
    calc (V.image f).card ≤ V.card := Finset.card_image_le
      _ = N^2 := by simp [V, Fintype.card_prod, ZMod.card, pow_two]
  have hA := hmap (fun p => (p.1, p.2, p.2))
  have hB := hmap (fun p => ((0 : ZMod N), p.1, p.2))
  have hC := hmap (fun p => (p.1, p.2, p.1 + p.2))
  have hD := hmap (fun p => (p.1, p.1 + p.2, p.2))
  change A.card ≤ N^2 at hA
  change B.card ≤ N^2 at hB
  change C.card ≤ N^2 at hC
  change D.card ≤ N^2 at hD
  have h0 := Finset.card_le_card hsub
  have h1 := Finset.card_union_le (A ∪ B ∪ C) D
  have h2 := Finset.card_union_le (A ∪ B) C
  have h3 := Finset.card_union_le A B
  omega

/-- All bad witnesses are counted by the distinct bad triples and the
four exceptional planes. -/
theorem badWitnessTriple_card_le {N : Nat} [NeZero N]
    (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) :
    (Finset.univ.filter fun t => ∃ v, BadWitness U E L t v).card ≤
      (Finset.univ.filter (IsBadTriple U E L)).card + 4 * N^2 := by
  have hsub : (Finset.univ.filter fun t => ∃ v, BadWitness U E L t v) ⊆
      (Finset.univ.filter (IsBadTriple U E L)) ∪
        (Finset.univ.filter fun t : ZMod N × ZMod N × ZMod N => ¬ DistinctTriple t) := by
    intro t ht
    by_cases hd : DistinctTriple t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hd, (Finset.mem_filter.mp ht).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (nonDistinctTriple_card_le N) _))

/-- For sufficiently large N the Bohr-extended selection covers all but
εN³ triples, including triples with repeated evaluation points. -/
theorem corollary20_bohr_all_triples {N : Nat} [NeZero N] [Fact N.Prime]
    (U : ZMod N → Finset (ZMod N)) (h0 : ∀ x, (0 : ZMod N) ∈ U x)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) {ε : Real}
    (hε : 0 < ε) (hN : 8 / ε ≤ (N : Real)) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
      (S : Fin m → Finset (ZMod N)),
      m ≤ ⌊(K : Real) / corollary20Kappa (ε / 2) K⌋₊ + 1 ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa (ε / 2) K * N ≤ (E i).card ∧
        (∀ x ∈ E i, L i x ∈ U x) ∧
        ((S i).card : Real) ≤ 16 * (corollary20Kappa (ε / 2) K)^(-(2 : Real)) ∧
        IsBHomomorphism (E i) (bohr (S i) (corollary20Kappa (ε / 2) K / (32 * Real.pi))) (L i)) ∧
      ((Finset.univ.filter fun t => ∃ v, BadWitness U E L t v).card : Real) < ε * (N : Real)^3 := by
  obtain ⟨m, E, L, S, hm, hE, hbad⟩ := corollary20_bohr_pieces U h0 hK1 hK (half_pos hε)
  refine ⟨m, E, L, S, hm, hE, ?_⟩
  have hcount : ((Finset.univ.filter fun t => ∃ v, BadWitness U E L t v).card : Real) ≤
      (Finset.univ.filter (IsBadTriple U E L)).card + 4 * (N : Real)^2 := by
    exact_mod_cast badWitnessTriple_card_le U E L
  have hlarge : (8 : Real) ≤ N * ε := (div_le_iff₀ hε).mp hN
  have herr : 4 * (N : Real)^2 ≤ ε / 2 * (N : Real)^3 := by
    have h := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (N : Real))
    nlinarith only [h]
  linarith

end LeanProofs.GowersSzemeredi
