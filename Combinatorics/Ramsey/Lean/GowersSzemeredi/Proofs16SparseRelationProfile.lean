import GowersSzemeredi.Proofs16BadRelationSplitting
import GowersSzemeredi.Proofs16PrimeBandSplit

/-! Few bad bounded relations imply a quasirandom Bohr graph. The exceptional
vertices, exceptional pairs, and typical reference vertex are constructed
from the bad-relation set rather than supplied as separate hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Sparse bad relations supply every combinatorial hypothesis of the prime
split-profile theorem. Only its analytic cutoff and size budgets remain. -/
theorem sparse_relation_profile_quasirandom {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D C : Finset (ZMod N)) (hC : C ⊆ D) (hCne : C.Nonempty)
    (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (a : ι → Nat) (b : κ → Nat) {c R : Nat}
    (hca : ∀ i, c ≤ a i) (hcb : ∀ j, c ≤ b j)
    (ha : ∀ i, 2 * a i < N) (hb : ∀ j, 2 * b j < N) (hc : 2 * c < N)
    {theta : Real} (htheta : theta < 1)
    (hbad : ((boundedBadRelationPairs gamma D L C R).card : Real) ≤ theta * (C.card : Real)^2)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ (κ ⊕ κ)) - 1 ≤ Fintype.card (ι ⊕ (κ ⊕ κ)) * (4 * c + 2) / N)
    (hsize : 20 * (Fintype.card (ι ⊕ (κ ⊕ κ)) * (4 * c + 2)) ≤
      ((mixedBohr gamma (fun i => a i - c)).card : Real)) :
    ∃ delta : Real, 0 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (x : ↥(mixedBohr gamma (fun i => a i - c))) (y : ↥C) =>
        (if (x : ZMod N) ∈ mixedBohr (fun j => L j y) (fun j => b j - c)
          then (1 : Real) else 0) - delta) ≤
      3 * (80 * (Fintype.card (ι ⊕ (κ ⊕ κ)) * (4 * c + 2)) /
          (mixedBohr gamma (fun i => a i - c)).card + theta) *
        ((mixedBohr gamma (fun i => a i - c)).card : Real)^2 * (C.card : Real)^2 := by
  let Ybad : Finset ↥C := Finset.univ.filter fun y =>
    (y : ZMod N) ∈ boundedBadRelationVertices gamma D L C R
  let Pbad : Finset (↥C × ↥C) := Finset.univ.filter fun p =>
    ((p.1 : ZMod N), (p.2 : ZMod N)) ∈ boundedBadRelationPairs gamma D L C R
  have hYcard : Ybad.card ≤ (boundedBadRelationVertices gamma D L C R).card := by
    apply Finset.card_le_card_of_injOn (fun y : ↥C => (y : ZMod N))
    · intro y hy; exact (Finset.mem_filter.mp hy).2
    · intro x _ y _ h; exact Subtype.ext h
  have hPcard : Pbad.card ≤ (boundedBadRelationPairs gamma D L C R).card := by
    apply Finset.card_le_card_of_injOn (fun p : ↥C × ↥C => ((p.1 : ZMod N), (p.2 : ZMod N)))
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · intro x _ y _ h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hYbad : (Ybad.card : Real) ≤ theta * Fintype.card ↥C := by
    rw [Fintype.card_coe]
    exact (Nat.cast_le.mpr hYcard).trans (bad_relation_vertices_card_le gamma D L C hCne R hbad)
  have hPbad : (Pbad.card : Real) ≤ theta * (Fintype.card ↥C : Real)^2 := by
    rw [Fintype.card_coe]
    exact (Nat.cast_le.mpr hPcard).trans hbad
  have hCpos : (0 : Real) < Fintype.card ↥C := by
    rw [Fintype.card_coe]; exact_mod_cast hCne.card_pos
  have hex : ∃ y : ↥C, y ∉ Ybad := by
    by_contra h
    push Not at h
    have heq : Ybad = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [heq, Finset.card_univ] at hYbad
    nlinarith
  obtain ⟨y₀, hy₀⟩ := hex
  have hsplit1 : ∀ y : ↥C, y ∉ Ybad → ∀ (nu : ι → centeredBall N R) (w : κ → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (w j : ZMod N) * L j y) = 0 ↔
      (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ w ∈ boundedRelationClass D L R) := by
    intro y hy nu w
    apply bounded_single_split_of_not_bad gamma D L hzero C hC R y.property
    intro h; exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsplit2 : ∀ y y' : ↥C, (y, y') ∉ Pbad → ∀ (nu : ι → centeredBall N R) (mu : (κ ⊕ κ) → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) +
        (∑ j, (mu j : ZMod N) * Sum.elim (fun k => L k y) (fun k => L k y') j) = 0 ↔
      (∑ i, (nu i : ZMod N) * gamma i = 0 ∧
        (fun j => mu (Sum.inl j)) ∈ boundedRelationClass D L R ∧
        (fun j => mu (Sum.inr j)) ∈ boundedRelationClass D L R) := by
    intro y y' hp nu mu
    apply bounded_pair_sum_split_of_not_bad gamma D L hzero C hC R y.property y'.property
    intro h; exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  simpa only [Fintype.card_coe] using split_profile_quasirandom_prime gamma
    (fun y : ↥C => fun j => L j y) a b hca hcb ha hb hc (boundedRelationClass D L R)
    htrunc hsize Ybad hYbad hy₀ hsplit1 Pbad hPbad hsplit2

end LeanProofs.GowersSzemeredi
