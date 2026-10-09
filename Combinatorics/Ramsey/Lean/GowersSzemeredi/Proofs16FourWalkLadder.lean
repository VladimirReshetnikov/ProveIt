import GowersSzemeredi.Proofs16WeakTransitivityLadder
import GowersSzemeredi.Proofs16GraphFourWalks

/-! Robust connectivity plus weak transitivity: Milićević's Claim 4.3
(arXiv:2601.01682, printed p. 49) in the four-walk form of J.102.

* `chainCount_three_eq`: `chainCount r univ 3 u v` is the number of
  four-walks `u–a–z–b–v` (`graphFourWalks`).
* `rel_four_on_four_walk_set`: let `R` be a relation ladder whose first
  level is symmetric with ordered-edge density `δ`, and which is weakly
  transitive against `R 1` with constant `c ≤ δ^5/2^17`. Then a set of at
  least `3δn/8` vertices has `R 4 u v` for every two of its vertices.

The density, the vertex count and the transitivity constant are all
polynomial in `δ`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem chainCount_three_eq {V : Type*} [Fintype V] (r : V → V → Prop) (u v : V) :
    chainCount r Finset.univ 3 u v = (graphFourWalks r u v).card := by
  have hL : chainCount r Finset.univ 3 u v = ∑ t : V × V × V,
      (if r u t.2.2 then 1 else 0) * (if r t.2.2 t.2.1 then 1 else 0) *
        (if r t.2.1 t.1 then 1 else 0) * (if r t.1 v then 1 else 0) := by
    simp only [chainCount, Fintype.sum_prod_type, Finset.sum_mul]
  rw [hL, graphFourWalks, Finset.card_filter]
  refine Fintype.sum_equiv
    ⟨fun t => (t.2.2, t.2.1, t.1), fun t => (t.2.2, t.2.1, t.1), fun _ => rfl, fun _ => rfl⟩
    _ _ (fun t => ?_)
  obtain ⟨x3, x2, x1⟩ := t
  dsimp only [Equiv.coe_fn_mk]
  by_cases h1 : r u x1 <;> by_cases h2 : r x1 x2 <;> by_cases h3 : r x2 x3 <;>
    by_cases h4 : r x3 v <;> simp [h1, h2, h3, h4]

/-- **Claim 4.3, four-walk form.** -/
theorem rel_four_on_four_walk_set {V : Type*} [Fintype V] [Nonempty V]
    (R : Nat → V → V → Prop) (hsym : ∀ a b, R 1 a b → R 1 b a) {c δ : Real} (hd : 0 < δ)
    (hedges : δ * (Fintype.card V : Real) ^ 2 ≤
      ∑ x : V, ((graphNeighbours (R 1) x).card : Real))
    (hWT : ∀ i, i + 1 ≤ 4 → ∀ x y, c * (Fintype.card V : Real) ≤
      ((Finset.univ.filter fun z => R i x z ∧ R 1 z y).card : Real) → R (i + 1) x y)
    (hc : 8 * c ≤ δ ^ 5 / 16384) :
    ∃ T : Finset V, 3 * δ * Fintype.card V / 8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T, R 4 u v := by
  obtain ⟨T, hT, hwalk⟩ := exists_dense_four_walk_set (R 1) hsym hd hedges
  refine ⟨T, hT, fun u hu v hv => ?_⟩
  have hWT' : ∀ i, i + 1 ≤ 4 → ∀ x y, c * (Finset.univ : Finset V).card ≤
      (((Finset.univ : Finset V).filter fun z => R i x z ∧ R 1 z y).card : Real) →
      R (i + 1) x y := by
    intro i hi x y h
    exact hWT i hi x y (by simpa only [Finset.card_univ] using h)
  have hcount : δ ^ 5 / 16384 * ((Finset.univ : Finset V).card : Real) ^ 3 ≤
      chainCount (R 1) Finset.univ 3 u v := by
    rw [chainCount_three_eq, Finset.card_univ]
    have := hwalk u hu v hv
    linarith
  exact rel_of_chainCount R Finset.univ hWT' 3 u v (by norm_num) (by positivity)
    (by norm_num; linarith) hcount

end LeanProofs.GowersSzemeredi
