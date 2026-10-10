import GowersSzemeredi.Proofs16IndependentChoiceSelection
import GowersSzemeredi.Proofs16ClaimNineFive

/-! Choosing the pairs `(x_a, y_a)` in the final selection of Milićević's
Proposition 9.3 (arXiv:2601.01682, printed p. 67), by the peer's
independent-choice averaging (`exists_independent_choice_few_bad_queries`).

Each `a` chooses a pair `c(a) = (x_a, y_a)` from its set `G_a` of good pairs.
An additive quadruple `q = a[4]` and the chosen pairs determine a 12-tuple
`twelveOf q c` (`x_j = c(a_j).1`, `y_j = c(a_j).2`, and `a₃ = a₀ + a₁ − a₂`).
`twelveOf` is injective on additive quadruples (`twelveOf_injective`). So
over all queries the bad choice tuples number at most `|Bad|`, for any set
`Bad` of 12-tuples: for instance the bad 12-tuples of the iteration, together
with the tuples whose 8-tuples are not respected.
* `exists_pair_choice_few_bad`: suppose every query has
  `∏_j |G_{a_j}| ≥ D`. Then some choice makes at most `|Bad|/D`
  distinct-index queries land in `Bad`. With `|G_a| ≥ γN²` and
  `|Bad| ≤ εN¹¹`, that is `εN³/γ⁴` failing quadruples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The 12-tuple of a quadruple of `a`'s and their chosen pairs. -/
def twelveOf {N : Nat} (q : Fin 4 → ZMod N) (c : Fin 4 → ZMod N × ZMod N) : Fin 11 → ZMod N :=
  ![(c 0).1, (c 1).1, (c 2).1, (c 3).1, (c 0).2, (c 1).2, (c 2).2, (c 3).2, q 0, q 1, q 2]

theorem twelveOf_coords {N : Nat} (q : Fin 4 → ZMod N) (c : Fin 4 → ZMod N × ZMod N)
    (hq : q 0 + q 1 = q 2 + q 3) (j : Fin 4) :
    twelveX (twelveOf q c) j = (c j).1 ∧ twelveY (twelveOf q c) j = (c j).2 ∧
      twelveA (twelveOf q c) j = q j := by
  fin_cases j
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨rfl, rfl, ?_⟩
    show q 0 + q 1 - q 2 = q 3
    linear_combination hq

theorem twelveOf_injective {N : Nat} {q q' : Fin 4 → ZMod N} {c c' : Fin 4 → ZMod N × ZMod N}
    (hq : q 0 + q 1 = q 2 + q 3) (hq' : q' 0 + q' 1 = q' 2 + q' 3)
    (h : twelveOf q c = twelveOf q' c') : q = q' ∧ c = c' := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · have e := (twelveOf_coords q c hq j).2.2
    have e' := (twelveOf_coords q' c' hq' j).2.2
    rw [← e, ← e', h]
  · obtain ⟨ex, ey, -⟩ := twelveOf_coords q c hq j
    obtain ⟨ex', ey', -⟩ := twelveOf_coords q' c' hq' j
    rw [h] at ex ey
    exact Prod.ext (ex.symm.trans ex') (ey.symm.trans ey')

/-- **Choosing the pairs.** -/
theorem exists_pair_choice_few_bad {N : Nat} (G : ZMod N → Finset (ZMod N × ZMod N))
    [NeZero N] (hG : ∀ a, (G a).Nonempty) (Q : Finset (Fin 4 → ZMod N))
    (hQinj : ∀ q ∈ Q, Function.Injective q) (hQadd : ∀ q ∈ Q, q 0 + q 1 = q 2 + q 3)
    (Bad : Finset (Fin 11 → ZMod N)) {D : Real} (hD : 0 < D)
    (hprod : ∀ q ∈ Q, D ≤ ((∏ j : Fin 4, (G (q j)).card : Nat) : Real)) :
    ∃ c : ZMod N → ZMod N × ZMod N, (∀ a, c a ∈ G a) ∧
      ((Q.filter fun q => twelveOf q (fun j => c (q j)) ∈ Bad).card : Real) ≤ Bad.card / D := by
  let B : (Fin 4 → ZMod N) → Finset (Fin 4 → ZMod N × ZMod N) := fun q =>
    (Fintype.piFinset fun j => G (q j)).filter fun b => twelveOf q b ∈ Bad
  have hB : ∀ q ∈ Q, ∀ b ∈ B q, ∀ j, b j ∈ G (q j) := fun q _ b hb j =>
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp hb).1 j
  have htotal : ∑ q ∈ Q, ((B q).card : Real) ≤ Bad.card := by
    have hsig : ∑ q ∈ Q, (B q).card = (Q.sigma B).card := (Finset.card_sigma _ _).symm
    have hle : (Q.sigma B).card ≤ Bad.card := by
      refine Finset.card_le_card_of_injOn (fun x => twelveOf x.1 x.2) ?_ ?_
      · intro x hx
        exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
      · intro x hx y hy hxy
        have hx1 := (Finset.mem_sigma.mp hx).1
        have hy1 := (Finset.mem_sigma.mp hy).1
        obtain ⟨h1, h2⟩ := twelveOf_injective (hQadd _ hx1) (hQadd _ hy1) hxy
        exact Sigma.ext h1 (heq_of_eq h2)
    have : ∑ q ∈ Q, (B q).card ≤ Bad.card := hsig ▸ hle
    exact_mod_cast this
  obtain ⟨f, hf, hcount⟩ := exists_independent_choice_few_bad_queries G hG Q B hQinj hB hD
    (fun q hq => by exact_mod_cast hprod q hq) htotal
  refine ⟨f, fun a => Fintype.mem_piFinset.mp hf a, le_trans ?_ hcount⟩
  have hsub : (Q.filter fun q => twelveOf q (fun j => f (q j)) ∈ Bad) ⊆
      Q.filter fun q => (fun j => f (q j)) ∈ B q := by
    intro q hq
    obtain ⟨hqQ, hbad⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨hqQ, Finset.mem_filter.mpr ⟨?_, hbad⟩⟩
    exact Fintype.mem_piFinset.mpr fun j => Fintype.mem_piFinset.mp hf (q j)
  exact_mod_cast Finset.card_le_card hsub

end LeanProofs.GowersSzemeredi
