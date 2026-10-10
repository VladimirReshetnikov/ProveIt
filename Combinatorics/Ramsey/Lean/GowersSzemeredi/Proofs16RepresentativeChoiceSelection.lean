import GowersSzemeredi.Proofs16IndependentChoiceSelection
import GowersSzemeredi.Proofs16FourRepresentationFlatten

/-! Select four-term representatives for progression points with few
failures against the original bad 16-tuple family. Distinct queried points
are treated independently; repeated progression indices remain separate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def progressionRepresentationChoiceSets {N : Nat} (U C : Finset (ZMod N)) (x : ZMod N) :
    Finset (FourRepresentationTuple N) :=
  if x ∈ C then fourDifferenceRepresentations U x else {(0,0,0,0)}

def representedBadFourBlocks {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (Bad : Finset (ColumnAnchorTuple N 15)) :
    Finset (Fin 4 → FourRepresentationTuple N) :=
  (Fintype.piFinset (fun j => fourDifferenceRepresentations U (q j))).filter
    (fun b => flattenFourRepresentations b ∈ Bad)

/-- A bad original 16-tuple determines both its four rows and all four
represented indices, so it is charged to at most one query. -/
theorem represented_bad_four_blocks_total_le {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (Q : Finset (Fin 4 → ZMod N)) (Bad : Finset (ColumnAnchorTuple N 15)) :
    (∑ q ∈ Q, (representedBadFourBlocks U q Bad).card) ≤ Bad.card := by
  let S := Q.sigma fun q => representedBadFourBlocks U q Bad
  have hcard : S.card ≤ Bad.card := by
    apply Finset.card_le_card_of_injOn (fun p => flattenFourRepresentations p.2)
    · intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
    · intro p hp r hr he
      have hb := flattenFourRepresentations_injective he
      have hpB := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).1
      have hrB := (Finset.mem_filter.mp (Finset.mem_sigma.mp hr).2).1
      have hq : p.1 = r.1 := by
        funext j
        have ep := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hpB j)).2
        have er := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hrB j)).2
        have ev : representationTupleEval id (p.2 j) = representationTupleEval id (r.2 j) :=
          congrArg (fun b => representationTupleEval id (b j)) hb
        exact ep.symm.trans (ev.trans er)
      cases p with | mk p1 p2 =>
        cases r with | mk r1 r2 =>
          dsimp only at hq hb
          subst r1
          exact Sigma.ext rfl (heq_of_eq hb)
  simpa only [S, Finset.card_sigma] using hcard

/-- One representative per progression point satisfies the averaged error
bound for all distinct-index queries, with only four local density factors. -/
theorem exists_progression_representatives_few_bad_distinct {N : Nat} [NeZero N]
    (U C : Finset (ZMod N)) {kappa : Real} (hk : 0 < kappa)
    (hrep : ∀ x ∈ C, kappa*(N : Real)^3 ≤ (fourDifferenceRepresentations U x).card)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : ∀ q ∈ Q, (∀ j, q j ∈ C) ∧ Function.Injective q)
    (Bad : Finset (ColumnAnchorTuple N 15)) :
    ∃ f : ZMod N → FourRepresentationTuple N,
      (∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x) ∧
      (((Q.filter fun q => flattenFourRepresentations (fun j => f (q j)) ∈ Bad).card) : Real) ≤
        (Bad.card : Real)/(kappa^4*(N : Real)^12) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let F := progressionRepresentationChoiceSets U C
  have hF : ∀ x : ZMod N, (F x).Nonempty := by
    intro x
    by_cases hx : x ∈ C
    · have hpos : (0 : Real) < (fourDifferenceRepresentations U x).card :=
        (by positivity : (0 : Real) < kappa*(N : Real)^3).trans_le (hrep x hx)
      simpa [F, progressionRepresentationChoiceSets, hx] using
        (Finset.card_pos.mp (by exact_mod_cast hpos))
    · simp [F, progressionRepresentationChoiceSets, hx]
  have hB : ∀ q ∈ Q, ∀ b ∈ representedBadFourBlocks U q Bad, ∀ j, b j ∈ F (q j) := by
    intro q hq b hb j
    have h := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hb).1 j
    simpa only [F, progressionRepresentationChoiceSets, if_pos ((hQ q hq).1 j)] using h
  have hprod : ∀ q ∈ Q, kappa^4*(N : Real)^12 ≤ ((∏ j : Fin 4, (F (q j)).card) : Real) := by
    intro q hq
    have hp : (∏ _j : Fin 4, kappa*(N : Real)^3) ≤ ∏ j : Fin 4, ((F (q j)).card : Real) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j hj
      simpa only [F, progressionRepresentationChoiceSets, if_pos ((hQ q hq).1 j)] using hrep (q j) ((hQ q hq).1 j)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ←pow_mul,
      Nat.cast_prod] using hp
  obtain ⟨f, hf, hbad⟩ := exists_independent_choice_few_bad_queries (E := (Bad.card : Real)) F hF Q
    (fun q => representedBadFourBlocks U q Bad) (fun q hq => (hQ q hq).2) hB
    (by positivity : (0 : Real) < kappa^4*(N : Real)^12) hprod
    (by exact_mod_cast represented_bad_four_blocks_total_le U Q Bad)
  have hvalid : ∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x := by
    intro x hx
    simpa only [F, progressionRepresentationChoiceSets, if_pos hx] using Fintype.mem_piFinset.mp hf x
  have heq : (Q.filter fun q => (fun j => f (q j)) ∈ representedBadFourBlocks U q Bad) =
      Q.filter (fun q => flattenFourRepresentations (fun j => f (q j)) ∈ Bad) := by
    apply Finset.filter_congr
    intro q hq
    simp only [representedBadFourBlocks, Finset.mem_filter]
    exact and_iff_right (Fintype.mem_piFinset.mpr (fun j => hvalid _ ((hQ q hq).1 j)))
  rw [heq] at hbad
  exact ⟨f, hvalid, hbad⟩

end LeanProofs.GowersSzemeredi
