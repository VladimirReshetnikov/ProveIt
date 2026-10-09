import GowersSzemeredi.Proofs16GlobalRobustProgressionInput

/-! Four chosen four-term representations flatten injectively into one
additive 16-tuple. The negative rows swap adjacent pairs so that both index
values and local-map values use the ordinary alternating list convention. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

abbrev FourRepresentationTuple (N : Nat) := ZMod N × ZMod N × ZMod N × ZMod N

def representationTupleEval {N : Nat} (f : ZMod N → ZMod N) (q : FourRepresentationTuple N) : ZMod N :=
  f q.1-f q.2.1+f q.2.2.1-f q.2.2.2

def flattenFourRepresentations {N : Nat} (b : Fin 4 → FourRepresentationTuple N) : ColumnAnchorTuple N 15 :=
  ( (b 0).1,
    ![(b 0).2.1, (b 0).2.2.1, (b 0).2.2.2,
      (b 1).2.1, (b 1).1, (b 1).2.2.2, (b 1).2.2.1,
      (b 2).1, (b 2).2.1, (b 2).2.2.1, (b 2).2.2.2,
      (b 3).2.1, (b 3).1, (b 3).2.2.2, (b 3).2.2.1] )

theorem flattenFourRepresentations_injective {N : Nat} :
    Function.Injective (flattenFourRepresentations (N := N)) := by
  intro b c h
  have hh := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  funext i
  fin_cases i
  · exact Prod.ext hh (Prod.ext (congrFun ht 0) (Prod.ext (congrFun ht 1) (congrFun ht 2)))
  · exact Prod.ext (congrFun ht 4) (Prod.ext (congrFun ht 3) (Prod.ext (congrFun ht 6) (congrFun ht 5)))
  · exact Prod.ext (congrFun ht 7) (Prod.ext (congrFun ht 8) (Prod.ext (congrFun ht 9) (congrFun ht 10)))
  · exact Prod.ext (congrFun ht 12) (Prod.ext (congrFun ht 11) (Prod.ext (congrFun ht 14) (congrFun ht 13)))

theorem flattenFourRepresentations_eval {N : Nat} (f : ZMod N → ZMod N)
    (b : Fin 4 → FourRepresentationTuple N) :
    columnAnchorEval f (columnAnchorList (flattenFourRepresentations b)) =
      representationTupleEval f (b 0)-representationTupleEval f (b 1)+
        representationTupleEval f (b 2)-representationTupleEval f (b 3) := by
  simp [flattenFourRepresentations, columnAnchorList, List.ofFn_succ, columnAnchorEval, representationTupleEval]
  ring

/-- Valid representation rows of an additive quadruple give an original
additive 16-tuple, including its original index-set membership. -/
theorem flattenFourRepresentations_mem_fibre {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (b : Fin 4 → FourRepresentationTuple N)
    (hb : ∀ i, b i ∈ fourDifferenceRepresentations U (q i))
    (hq : q 0-q 1+q 2-q 3 = 0) :
    flattenFourRepresentations b ∈ columnAnchorFibre U 15 0 := by
  have hm : ∀ i, (b i).1 ∈ U ∧ (b i).2.1 ∈ U ∧ (b i).2.2.1 ∈ U ∧ (b i).2.2.2 ∈ U := by
    intro i
    simpa only [Finset.mem_product] using (Finset.mem_filter.mp (hb i)).1
  have hv : ∀ i, representationTupleEval id (b i) = q i := fun i => (Finset.mem_filter.mp (hb i)).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · simp only [flattenFourRepresentations, columnAnchorList, List.ofFn_succ, List.ofFn_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨(hm 0).1, (hm 0).2.1, (hm 0).2.2.1, (hm 0).2.2.2,
      (hm 1).2.1, (hm 1).1, (hm 1).2.2.2, (hm 1).2.2.1,
      (hm 2).1, (hm 2).2.1, (hm 2).2.2.1, (hm 2).2.2.2,
      (hm 3).2.1, (hm 3).1, (hm 3).2.2.2, (hm 3).2.2.1⟩
  · rw [flattenFourRepresentations_eval, hv, hv, hv, hv]
    exact hq

end LeanProofs.GowersSzemeredi
