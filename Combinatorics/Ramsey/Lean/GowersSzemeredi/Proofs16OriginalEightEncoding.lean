import GowersSzemeredi.Proofs16QuerySourceAgreement

/-! Two original four-term representations join to one original additive
eight-tuple. The negative block swaps adjacent entries to preserve the
ordinary alternating-list convention. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def joinSourceRepresentations {N : Nat} (p q : FourRepresentationTuple N) : ColumnAnchorTuple N 7 :=
  (p.1,![p.2.1,p.2.2.1,p.2.2.2,q.2.1,q.1,q.2.2.2,q.2.2.1])

theorem joinSourceRepresentations_injective {N : Nat} :
    Function.Injective (fun p : FourRepresentationTuple N × FourRepresentationTuple N => joinSourceRepresentations p.1 p.2) := by
  intro p q he
  have hh := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  apply Prod.ext
  · exact Prod.ext hh (Prod.ext (congrFun ht 0) (Prod.ext (congrFun ht 1) (congrFun ht 2)))
  · exact Prod.ext (congrFun ht 4) (Prod.ext (congrFun ht 3) (Prod.ext (congrFun ht 6) (congrFun ht 5)))

theorem join_source_representations_eval {N : Nat} (f : ZMod N → ZMod N)
    (p q : FourRepresentationTuple N) :
    columnAnchorEval f (columnAnchorList (joinSourceRepresentations p q)) =
      representationTupleEval f p-representationTupleEval f q := by
  simp [joinSourceRepresentations,columnAnchorList,List.ofFn_succ,columnAnchorEval,representationTupleEval]
  ring

theorem join_source_representations_mem_fibre {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) {a u : ZMod N} {p q : FourRepresentationTuple N}
    (hp : p ∈ fourDifferenceRepresentations U (u+a)) (hq : q ∈ fourDifferenceRepresentations U u) :
    joinSourceRepresentations p q ∈ columnAnchorFibre U 7 a := by
  have hpm : p.1 ∈ U ∧ p.2.1 ∈ U ∧ p.2.2.1 ∈ U ∧ p.2.2.2 ∈ U := by
    simpa only [Finset.mem_product] using (Finset.mem_filter.mp hp).1
  have hqm : q.1 ∈ U ∧ q.2.1 ∈ U ∧ q.2.2.1 ∈ U ∧ q.2.2.2 ∈ U := by
    simpa only [Finset.mem_product] using (Finset.mem_filter.mp hq).1
  have hpe := (Finset.mem_filter.mp hp).2
  have hqe := (Finset.mem_filter.mp hq).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
  · simp only [joinSourceRepresentations,columnAnchorList,List.ofFn_succ,List.ofFn_zero,List.mem_cons,
      List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨hpm.1,hpm.2.1,hpm.2.2.1,hpm.2.2.2,hqm.2.1,hqm.1,hqm.2.2.2,hqm.2.2.1⟩
  · rw [join_source_representations_eval]
    change (p.1-p.2.1+p.2.2.1-p.2.2.2)-(q.1-q.2.1+q.2.2.1-q.2.2.2) = a
    linear_combination hpe-hqe

/-- The original eight-tuple endpoint domain contains exactly the two
original representation spectra; no selected-map frequency is discarded. -/
theorem bohr_joined_source_spectrum {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (p q : FourRepresentationTuple N) (rho : Real) :
    bohr (columnListSpectrum T (columnAnchorList (joinSourceRepresentations p q))) rho =
      bohr (representationColumnSpectrum T p ∪ representationColumnSpectrum T q) rho := by
  ext y
  rw [bohr_union]
  simp only [Finset.mem_inter,mem_columnListSpectrum_bohr,representationColumnSpectrum]
  simp only [joinSourceRepresentations,columnAnchorList,List.ofFn_succ,List.ofFn_zero,
    representationColumnEntries,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  tauto

end LeanProofs.GowersSzemeredi
