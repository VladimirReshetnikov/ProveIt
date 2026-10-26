import DiophantineConsistency.WangTiles942PhysicalOrder

/-! Focused coverage, ordering, rank and modular-evaluation interface checks.
The numerical tests below evaluate only the literal cache, never floor ranks. -/
namespace DiophantineConsistency.WangTiles942PhysicalOrderChecks
open WangTiles942 WangTiles942PhysicalData WangTiles942PhysicalOrder
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000

example : rows.length=941 := rows_length
example (j : Fin 941) :
    0 < (abstractIndex j).val ∧
    selectorWeight (tile (abstractIndex j))=value j := by
  exact ⟨Fin.pos_iff_ne_zero.mpr (abstractIndex_ne_zero j),weight_eq j⟩

example : StrictAnti value := value_strictAnti
example : Function.Bijective nonStartIndex := nonStartIndex_bijective
example : Function.Bijective abstractAt := abstractAt_bijective
example (p : Fin 942) : physicalPosition (abstractAt p)=p.val :=
  congrArg Fin.val (physicalMap_abstractAt p)
example (i : Fin 942) : ∃! p : Fin 942, abstractAt p=i := by
  obtain ⟨p,hp⟩ := full_coverage i
  exact ⟨p,hp,fun q hq => abstractAt_bijective.injective (hq.trans hp.symm)⟩

example : abstractAt 0=0 := abstractAt_zero
example : abstractAt 1=926 := by decide +kernel
example : abstractAt 459=866 := by decide +kernel
example : abstractAt 504=928 := by decide +kernel
example : abstractAt 940=9 := by decide +kernel
example : abstractAt 941=433 := by decide +kernel
example : abstractAt 1≠925 := by decide +kernel
example : weightAt 0=34876427265 ∧ weightAt 941=1025 := by decide +kernel

/-- Start is protected at zero; sorting it with the non-Start rows is wrong. -/
example : weightAt 0 < weightAt 1 := by decide +kernel

example (j : Fin 941) : value j=physicalWeight j.succ := value_eq_physicalWeight j
example (f : ℕ → ℕ → ℕ) :
    (∑ i : Fin 942, f (physicalPosition i) (selectorWeight (tile i))) =
      ∑ p : Fin 942, f p.val (weightAt p) := selector_sum_reindex f

/-- The generic finite-order lemma includes the zero-size type without premises. -/
example (f : Fin 0 → Fin 0) (hf : StrictMono f) (i : Fin 0) : f i=i :=
  strictMono_fin_eq_self f hf i
example (f : Fin 1 → Fin 1) (hf : StrictMono f) : f 0=0 :=
  strictMono_fin_eq_self f hf 0

#print axioms rows_good
#print axioms rows_descending
#print axioms weight_eq
#print axioms value_strictAnti
#print axioms nonStartIndex_bijective
#print axioms strictMono_fin_eq_self
#print axioms rankMap_eq
#print axioms position_eq
#print axioms physicalMap_abstractAt
#print axioms abstractAt_physicalMap
#print axioms abstractAt_bijective
#print axioms abstractAt_eq_inverse
#print axioms full_coverage
#print axioms value_eq_physicalWeight
#print axioms weight_abstractAt
#print axioms selector_sum_reindex
end DiophantineConsistency.WangTiles942PhysicalOrderChecks
