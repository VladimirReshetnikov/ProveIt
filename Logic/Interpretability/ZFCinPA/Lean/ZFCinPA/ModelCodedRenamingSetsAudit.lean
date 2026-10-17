import ZFCinPA.ModelCodedRenamingSets
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LeanProofs.ZFCinPA.ModelCodedRenamingSets
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_existsUnique
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.mem_setRename_iff
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_isFormulaSet
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_empty
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_insert
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_subset
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_shift_lift
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.setRename_shift_offset
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingSets.rename_substs1
example (a k s seq : V) : ∃! out : V, ∀ y,
    y ∈ out ↔ ∃ x ∈ seq, y = rename L a k s x := setRename_existsUnique L a k s seq
example (a k s seq y : V) : y ∈ setRename L a k s seq ↔
    ∃ x ∈ seq, y = rename L a k s x := mem_setRename_iff a k s
example (a k s seq p : V) (hp : p ∈ seq) :
    rename L a k s p ∈ setRename L a k s seq := rename_mem_setRename a k s hp
example (a k s seq : V) (hs : IsFormulaSet L seq) :
    IsFormulaSet L (setRename L a k s seq) := setRename_isFormulaSet a k s hs
example (a k s : V) : setRename L a k s (∅ : V) = ∅ := setRename_empty a k s
example (a k s p seq : V) : setRename L a k s (insert p seq) =
    insert (rename L a k s p) (setRename L a k s seq) := setRename_insert a k s p seq
example (a k s seq target : V) (h : seq ⊆ target) :
    setRename L a k s seq ⊆ setRename L a k s target := setRename_subset a k s h
example (a k s seq : V) (hs : IsFormulaSet L seq) :
    setRename L a (k+1) s (setShift L seq) = setShift L (setRename L a k s seq) :=
  setRename_shift_lift a k s hs
example (a s seq : V) (hs : IsFormulaSet L seq) :
    setRename L a 0 s (setShift L seq) = setRename L a 0 (s+1) seq :=
  setRename_shift_offset a s hs
example (a k s p t : V) (hp : IsSemiformula L 1 p) (ht : IsTerm L t) :
    rename L a k s (substs1 L t p) =
      substs1 L (termRename L a k s t) (rename L a k s p) := rename_substs1 a k s hp ht
