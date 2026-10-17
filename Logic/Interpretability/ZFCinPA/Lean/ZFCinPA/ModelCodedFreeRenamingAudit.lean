import ZFCinPA.ModelCodedFreeRenaming

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.renameIndex_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.termRename_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.termRenameVec_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.renameIndex_lift_zero
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.renameIndex_lift_succ
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.renameIndex_offset_succ
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.termRename_isSemiterm
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_isSemiformula
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_shift_lift
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_shift_offset
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_subst
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_free_lift
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_of_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedFreeRenaming.rename_neg

example (a k s : V) : renameIndex a (k+1) s 0 = 0 := renameIndex_lift_zero a k s
example (a k s x : V) : renameIndex a (k+1) s (x+1) = renameIndex a k s x+1 :=
  renameIndex_lift_succ a k s x
example (a s x : V) : renameIndex a 0 s (x+1) = renameIndex a 0 (s+1) x :=
  renameIndex_offset_succ a s x
example (a k s d t : V) (ht : IsSemiterm L d t) :
    IsSemiterm L d (termRename L a k s t) := termRename_isSemiterm a k s ht
example (a k s d p : V) (hp : IsSemiformula L d p) :
    IsSemiformula L d (rename L a k s p) := rename_isSemiformula a k s hp
example (a k s p : V) (hp : IsFormula L p) :
    rename L a (k+1) s (shift L p) = shift L (rename L a k s p) :=
  rename_shift_lift a k s hp.isUFormula
example (a s p : V) (hp : IsFormula L p) :
    rename L a 0 s (shift L p) = rename L a 0 (s+1) p :=
  rename_shift_offset a s hp.isUFormula
example (a k s p : V) (hp : IsSemiformula L 1 p) :
    rename L a (k+1) s (free L p) = free L (rename L a k s p) :=
  rename_free_lift a k s hp
example (a k s n m p w : V) (hp : IsSemiformula L n p)
    (hw : IsSemitermVec L n m w) :
    rename L a k s (subst L w p) =
      subst L (termRenameVec L a k s n w) (rename L a k s p) :=
  rename_subst a k s hp m w hw
example (a k s p : V) (hp : IsFormula L p) (hf : shift L p = p) :
    rename L a k s p = p := rename_of_shift_fixed a k s hp.isUFormula hf
example (a k s p : V) (hp : IsFormula L p) :
    rename L a k s (neg L p) = neg L (rename L a k s p) :=
  rename_neg a k s hp.isUFormula
example (a k s p : V) (hp : IsUFormula L p) :
    rename L a k s (^∀ p) = ^∀ (rename L a k s p) := rename_all a k s hp
example (a k s p : V) (hp : IsUFormula L p) :
    rename L a k s (^∃ p) = ^∃ (rename L a k s p) := rename_exs a k s hp
example (a k s x : V) : termRename L a k s (^#x) = ^#x := termRename_bvar a k s x
example (a k s x : V) : termRename L a k s (^&x) = ^&(renameIndex a k s x) := termRename_fvar a k s x
