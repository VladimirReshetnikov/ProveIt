import ZFCinPA.ModelCodedRenamingAxioms

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LeanProofs.ZFCinPA.ModelCodedRenamingAxioms
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingAxioms.ofList_class_iff
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingAxioms.schemaRecognizer_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingAxioms.zf_axiom_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingAxioms.zfc_axiom_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingAxioms.zf_axiom_rename
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingAxioms.zfc_rename_mem

example (a k s p : V) (hp : IsFormula ℒₛₑₜ p)
    (hax : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ a k s p = p := zf_axiom_rename a k s hp hax
example (a k s p : V) (hp : IsFormula ℒₛₑₜ p)
    (hax : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ a k s p = p := zfc_axiom_rename a k s hp hax
example (a k s p : V) (hp : IsFormula ℒₛₑₜ p)
    (hax : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ a k s p ∈ (𝗭𝗙 : SetTheory).Δ₁Class := zf_rename_mem a k s hp hax
example (a k s p : V) (hp : IsFormula ℒₛₑₜ p)
    (hax : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ a k s p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := zfc_rename_mem a k s hp hax
example (p : V) (hp : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) : shift ℒₛₑₜ p = p :=
  zf_axiom_shift_fixed hp
example (p : V) (hp : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) : shift ℒₛₑₜ p = p :=
  zfc_axiom_shift_fixed hp
