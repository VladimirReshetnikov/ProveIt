import ZFCinPA.ValidatorSeedSourceBasis222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open ValidatorSeedSourceBasis222 ValidatorFullSeedTheory222 ValidatorSourceFullSeed222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Literal graph correctness is total; only the full-body equation needs typing. -/
example (out k : V) : (V ⊧/![out,k] seedInstanceGraph.val) ↔ out=seedInstanceCode k := by simp
example (out k : V) : (V ⊧/![out,k] closedSeedGraph.val) ↔ out=closedSeedCode k := by simp
example (out k : V) : (V ⊧/![out,k] openSeedProofGraph.val) ↔ out=openSeedProofCode k := by simp
example (k : V) (hk : IsSemiformula ℒₛₑₜ 2 k) :
    seedInstanceCode k=fullSeedBodyVal k := seedInstanceCode_eq hk
example (K : Semiformula V ℒₛₑₜ 2) : SeedR (closedSeedCode K.val) := closedSeed_recognized K
example (K : Semiformula V ℒₛₑₜ 2) :
    closedSeedCode K.val∈seedTheory.Δ₁Class := closedSeed_mem K
example (K : Semiformula V ℒₛₑₜ 2) :
    Proof seedTheory (openSeedProofCode K.val) (fullSeedBody K).val := openSeed_isProof K
example (K : Semiformula V ℒₛₑₜ 2) :
    (openSeedProof K).val=openSeedProofCode K.val := rfl
example : Source V ⊢! fullSeedBody (⊥ : Semiformula V ℒₛₑₜ 2) := openSeedProof ⊥
example : Source V ⊢! fullSeedBody (⊤ : Semiformula V ℒₛₑₜ 2) := openSeedProof ⊤

/-- A nested matrix with sparse free parameters, not a closed-matrix specialization. -/
def sparseMatrix : SetTheorySemiproposition 2 :=
  ∀⁰ (FirstOrder.Semiformula.rel Language.Mem.mem
    ![(#0 : SyntacticSemiterm ℒₛₑₜ 3),&17] ⋏
      FirstOrder.Semiformula.nrel Language.Eq.eq ![#2,&31])
example : Source V ⊢! fullSeedBody (⌜sparseMatrix⌝ : Semiformula V ℒₛₑₜ 2) :=
  openSeedProof _
example (K : Semiformula V ℒₛₑₜ 2) :
    Source V ⊢! fullSeedBody K.shift.shift := openSeedProof _

/-- Empty and singleton targets are source proofs, including arbitrary internal terms. -/
example : Source V ⊢ ∃⁰ emptyBody := empty_object
example (t : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ singletonBody t := singleton_object t
example (t : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ tagBody t := tagged_nonempty t
example (x : V) : Source V ⊢ ∃⁰ singletonBody (Bootstrapping.Semiterm.fvar (x+31)) := singleton_object _
example (t : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ tagBody t.shift.shift := tagged_nonempty _
example : Source V ⊢ ∀⁰ ∃⁰ memTerm
    (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) := all_tagged_nonempty
example : Source V ⊢ (∃⁰ (emptyBody ⋏ (∃⁰ memTerm
    (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)))) :=
  empty_marker_with_inhabited_tag
example : Provable seedTheory ((∃⁰ emptyBody : Formula V ℒₛₑₜ).val) :=
  TProvable.iff_provable.mp empty_object
example (t : Term V ℒₛₑₜ) : Provable seedTheory ((∃⁰ singletonBody t).val) :=
  TProvable.iff_provable.mp (singleton_object t)

/-- Exact bound/free slot controls: the marker is shifted past the new witness. -/
example (t : Term V ℒₛₑₜ) : singletonBody t=
    ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
      eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift.bShift) := rfl
example (t : Term V ℒₛₑₜ) : tagBody t=memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) := rfl
example : (emptyBody : Semiformula V ℒₛₑₜ 1).free=emptyAt (Bootstrapping.Semiterm.fvar 0) :=
  emptyBody_free
example : ((∃⁰ memTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)) :
    Semiformula V ℒₛₑₜ 1).free=∃⁰ tagBody (Bootstrapping.Semiterm.fvar 0) := tagQuantifier_free

#print axioms seedInstance_defined
#print axioms closedSeed_defined
#print axioms openSeedProof_defined
#print axioms seedInstanceCode_eq
#print axioms recognizer_parameter_bound
#print axioms closedSeed_recognized
#print axioms closedSeed_mem
#print axioms openSeed_isProof
#print axioms openSeedProof
#print axioms term_is_fvar
#print axioms emptyBody_free
#print axioms tagQuantifier_free
#print axioms empty_object
#print axioms singleton_object
#print axioms tagged_nonempty
#print axioms all_tagged_nonempty
#print axioms empty_marker_with_inhabited_tag
end LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222Checks
