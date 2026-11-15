import PA194ContextExsElimCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextExsWitnessCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextExsElimCode PA194ContextAllCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Branch form matching the usual shifted-context witness elimination. -/
noncomputable def contextExsElimWitness (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert (∃⁰ p) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼p.free) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  have he : insert q.shift (insert (∼p.free) Γ.shift) = insert (∼p).free (insert q Γ).shift := by
    rw [Sequent.shift_insert]
    apply Sequent.ext
    intro x
    simp only [Sequent.mem_insert_iff]
    have hn : (∼p).free = ∼p.free := by simp [Bootstrapping.Semiformula.free]
    rw [hn]
    tauto
  exact contextExsElimProof T Γ p q de (TDerivation.cast he db)

@[simp] theorem contextExsElimWitness_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert (∃⁰ p) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼p.free) Γ.shift)) :
    (contextExsElimWitness T Γ p q de db).val = contextExsElimCode p.val q.val Γ.val de.val db.val := by
  simp [contextExsElimWitness]

#print axioms contextExsElimWitness
#print axioms contextExsElimWitness_val
end models
end PA194ContextExsWitnessCode
