import PA194ReopenProof
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194CloseProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ReopenProof
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundClosedLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Generalize a proof of p into a proof of one universal closure. -/
noncomputable def closeProof (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨p, hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨closeOne p, closeOne_scoped p hp⟩ : Formula M SourceL) := by
  have hb := bindFormula_scope_open p hp
  let body : Semiformula M SourceL 1 := ⟨bindFormula 0 p, by simpa using hb.1⟩
  have heq : body.free = (⟨p,hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa [body] using hb.2
  have hbody : T ⊢! body.free := heq.symm ▸ d
  have hc : T ⊢! ∀⁰ body := TProof.all hbody
  convert hc using 1
  ext
  rfl

theorem close_provable (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 0 p)
    (h : Provable T.theory p) : Provable T.theory (closeOne p) := by
  let a : Formula M SourceL := ⟨p, hp⟩
  let b : Formula M SourceL := ⟨closeOne p, closeOne_scoped p hp⟩
  have h' : T ⊢ a := (TProvable.iff_provable).2 h
  have h'' : T ⊢ b := ⟨closeProof T p hp h'.get⟩
  exact (TProvable.iff_provable).1 h''

theorem close_iterated_provable (T : InternalTheory M SourceL) (n p : M)
    (hp : IsSemiformula SourceL 0 p)
    (h : Provable T.theory p) : Provable T.theory (modelClose n p) := by
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  have hdef : 𝚺₁-Predicate (fun i : M => Provable T.theory (modelClose i p)) := by definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => simpa [modelClose_zero] using h
  | succ i ih =>
    rw [modelClose_succ]
    exact close_provable T _ (modelClose_scope i p hp) ih

theorem close_iterated_provable_iff (T : InternalTheory M SourceL) (n p : M)
    (hp : IsSemiformula SourceL 0 p) :
    Provable T.theory (modelClose n p) ↔ Provable T.theory p :=
  ⟨reopen_iterated_provable T n p hp, close_iterated_provable T n p hp⟩

#print axioms closeProof
#print axioms close_provable
#print axioms close_iterated_provable
#print axioms close_iterated_provable_iff
end models
end PA194CloseProof
