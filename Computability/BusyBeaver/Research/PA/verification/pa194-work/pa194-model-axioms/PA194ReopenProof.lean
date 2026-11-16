import PA194FullyClosedSeparation
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ReopenProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource
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

/-- Specialize one internally closed formula back to its original open form. -/
noncomputable def reopenProof (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨closeOne p, closeOne_scoped p hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨p, hp⟩ : Formula M SourceL) := by
  have hb := bindFormula_scope_open p hp
  let body : Semiformula M SourceL 1 := ⟨bindFormula 0 p, by simpa using hb.1⟩
  have hall : T ⊢! ∀⁰ body := by
    convert d using 1
    ext
    rfl
  have hshift : T ⊢! ∀⁰ body.shift := by
    simpa using TProof.shift hall
  have hopen : T ⊢! body.free := TProof.specialize hshift (Semiterm.fvar 0)
  have heq : body.free = (⟨p,hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa [body] using hb.2
  exact heq ▸ hopen

theorem reopen_provable (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 0 p)
    (h : Provable T.theory (closeOne p)) : Provable T.theory p := by
  let a : Formula M SourceL := ⟨p, hp⟩
  let b : Formula M SourceL := ⟨closeOne p, closeOne_scoped p hp⟩
  have h' : T ⊢ b := (TProvable.iff_provable).2 h
  have h'' : T ⊢ a := ⟨reopenProof T p hp h'.get⟩
  exact (TProvable.iff_provable).1 h''

theorem reopen_iterated_provable (T : InternalTheory M SourceL) (n p : M)
    (hp : IsSemiformula SourceL 0 p)
    (h : Provable T.theory (modelClose n p)) : Provable T.theory p := by
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  have hdef : 𝚺₁-Predicate (fun i : M => i ≤ n → Provable T.theory (modelClose (n - i) p)) := by
    definability
  have hi : ∀ i : M, i ≤ n → Provable T.theory (modelClose (n - i) p) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction with
    | hP => exact hdef
    | zero => simpa [modelClose_zero] using h
    | succ i ih =>
      intro hle
      have hil : i ≤ n := le_trans (by simp) hle
      have hlt : i < n := lt_of_lt_of_le (lt_add_one i) hle
      have old := ih hil
      have heq : n - (i+1) + 1 = n-i := by simpa using sub_succ_add_succ hlt (0 : M)
      rw [← heq, modelClose_succ] at old
      exact reopen_provable T _ (modelClose_scope _ p hp) old
  simpa [modelClose_zero] using hi n (le_refl n)

theorem separation_root_provable (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (ha : fullyClosedSeparation p ∈ T.theory.Δ₁Class (V := M)) :
    Provable T.theory (sepRoot p) := by
  have hs := sepRoot_scoped p hp
  let a : Formula M SourceL := ⟨fullyClosedSeparation p, (fullyClosedSeparation_sentence p hp).1⟩
  have h : Provable T.theory (fullyClosedSeparation p) := by
    have hd : T ⊢ a := ⟨TProof.byAxm ha⟩
    exact TProvable.iff_provable.mp hd
  exact reopen_iterated_provable T (formulaFreeBound (sepRoot p)) (sepRoot p) hs h

#print axioms separation_root_provable
#print axioms reopen_iterated_provable
#print axioms reopenProof
#print axioms reopen_provable
end models
end PA194ReopenProof
