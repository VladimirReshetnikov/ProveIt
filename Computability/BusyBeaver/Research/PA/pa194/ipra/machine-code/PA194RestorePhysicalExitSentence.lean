import PA194RestorePhysicalExitCode
import PA194StartupSentence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable section
namespace PA194RestorePhysicalExitSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header PA194StartupSentence
abbrev T := TermN 13
def A (a b : T) : T := app2 addCode a b
def p (a b : T) : T := app2 pairCode a b
def r (i : Fin 9) : T := .bvar ⟨i.val,by have h := i.isLt; omega⟩
def tail : T := .bvar 9
def k : T := .bvar 10
def n : T := .bvar 11
def spare : T := .bvar 12
def sourceT (reg : Fin 9 → T) : T :=
  p (state 31) (p (reg 0) (p (reg 1) (p (reg 2) (p (reg 3) (p (reg 4) (p (reg 5) (p (reg 6) (p (reg 7) (p (reg 8) tail)))))))))
def pack (g count s control : T) : T := p g (p count (p s control))
def gap : T := A (A (A k one) one) one
def resultRegs : Fin 9 → T := ![A (r 0) (r 6),r 1,r 2,r 3,r 4,r 5,app2 subCode (r 6) (r 6),r 7,r 8]
def exitRegs : Fin 9 → T := ![A (resultRegs 0) one,resultRegs 1,resultRegs 2,resultRegs 3,resultRegs 4,
  resultRegs 5,resultRegs 6,resultRegs 7,resultRegs 8]
def k' : T := A k (r 6)
def n' : T := A n (r 6)
def e31 : Fin 13 → T := ![resultRegs 0,resultRegs 1,resultRegs 2,resultRegs 3,resultRegs 4,
  resultRegs 5,resultRegs 6,resultRegs 7,resultRegs 8,tail,A k' one,n',spare]
def exitArgs : Fin 11 → T := ![exitRegs 0,exitRegs 1,exitRegs 2,exitRegs 3,exitRegs 4,exitRegs 5,
  exitRegs 6,exitRegs 7,exitRegs 8,spare,app2 PA194OneSpareReturn.repeatOutput (.func Code.succ ![n']) (state 0)]
def input : T := pack gap n spare (sourceT r)
def output : T := pack (A gap (r 6)) (A n' one) spare (sourceT exitRegs)
def cost : Code 1 := PA194RestorePhysicalCost.cost
def frame31 : Code 1 := PA194ModelLoopFrameAt.frameAt 31 PA194ControllerLoopFrame.readers
def frame34 : Code 1 := PA194ModelLoopFrameAt.frameAt 34 PA194ControllerLoopFrame.readers
def unaryTerm (c : Code 1) (x : T) : T := .func c ![x]
def orbitClock : T := app2 (timeCode (PA194ModelTransferState.next PA194ActualRestoreSource.triple) cost) (r 6) input
def finalClock : T := A (A orbitClock (.func PA194Site31CodedClock.clockCode e31))
  (.func PA194Site32ZeroClockCode.clockCode (Fin.cons k' exitArgs))
def lhs : T := app2 PA194Stepper.stepper finalClock (unaryTerm frame31 input)
def rhs : T := unaryTerm frame34 output
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  let rs : Fin 9 → M := fun i => e ⟨i.val,by have h := i.isLt; omega⟩
  have h := PA194RestorePhysicalExitCode.completeExit rs (e 9) (e 10) (e 11) (e 12)
  dsimp only at h
  have hargs : Fin.cons (e 10+rs 6)
      (PA194Site31OutputFile.updated
        (PA194ActualLoopOrbit.frameArgs (PA194ModelRestoreSource.running rs (rs 6)) (e 11+rs 6) (e 12)) (e 11+rs 6)) =
      (![e 10+e 6,e 0+e 6+1,e 1,e 2,e 3,e 4,e 5,F subCode ![e 6,e 6],e 7,e 8,e 12,
        F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => e 11+e 6),(0 : M)]] : Fin 12 → M) := by
    funext i
    fin_cases i <;> simp [rs,PA194Site31OutputFile.updated,PA194ActualLoopOrbit.frameArgs,
      PA194ActualSourceLoop.args,PA194ModelRestoreSource.running,Function.update] <;> rfl
  rw [hargs] at h
  have hv12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : T) :
      (fun i : Fin 12 => Semiterm.val e Empty.elim (![ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 ] i)) = ![ Semiterm.val e Empty.elim a0, Semiterm.val e Empty.elim a1, Semiterm.val e Empty.elim a2, Semiterm.val e Empty.elim a3, Semiterm.val e Empty.elim a4, Semiterm.val e Empty.elim a5, Semiterm.val e Empty.elim a6, Semiterm.val e Empty.elim a7, Semiterm.val e Empty.elim a8, Semiterm.val e Empty.elim a9, Semiterm.val e Empty.elim a10, Semiterm.val e Empty.elim a11 ] := by
    funext i; fin_cases i <;> rfl
  have hv13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : T) :
      (fun i : Fin 13 => Semiterm.val e Empty.elim (![ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 ] i)) = ![ Semiterm.val e Empty.elim a0, Semiterm.val e Empty.elim a1, Semiterm.val e Empty.elim a2, Semiterm.val e Empty.elim a3, Semiterm.val e Empty.elim a4, Semiterm.val e Empty.elim a5, Semiterm.val e Empty.elim a6, Semiterm.val e Empty.elim a7, Semiterm.val e Empty.elim a8, Semiterm.val e Empty.elim a9, Semiterm.val e Empty.elim a10, Semiterm.val e Empty.elim a11, Semiterm.val e Empty.elim a12 ] := by
    funext i; fin_cases i <;> rfl
  simp [lhs,rhs,input,output,pack,sourceT,p,A,gap,k,n,spare,tail,r,resultRegs,exitRegs,k',n',e31,exitArgs,orbitClock,finalClock,unaryTerm,cost,frame31,frame34,
    PA194StartupSentence.valApp2,PA194StartupSentence.valState,PA194StartupSentence.valOne,
    Semiterm.val_bvar,Semiterm.val_func,Function.comp_def,hv12,hv13,rs,PA194ModelLoopState.packed,
    PA194ModelRestoreSource.source,PA194ModelRestoreSource.running,Function.update,PA194Site31OutputFile.updated,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,modelPairCode] at h ⊢
  exact h
end models
theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs := nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194RestorePhysicalExitSentence
