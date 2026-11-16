import PA194Site31SentenceVectors
import PA194ActualLoopOrbit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace PA194Site31SentenceClock
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194StartupSentence PA194Site31Sentence PA194Site31SentenceVectors
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
def regs (e : Fin 13 → M) : Fin 9 → M := fun i => e ⟨i.val,by have h := i.isLt; omega⟩
def args (e : Fin 13 → M) : Fin 11 → M := PA194ActualLoopOrbit.frameArgs (regs e) (e 11) (e 12)
theorem physicalArgsEval (e : Fin 13 → M) :
    physicalArgs (args e) =
      ![e 2,e 8,e 1,e 4,e 3,e 7,e 0,e 5,e 6,e 12,F PA194OneSpareReturn.repeatOutput ![e 11,(0 : M)]] := by
  funext i
  fin_cases i <;> simp [physicalArgs,inputOrder,args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,regs]

theorem valClock (e : Fin 13 → M) :
    Semiterm.val e Empty.elim PA194Site31Sentence.clock24 =
      PA194Site31PhysicalClock.clock24 (e 10) (e 11) (args e) := by
  have hv := physicalArgsEval e
  dsimp only [PA194Site31PhysicalClock.clock24]
  rw [hv]
  have v0 : V 0 = R 2 := rfl
  have v1 : V 1 = R 8 := rfl
  have v2 : V 2 = R 1 := rfl
  have v3 : V 3 = R 4 := rfl
  have v4 : V 4 = R 3 := rfl
  have v5 : V 5 = R 7 := rfl
  have hrev := valRev e
  simp only [v0,v1,v2,v3,v4,v5] at hrev
  simp only [PA194Site31Sentence.clock24,croot,c71,pass,scan,c15,rc,cr,c6,
    plus1,twice,A,PA194StartupSentence.valApp2,Semiterm.val_func]
  simp only [v0,v1,v2,v3,v4,v5,Function.comp_def]
  rw [hrev]
  simp [base,b,H6,H5,H4,H3,H2,H1,H0,plus1,twice,A,V,R,k,c,
    PA194StartupSentence.valApp2,PA194StartupSentence.valState,PA194StartupSentence.valOne,
    Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  rfl

#print axioms physicalArgsEval
#print axioms valClock
end models
end PA194Site31SentenceClock
