import PA194DecoderClock
import PA194UnpairExit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194DecoderComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194DecoderSynchronization PA194DecoderClock PA194UnpairExit
open PA194DiagonalIteration PA194DiagonalLink PA194MachineProjections
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decode (initial : Fin 11 → M) (tail : M) :
    let start := sourceState 34 initial tail
    let p := cantor (initial 6) (initial 7)+initial 8
    ∃ x y : M,
      F PA194SourceControllerCode.run ![F totalClock ![initial 8,start]+1,start] =
        sourceState 42 (argsAt initial x y 0) tail ∧
      F fixedFirst ![p] = x ∧ F fixedSecond ![p] = y := by
  let start := sourceState 34 initial tail
  let p := cantor (initial 6) (initial 7)+initial 8
  let seed := pair (initial 6) (initial 7)
  obtain ⟨x,y,left,hs,hcount,hpair⟩ := synchronization initial tail (initial 8) (le_refl _)
  have hzero : left = (0 : M) := by
    apply add_right_cancel (b := initial 8)
    simpa only [zero_add] using hcount
  subst left
  let out := argsAt initial x y (0 : M)
  have h8 : out 8 = (0 : M) := by simp [out,argsAt]
  have hexit := exitTo42 out tail h8
  have hclock := accumulate start (initial 8)
  have hproj := iterationProjects seed (initial 8)
  change F fixedFirst ![F scoreCode ![seed]+initial 8] = pi₁ (F PA194DiagonalCode.run ![initial 8,seed]) ∧
    F fixedSecond ![F scoreCode ![seed]+initial 8] = pi₂ (F PA194DiagonalCode.run ![initial 8,seed]) at hproj
  rw [modelScore] at hproj
  have hscores : cantor (pi₁ seed) (pi₂ seed)+initial 8 = p := by simp [seed,p,pi₁_pair,pi₂_pair]
  rw [hscores,←hpair,pi₁_pair,pi₂_pair] at hproj
  refine ⟨x,y,?_,hproj.1,hproj.2⟩
  change F (iterate step) ![F totalClock ![initial 8,start]+1,start] = sourceState 42 out tail
  rw [iterateSucc]
  change F step ![F PA194SourceControllerCode.run ![F totalClock ![initial 8,start],start]] = _
  rw [hclock,hs]
  exact hexit
theorem decodeFromZero (initial : Fin 11 → M) (tail : M)
    (hx : initial 6 = (0 : M)) (hy : initial 7 = (0 : M)) :
    let start := sourceState 34 initial tail
    ∃ x y : M,
      F PA194SourceControllerCode.run ![F totalClock ![initial 8,start]+1,start] =
        sourceState 42 (argsAt initial x y 0) tail ∧
      F fixedFirst ![initial 8] = x ∧ F fixedSecond ![initial 8] = y := by
  have hp : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  have h := decode initial tail
  simpa only [hx,hy,hp,zero_add] using h
#print axioms decodeFromZero
#print axioms decode
end models
end PA194DecoderComplete
