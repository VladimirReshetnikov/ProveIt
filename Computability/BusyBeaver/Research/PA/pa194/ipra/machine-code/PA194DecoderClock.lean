import PA194DecoderSynchronization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194DecoderClock
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194IteratedSimulation PA194CumulativeClock PA194ClockInvariantDefinable PA194ControllerRunAdd PA194DecoderRoundCode
noncomputable def totalClock : Code 2 := clock (iterate advance) roundClock
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

theorem accumulate (start steps : M) :
    F PA194SourceControllerCode.run ![F totalClock ![steps,start],start] = F (iterate advance) ![steps,start] := by
  let f : M → M := fun n => F PA194SourceControllerCode.run ![F totalClock ![n,start],start]
  let g : M → M := fun n => F (iterate advance) ![n,start]
  let c : M → M := fun n => F totalClock ![n,start]
  have hc : 𝚺₁-Function₁ c := bindBinary _ start (binaryCodeDef (M := M) totalClock)
  have hf : 𝚺₁-Function₁ f := composeUnary _ c (bindBinary _ start (binaryCodeDef (M := M) PA194SourceControllerCode.run)) hc
  have hg : 𝚺₁-Function₁ g := bindBinary _ start (binaryCodeDef (M := M) (iterate advance))
  have hp : 𝚺₁-Predicate (fun n : M => f n = g n) := equalPred f g hf hg
  have main : ∀ n : M, f n = g n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero =>
      change F PA194SourceControllerCode.run ![F totalClock ![(0 : M),start],start] = F (iterate advance) ![0,start]
      rw [totalClock,clockZero]
      change F (iterate step) ![(0 : M),start] = F (iterate advance) ![0,start]
      rw [iterateZero,iterateZero]
    | succ n ih =>
      change F PA194SourceControllerCode.run ![F totalClock ![n+1,start],start] = F (iterate advance) ![n+1,start]
      rw [totalClock,clockSucc]
      have hv : (fun _ : Fin 1 => F (iterate advance) ![n,start]) = ![F (iterate advance) ![n,start]] := by
        funext i; fin_cases i; rfl
      rw [hv]
      change F (iterate step) ![F totalClock ![n,start]+F roundClock ![F (iterate advance) ![n,start]],start] = _
      rw [PA194ControllerRunAdd.iterateAdd]
      change F PA194SourceControllerCode.run ![F roundClock ![g n],f n] = F (iterate advance) ![n+1,start]
      rw [ih,←advanceModel,iterateSucc]
  exact main steps
#print axioms accumulate
end models
end PA194DecoderClock
