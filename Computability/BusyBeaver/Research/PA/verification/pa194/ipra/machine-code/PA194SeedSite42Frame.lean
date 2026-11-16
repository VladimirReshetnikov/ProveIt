import PA194SeedSite42Values
import PA194ModelTransfer42Source
import PA194ModelTransfer45Source
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SeedSite42Frame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeedFrameAlignment PA194StartupSourceFrame PA194SeedToFirstSite35 PA194ActualLoopOrbit PA194RegisterPermutation TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem firstFrame :
    let seed := PA194SeedSecondRound.afterRound (M := M)
    let regs : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
    let count := Structure.func (L := language) Code.succ (fun _ => PA194SeedSecondRound.countAfterDrain (M := M))
    PA194ActualLoopOrbit.frameArgs regs count (seed 9) = seed := by
  dsimp only
  let seed := PA194SeedSecondRound.afterRound (M := M)
  have hs : seed 10 = Structure.func (L := language) PA194OneSpareReturn.repeatOutput
      ![Structure.func (L := language) Code.succ (fun _ => PA194SeedSecondRound.countAfterDrain (M := M)),(0 : M)] := by
    simp [seed,PA194SeedSecondRound.afterRound,PA194Site35OutputFile.updated]
  funext i
  fin_cases i <;> simp [PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args] <;> exact hs.symm
#print axioms firstFrame
end models
end PA194SeedSite42Frame
