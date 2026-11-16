import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite3661
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194SeedFirstSite3671Suffix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OneSpareReturn PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem firstSuffix :
    let seed := PA194SeedSecondRound.afterRound (M := M)
    let r : Fin 9 → M := fun i => seed ⟨i.val,by omega⟩
    let n := F Code.succ (fun _ => PA194SeedSecondRound.countAfterDrain (M := M))
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let n42 := n+r 7
    let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
    let n45 := n42+r42 6
    let args := PA194ActualLoopOrbit.frameArgs r45 n45 (seed 9)
    physicalArgs args 10 = F repeatOutput ![n45,(0 : M)] := by
  dsimp only
  simp [PA194RegisterPermutation.physicalArgs,PA194RegisterPermutation.inputOrder,
    PA194ActualLoopOrbit.frameArgs,Function.update]
#print axioms firstSuffix
end models
end PA194SeedFirstSite3671Suffix
