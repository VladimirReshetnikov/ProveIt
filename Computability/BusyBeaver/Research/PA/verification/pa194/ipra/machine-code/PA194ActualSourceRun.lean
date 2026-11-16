import PA194ActualSourceLoop
import PA194ModelLoopFour
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualSourceRun
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction PackedDecoderModel PA194GenericRightScan PA194Site28CarryCell PA194Stepper PA194ModelLoopIteration PA194ModelSourceLoop PA194ActualSourceLoop PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch
open PA194SourceControllerCode
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem sourceRunIteration (r : Fin 9 → M) (tail steps : M) (h : steps ≤ r 0) :
    F PA194SourceControllerCode.run ![(steps+steps)+(steps+steps),PA194ModelSourceLoop.source r tail] =
      PA194ModelSourceLoop.source (PA194ModelSourceLoop.running r steps) tail := by
  have hgroup := PA194ModelLoopFour.groupFour (M := M) PA194SourceControllerCode.step steps (PA194ModelSourceLoop.source r tail)
  change F PA194SourceControllerCode.run ![(steps+steps)+(steps+steps),PA194ModelSourceLoop.source r tail] =
    F (iterCode quad) ![steps,PA194ModelSourceLoop.source r tail] at hgroup
  exact hgroup.trans (PA194ActualSourceLoop.sourceIteration r tail steps h)
theorem reachesZero (r : Fin 9 → M) (tail : M) :
    let n := r 0
    let out := PA194ModelSourceLoop.running r n
    F PA194SourceControllerCode.run ![(n+n)+(n+n),PA194ModelSourceLoop.source r tail] = PA194ModelSourceLoop.source out tail ∧
      out 0 = (0 : M) ∧ out 6 = r 6+n ∧ out 8 = r 8+n := by
  dsimp only
  constructor
  · exact sourceRunIteration r tail (r 0) le_rfl
  · constructor
    · simp only [PA194ModelSourceLoop.running,Function.update_of_ne,Function.update_self]
      rw [modelSubAsTsub]
      simp
    · constructor <;> simp [PA194ModelSourceLoop.running]
#print axioms sourceRunIteration
#print axioms reachesZero
end models
end PA194ActualSourceRun
