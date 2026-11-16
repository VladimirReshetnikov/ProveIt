import PA194ModelRestoreSource
import PA194SourceSite31TransferLoop
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194ActualRestoreSource
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelRestoreSource PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SourceSite25Physical PA194RegisterPermutation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def triple : Code 1 := unary step (unary step (unary step (.proj 0)))
def args (r : Fin 9 → M) : Fin 11 → M := ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,(0 : M),(0 : M)]
theorem sourceEq (r : Fin 9 → M) (tail : M) : PA194SourceSite31Controller.sourceState 31 (args r) tail = PA194ModelRestoreSource.source r tail := by
  simp [PA194SourceSite31Controller.sourceState,PA194SourceSite31Controller.regsOfArgs,regsOfArgs,args,PA194ModelRestoreSource.source,PA194SourceRegisterRelation.pack]
theorem modelTriple (x : M) : F triple (fun _ => x) = F step ![F step ![F step ![x]]] := by
  have hv (z : M) : (![z] : Fin 1 → M) = fun _ => z := by
    funext i; fin_cases i <;> rfl
  simp only [triple,modelUnary,modelProjection,hv]
theorem oneLoop (r : Fin 9 → M) (tail m : M) (hm : r 6 = m+1) :
    F triple (fun _ => PA194ModelRestoreSource.source r tail) = PA194ModelRestoreSource.source
      (Function.update (Function.update r 0 (r 0+1)) 6 m) tail := by
  have htail : physicalArgs (args r) 10 = F PA194OneSpareReturn.repeatOutput ![(0 : M),(0 : M)] := by
    rw [PA194OneSpareReturn.modelOutputZero]
    rfl
  have harg : args r 6 = m+1 := by simpa [args] using hm
  obtain ⟨hsource,hphysical⟩ := PA194SourceSite31TransferLoop.oneLoop (0 : M) (0 : M) tail m (args r) htail harg
  have hout : PA194SourceSite31Controller.sourceState 31 (Function.update (PA194Site31OutputFile.updated (args r) (0 : M)) 6 m) tail =
      PA194ModelRestoreSource.source (Function.update (Function.update r 0 (r 0+1)) 6 m) tail := by
    simp [PA194SourceSite31Controller.sourceState,PA194SourceSite31Controller.regsOfArgs,regsOfArgs,PA194ModelRestoreSource.source,PA194SourceRegisterRelation.pack,
      PA194Site31OutputFile.updated,args,Function.update]
  rw [sourceEq] at hsource
  rw [hout] at hsource
  rw [modelTriple]
  exact hsource

theorem sourceIteration (r : Fin 9 → M) (tail steps : M) (h : steps ≤ r 6) :
    F (iterCode triple) ![steps,PA194ModelRestoreSource.source r tail] =
      PA194ModelRestoreSource.source (PA194ModelRestoreSource.running r steps) tail := by
  apply PA194ModelRestoreSource.sourceIteration triple r tail steps
  · intro v m hm
    exact oneLoop v tail m hm
  · exact h
#print axioms modelTriple
#print axioms oneLoop
#print axioms sourceIteration
end models
end PA194ActualRestoreSource
