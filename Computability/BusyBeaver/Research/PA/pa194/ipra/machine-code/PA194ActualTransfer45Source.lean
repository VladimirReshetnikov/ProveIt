import PA194ModelTransfer45Source
import PA194SourceSite45TransferStep
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194ActualTransfer45Source
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelTransfer45Source PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch
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
theorem sourceEq (r : Fin 9 → M) (tail : M) : PA194SourceSite31Controller.sourceState 45 (args r) tail = PA194ModelTransfer45Source.source r tail := by
  simp [PA194SourceSite31Controller.sourceState,PA194SourceSite31Controller.regsOfArgs,regsOfArgs,args,PA194ModelTransfer45Source.source,PA194SourceRegisterRelation.pack]
theorem modelTriple (x : M) : F triple (fun _ => x) = F step ![F step ![F step ![x]]] := by
  have hv (z : M) : (![z] : Fin 1 → M) = fun _ => z := by
    funext i; fin_cases i <;> rfl
  simp only [triple,modelUnary,modelProjection,hv]
theorem oneLoop (r : Fin 9 → M) (tail m : M) (hm : r 6 = m+1) :
    F triple (fun _ => PA194ModelTransfer45Source.source r tail) = PA194ModelTransfer45Source.source
      (Function.update (Function.update r 3 (r 3+1)) 6 m) tail := by
  have htail : physicalArgs (args r) 10 = F PA194OneSpareReturn.repeatOutput ![(0 : M),(0 : M)] := by
    rw [PA194OneSpareReturn.modelOutputZero]
    rfl
  have harg : args r 6 = m+1 := by simpa [args] using hm
  obtain ⟨_,_,hsource,_⟩ := PA194SourceSite45TransferStep.transferStep (0 : M) (0 : M) tail m (args r) harg htail
  have hout : PA194SourceSite31Controller.sourceState 45 (PA194Site46OutputFile.updated (Function.update (args r) 6 m) (0 : M)) tail =
      PA194ModelTransfer45Source.source (Function.update (Function.update r 3 (r 3+1)) 6 m) tail := by
    simp [PA194SourceSite31Controller.sourceState,PA194SourceSite31Controller.regsOfArgs,regsOfArgs,PA194ModelTransfer45Source.source,PA194SourceRegisterRelation.pack,
      PA194Site46OutputFile.updated,args,Function.update]
  rw [sourceEq] at hsource
  rw [hout] at hsource
  rw [modelTriple]
  exact hsource

theorem sourceIteration (r : Fin 9 → M) (tail steps : M) (h : steps ≤ r 6) :
    F (iterCode triple) ![steps,PA194ModelTransfer45Source.source r tail] =
      PA194ModelTransfer45Source.source (PA194ModelTransfer45Source.running r steps) tail := by
  apply PA194ModelTransfer45Source.sourceIteration triple r tail steps
  · intro v m hm
    exact oneLoop v tail m hm
  · exact h
#print axioms modelTriple
#print axioms oneLoop
#print axioms sourceIteration
end models
end PA194ActualTransfer45Source
