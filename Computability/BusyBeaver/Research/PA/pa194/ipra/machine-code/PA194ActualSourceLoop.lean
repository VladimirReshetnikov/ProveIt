import PA194ModelSourceLoop
import PA194SourceDynamicLoop
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualSourceLoop
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelSourceLoop PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch
open PA194SourceControllerCode PA194SourceDynamicLoop PA194SourceSite25Physical PA194SourceRegisterRelation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def quad : Code 1 := unary step (unary step (unary step (unary step (.proj 0))))
def args (r : Fin 9 → M) : Fin 11 → M := ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,(0 : M),(0 : M)]
theorem sourceEq (r : Fin 9 → M) (tail : M) : sourceState 27 (args r) tail = PA194ModelSourceLoop.source r tail := by
  simp [sourceState,regsOfArgs,args,PA194ModelSourceLoop.source,PA194SourceRegisterRelation.pack]
theorem modelQuad (x : M) : F quad (fun _ => x) = F step ![F step ![F step ![F step ![x]]]] := by
  have hv (z : M) : (![z] : Fin 1 → M) = fun _ => z := by
    funext i; fin_cases i <;> rfl
  simp only [quad,modelUnary,modelProjection,hv]
theorem oneLoop (r : Fin 9 → M) (tail m : M) (hm : r 0 = m+1) :
    F quad (fun _ => PA194ModelSourceLoop.source r tail) = PA194ModelSourceLoop.source
      (Function.update (Function.update (Function.update r 0 m) 6 (r 6+1)) 8 (r 8+1)) tail := by
  have htail : args r 10 = F PA194OneSpareReturn.repeatOutput ![(0 : M),(0 : M)] := by
    rw [PA194OneSpareReturn.modelOutputZero]
    rfl
  have harg : args r 0 = m+1 := by simpa [args] using hm
  obtain ⟨c0,c1,c2,hsource,hphysical⟩ := fourSteps (0 : M) tail (0 : M) m (args r) harg htail
  have hout : sourceState 27
      (PA194Site29DynamicOutput.updated (PA194Site28DynamicOutput.updated (Function.update (args r) 0 m) (0 : M)) ((0 : M)+1)) tail =
      PA194ModelSourceLoop.source (Function.update (Function.update (Function.update r 0 m) 6 (r 6+1)) 8 (r 8+1)) tail := by
    simp [sourceState,regsOfArgs,PA194ModelSourceLoop.source,PA194SourceRegisterRelation.pack,PA194Site29DynamicOutput.updated,PA194Site28DynamicOutput.updated,args,Function.update]
  rw [sourceEq] at hsource
  rw [hout] at hsource
  rw [modelQuad]
  exact hsource
theorem sourceIteration (r : Fin 9 → M) (tail steps : M) (h : steps ≤ r 0) :
    F (iterCode quad) ![steps,PA194ModelSourceLoop.source r tail] =
      PA194ModelSourceLoop.source (PA194ModelSourceLoop.running r steps) tail := by
  apply PA194ModelSourceLoop.sourceIteration quad r tail steps
  · intro v m hm
    exact oneLoop v tail m hm
  · exact h
#print axioms modelQuad
#print axioms oneLoop
#print axioms sourceIteration
end models
end PA194ActualSourceLoop
