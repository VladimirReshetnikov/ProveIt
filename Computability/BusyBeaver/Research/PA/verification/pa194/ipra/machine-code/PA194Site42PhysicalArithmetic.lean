import DiophantineConsistency.PRASubAddition
import PA194SourceSite42TransferStep
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace PA194Site42PhysicalArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition PRASubtraction PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194RegisterPermutation PA194OneSpareReturn PA194SourceSite31Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def sourceArgsAt (args : Fin 11 → M) (j : M) : Fin 11 → M :=
  Function.update (Function.update args 7 (F subCode ![args 7,j])) 8 (args 8+j)
noncomputable def argsAt (args : Fin 11 → M) (count j : M) : Fin 11 → M :=
  Function.update (sourceArgsAt args j) 10 (F repeatOutput ![count+j,(0 : M)])

theorem suffixAt (args : Fin 11 → M) (count j : M) :
    physicalArgs (argsAt args count j) 10 = F repeatOutput ![count+j,(0 : M)] := by
  simp [physicalArgs,inputOrder,argsAt]

theorem advance (args : Fin 11 → M) (count j : M) (hj : j+1 ≤ args 7) :
    ∃ m : M, argsAt args count j 7 = m+1 ∧
      PA194Site43OutputFile.updated (Function.update (argsAt args count j) 7 m) (count+j) = argsAt args count (j+1) := by
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hj
  have h1 : F subCode ![args 7,j+1] = d := by rw [hd]; exact modelSubAdd (j+1) d
  have h0 : F subCode ![args 7,j] = d+1 := by
    rw [hd]
    have heq : (j+1)+d = j+(d+1) := by ac_rfl
    rw [heq]; exact modelSubAdd j (d+1)
  refine ⟨d,?_,?_⟩
  · simp [argsAt,sourceArgsAt,h0]
  · funext i
    fin_cases i <;> simp [argsAt,sourceArgsAt,PA194Site43OutputFile.updated,h0,h1,add_assoc]
    rw [←modelAddOne]
    change F repeatOutput ![(count+j)+1,(0 : M)] = F repeatOutput ![count+(j+1),(0 : M)]
    rw [add_assoc]
theorem modelStep (args : Fin 11 → M) (count k tail j : M) (hj : j+1 ≤ args 7) :
    ∃ c42 c43 : M,
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        PA194SourceSite31Controller.sourceState 42 (argsAt args count j) tail]]] =
          PA194SourceSite31Controller.sourceState 42 (argsAt args count (j+1)) tail ∧
      F PA194Stepper.stepper ![modelNumeral M 36,
        F PA194Stepper.stepper ![c43,F PA194Stepper.stepper ![c42,
          physicalFrame 42 (((k+j)+1)+1) (argsAt args count j)]]] =
        physicalFrame 42 ((((k+j)+1)+1)+1) (argsAt args count (j+1)) := by
  obtain ⟨m,hm,hnext⟩ := advance args count j hj
  have hs := suffixAt args count j
  have ht := PA194SourceSite42TransferStep.transferStep (k+j) (count+j) tail m (argsAt args count j) hm hs
  dsimp only at ht
  obtain ⟨c42,c43,hc,hp⟩ := ht
  rw [hnext] at hc hp
  exact ⟨c42,c43,hc,hp⟩
#print axioms modelStep
#print axioms suffixAt
#print axioms advance
end models
end PA194Site42PhysicalArithmetic
