import PA194CompressedSourceFrame
import PA194RegisterLayout
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194RegisterRoot
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PRAExhaustion PA194SourceRegisters PA194SourceControllerCode
open PA194CompressedRootCode PA194CompressedSourceFrame PA194OneSpareReturn
open PA194BinaryDouble (unary modelUnary)
open PA194RegisterLayout PA194Path27Header PA194ZeroRuns PA194UnaryRuns PRASelectCode
open PA194RegisterFile PA194CompressedBoxFiles
open TableDispatch PA194FiniteControls PA194StateOne
open PackedDecoderModel (modelDecodeRight)

/-- The controller-state register values packed in the specified physical file order. -/
def packedFileCode (A : Allocation) : Code 3 :=
  .comp (sourceFileCode A) (pack 11 argumentCodes)

/-- PR code for the physical source root, parameterized by controller
    state, additional header gap, extra spare count, and first spare value. -/
def sourceRootCode (A : Allocation) : Code 4 := .comp rootCode (pack 3 ![unary pc (.proj 0),.proj 1,
  .comp (packedFileCode A) (pack 3 ![.proj 0,.proj 2,.proj 3])])

section models
variable (A : Allocation)
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- The physical source-root state built from a file already in native order. -/
noncomputable def frame (q : Nat) (gap packed : M) : M :=
  F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
    modelWord (PA194SourceProgram.path q) (F zeros ![gap,(1 : M)+(packed+packed)])]]

theorem rootCode_file (i : Fin 3673) (gap packed : M) :
    F rootCode ![modelNumeral M i.val,gap,packed] =
      frame i.val (gap+modelNumeral M (48-(PA194SourceProgram.path i.val).length)) packed := by
  simp only [rootCode,rightHalf,modelBin,modelUnary,modelProjection,modelConstant,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,modelNumeralOne,pathDispatch,
    modelLookupNumeral,offsets_get,modelPushOne]
  rw [indexedCorrect,pathCodes_get,wordCodeCorrect]
  unfold frame
  have hr (a : M) : a+a+1 = 1+(a+a) := by ac_rfl
  rw [hr]
  rfl

theorem packedFileCodeCorrect (s count spare : M) :
    F (packedFileCode A) ![s,count,spare] = F (sourceFileCode A) (args s count spare) := by
  rw [packedFileCode,modelComposition,getCode_pack]
  congr 1
  funext i
  exact argumentCodesCorrect s count spare i

theorem sourceRootCodeCorrect (s gap count spare : M) (j : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M j.val) :
    F (sourceRootCode A) ![s,gap,count,spare] =
      frame j.val (gap+modelNumeral M (48-(PA194SourceProgram.path j.val).length))
        (file (tapeArgs A s count spare)) := by
  rw [sourceRootCode,modelComposition,getCode_pack]
  have h : (fun x : Fin 3 => F (![unary pc (.proj 0),.proj 1,
        .comp (packedFileCode A) (pack 3 ![.proj 0,.proj 2,.proj 3])] x : Code 4) ![s,gap,count,spare]) =
      ![modelNumeral M j.val,gap,F (sourceFileCode A) (args s count spare)] := by
    funext i
    fin_cases i
    · change F (unary pc (.proj 0)) ![s,gap,count,spare] = modelNumeral M j.val
      rw [modelUnary,modelProjection]
      have hv : (fun _ : Fin 1 => s) = ![s] := by
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      change F pc (fun _ => s) = modelNumeral M j.val
      rw [hv]
      exact hpc
    · change F (.proj 1) ![s,gap,count,spare] = gap
      rw [modelProjection]
      rfl
    · change F (.comp (packedFileCode A) (pack 3 ![.proj 0,.proj 2,.proj 3])) ![s,gap,count,spare] =
        F (sourceFileCode A) (args s count spare)
      rw [modelComposition,getCode_pack]
      have hv : (fun x : Fin 3 => F (![.proj 0,.proj 2,.proj 3] x : Code 4) ![s,gap,count,spare]) =
          ![s,count,spare] := by
        funext k
        fin_cases k
        · change F (.proj 0) ![s,gap,count,spare] = s
          exact modelProjection _ _
        · change F (.proj 2) ![s,gap,count,spare] = count
          exact modelProjection _ _
        · change F (.proj 3) ![s,gap,count,spare] = spare
          exact modelProjection _ _
      rw [hv,packedFileCodeCorrect]
  rw [h,rootCode_file,frameFile]

#print axioms packedFileCodeCorrect
#print axioms sourceRootCodeCorrect
end models
end PA194RegisterRoot
