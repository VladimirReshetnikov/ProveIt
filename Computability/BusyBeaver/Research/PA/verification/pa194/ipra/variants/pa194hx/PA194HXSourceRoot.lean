import PA194CompressedSourceFrame
import PA194HXFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXSourceRoot
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PRAExhaustion PA194SourceRegisters PA194SourceControllerCode
open PA194CompressedRootCode PA194CompressedSourceFrame PA194OneSpareReturn
open PA194BinaryDouble (unary modelUnary)
open TableDispatch PA194FiniteControls PA194StateOne
open PackedDecoderModel (modelDecodeRight)

/-- The controller-state register values packed in HX's physical file order. -/
def packedFileCode : Code 3 :=
  .comp PA194HXAllocation.sourceFileCode (pack 11 argumentCodes)

/-- PR code for the HX physical source root, parameterized by controller
    state, additional header gap, extra spare count, and first spare value. -/
def sourceRootCode : Code 4 := .comp rootCode (pack 3 ![unary pc (.proj 0),.proj 1,
  .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem packedFileCodeCorrect (s count spare : M) :
    F packedFileCode ![s,count,spare] = F PA194HXAllocation.sourceFileCode (args s count spare) := by
  rw [packedFileCode,modelComposition,getCode_pack]
  congr 1
  funext i
  exact argumentCodesCorrect s count spare i

theorem sourceRootCodeCorrect (s gap count spare : M) (j : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M j.val) :
    F sourceRootCode ![s,gap,count,spare] =
      PA194HXFrame.frame j.val (gap+modelNumeral M (48-(PA194SourceProgram.path j.val).length))
        (args s count spare) := by
  rw [sourceRootCode,modelComposition,getCode_pack]
  have h : (fun x : Fin 3 => F (![unary pc (.proj 0),.proj 1,
        .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])] x : Code 4) ![s,gap,count,spare]) =
      ![modelNumeral M j.val,gap,F PA194HXAllocation.sourceFileCode (args s count spare)] := by
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
    · change F (.comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])) ![s,gap,count,spare] =
        F PA194HXAllocation.sourceFileCode (args s count spare)
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
  rw [h,PA194HXAllocation.modelSourceFile_swap,rootCodeCorrect,← PA194HXFrame.frame_eq]

#print axioms packedFileCodeCorrect
#print axioms sourceRootCodeCorrect
end models
end PA194HXSourceRoot
