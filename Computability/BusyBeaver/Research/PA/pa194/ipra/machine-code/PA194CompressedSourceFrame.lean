import PA194CompressedRootCode
import PA194SourceRegisters

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedSourceFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PRAExhaustion PA194SourceRegisters PA194SourceControllerCode
open PA194RegisterPermutation PA194CompressedRootCode PA194SourceSite31Physical PA194OneSpareReturn
open PA194BinaryDouble (unary modelUnary)
open TableDispatch PA194FiniteControls PA194StateOne
open PackedDecoderModel (modelDecodeRight)

def argumentCodes : Fin 11 → Code 3 :=
  Fin.snoc (Fin.snoc (fun r : Fin 9 => unary (getRegister r.val) (.proj 0)) (.proj 2))
    (bin repeatOutput (.proj 1) (.zero 3))

/-- Inputs are the controller state, additional spare count, and first spare
value. The suffix contains one unit block for every additional spare. -/
def packedFileCode : Code 3 := .comp sourceFileCode (pack 11 argumentCodes)

/-- Inputs are the controller state, additional header length, additional spare
count, and first spare value. -/
def sourceRootCode : Code 4 := .comp rootCode (pack 3 ![unary pc (.proj 0),.proj 1,
  .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def args (s count spare : M) : Fin 11 → M :=
  Fin.snoc (Fin.snoc (fun r : Fin 9 => getSem r.val (pi₂ s)) spare)
    (F repeatOutput ![count,(0 : M)])

theorem argumentCodesCorrect (s count spare : M) (i : Fin 11) :
    F (argumentCodes i) ![s,count,spare] = args s count spare i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [argumentCodes,args,Fin.snoc_last,modelBin,modelProjection,Matrix.cons_val_one,
      Matrix.cons_val_zero,PRAMultiplication.modelZero]
    rfl
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [argumentCodes,args,Fin.snoc_castSucc,Fin.snoc_last,modelProjection,Matrix.cons_val_two]
      rfl
    · simp only [argumentCodes,args,Fin.snoc_castSucc,modelUnary,modelProjection,Matrix.cons_val_zero,
        getRegister,file]
      have h := getAuxModel k.val PackedClock.decodeRight s
      have hv : (![s] : Fin 1 → M) = fun _ => s := by
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      rw [hv,modelDecodeRight] at h
      exact h

theorem packedFileCodeCorrect (s count spare : M) :
    F packedFileCode ![s,count,spare] = F sourceFileCode (args s count spare) := by
  rw [packedFileCode,modelComposition,getCode_pack]
  congr 1
  funext i
  exact argumentCodesCorrect s count spare i

theorem sourceRootCodeCorrect (s gap count spare : M) (j : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M j.val) :
    F sourceRootCode ![s,gap,count,spare] =
      physicalFrame j.val (gap+modelNumeral M (48-(PA194SourceProgram.path j.val).length))
        (args s count spare) := by
  rw [sourceRootCode,modelComposition,getCode_pack]
  have h : (fun x : Fin 3 => F (![unary pc (.proj 0),.proj 1,
        .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])] x : Code 4) ![s,gap,count,spare]) =
      ![modelNumeral M j.val,gap,F sourceFileCode (args s count spare)] := by
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
        F sourceFileCode (args s count spare)
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
  rw [h,rootCodeCorrect]

#print axioms packedFileCodeCorrect
#print axioms sourceRootCodeCorrect
end models
end PA194CompressedSourceFrame
