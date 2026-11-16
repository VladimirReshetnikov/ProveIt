import PA194ADCompressedPhysical
import PA194ADSourceArgs
import PA194CompressedSourceFrame
import PA194ClockInvariantDefinable
import PA194HalfDiv

/-! Arithmetic encoding of the OR address trie at the literal source root. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194ADRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PRATermCompilation
open PA194BinaryDouble (unary modelUnary)
open PA194CompressedRootCode (indexed indexedCorrect wordCode wordCodeCorrect)
open PA194CompressedSourceFrame (args argumentCodes argumentCodesCorrect)
open PA194SourceProgram
open PA194ClockInvariantDefinable PA194SourceControllerCode PA194ADCompressedData
open PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194HalfDiv PA194StateOne
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime

theorem path_short (i : Nat) : (path i).length ≤ 48 :=
  (PA194SourceProgram.path_short i).trans (by decide)

def pathCodes : List (Code 1) := (List.range 3673).map (wordCode ∘ path)

def offsets : List Nat := (List.range 3673).map (fun i => 48-(path i).length)

def rightHalf : Code 3 := bin (indexed pathCodes) (.proj 0)
  (bin zeros (bin addCode (.proj 1) (unary (lookupCode 0 offsets) (.proj 0))) (unary pushOne (.proj 2)))

/-- The OR root as a function of the source ordinal, extra gap, and register file. -/
def rootCode : Code 3 :=
  bin pairCode (unary (constantCode 24) (.proj 0))
    (bin pairCode (unary (constantCode 1) (.proj 0)) rightHalf)

def packedFileCode : Code 3 := .comp PA194ADFile.sourceFileCode (pack 11 argumentCodes)

/-- The source controller is unchanged. Only address selection at the physical
root uses the OR trie. -/
def sourceRootCode : Code 4 := .comp rootCode (pack 3 ![unary pc (.proj 0),.proj 1,
  .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])])

private theorem pathCodeAt (i : Fin 3673) :
    pathCodes.getD i.val (.proj 0) = wordCode (path i.val) := by
  have hi : i.val < pathCodes.length := by simpa [pathCodes] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp [pathCodes]

private theorem offsetAt (i : Fin 3673) :
    offsets.getD i.val 0 = 48-(path i.val).length := by
  have hi : i.val < offsets.length := by simpa [offsets] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp [offsets]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packedFileCodeCorrect (s count spare : M) :
    F packedFileCode ![s,count,spare] = F PA194ADFile.sourceFileCode (args s count spare) := by
  rw [packedFileCode,modelComposition,getCode_pack]
  congr 1
  funext i
  exact argumentCodesCorrect s count spare i

private theorem zeros_eq (n x : M) : F zeros ![n,x] = bitPrefix false n x := by
  have hp : 𝚺₁-Function₂ (bitPrefix (V := M) false) := by
    change 𝚺₁-Function₂ (fun n x : M => Exp.exp n * x)
    definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact equalPred _ _ (bindBinary _ x (binaryCodeDef zeros)) (bindBinary _ x hp)
  | zero => rw [modelZerosZero, bitPrefix_zero]
  | succ n ih =>
    have hz := PA194BidirectionalRunScan.runSucc false n x
    change F zeros ![n + 1,x] = F zeros ![n,x] + F zeros ![n,x] at hz
    rw [hz, ih, bitPrefix_succ]
    simp [two_mul]

private theorem word_eq (bits : List Bool) (x : M) :
    bits.foldr ConPA.Machine.Compressed.push x = modelWord bits x := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [List.foldr_cons, ih, PA194SymbolicMove.wordPush]
    cases bit <;> simp [ConPA.Machine.Compressed.push, PA194BidirectionalRow.push, two_mul]

theorem root_eval (gap : M) (box : BoxSt → M) (i extra : Nat) (effect : Eff) :
    PA194ADCompressedPhysical.root gap box i extra effect =
      ⟪(24 : M),(1 : M),modelWord (path i)
        (F zeros ![gap+modelNumeral M (48+extra-(path i).length),
          F pushOne (fun _ => box (.plain effect))])⟫ := by
  simp only [PA194ADCompressedPhysical.root, PA194RuntimeContracts.rootFrame, encode, scanFrame, if_true,
    PA194ADCompressedPhysical.rootControl, packBits, packSegments, runLength, Nat.cast_one, one_mul,
    modelNumeralCast, word_eq, zeros_eq, modelPushOne]
  simp [ConPA.Machine.Compressed.push, two_mul]

theorem root_advanced_gap (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    PA194ADCompressedPhysical.root gap box i 1 effect = PA194ADCompressedPhysical.root (gap + 1) box i 0 effect := by
  rw [root_eval, root_eval]
  have hs := path_short i
  have h : 48+1-(path i).length = 1+(48-(path i).length) := by omega
  rw [h, modelNumeralAdd, modelNumeralOne, Nat.add_zero, add_assoc]

theorem rootCode_eval (i : Fin 3673) (gap file : M) :
    F rootCode ![modelNumeral M i.val,gap,file] =
      PA194ADCompressedPhysical.root gap (fun _ => file) i.val := by
  rw [root_eval]
  simp only [rootCode, rightHalf, modelBin, modelUnary, modelProjection,
    modelConstant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    modelLookupNumeral, offsetAt, modelPairCode, modelNumeralOne]
  rw [indexedCorrect, pathCodeAt, wordCodeCorrect]
  simp only [Nat.add_zero, modelNumeralCast, Nat.cast_ofNat, Nat.cast_one] <;> rfl

theorem root_initial_file (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    PA194ADCompressedPhysical.root gap box i 0 effect =
      PA194ADCompressedPhysical.root gap (fun _ => box (.plain effect)) i := by
  rw [root_eval, root_eval]

theorem sourceRoot_eval (s gap count spare : M) (i : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M i.val) :
    F sourceRootCode ![s,gap,count,spare] =
      PA194ADCompressedPhysical.root gap (fun _ => F PA194ADFile.sourceFileCode (args s count spare)) i.val := by
  rw [sourceRootCode, modelComposition, getCode_pack]
  have he : (fun j : Fin 3 => F (![unary pc (.proj 0),.proj 1,
      .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])] j : Code 4) ![s,gap,count,spare]) =
      ![modelNumeral M i.val,gap,F PA194ADFile.sourceFileCode (args s count spare)] := by
    funext j
    fin_cases j
    · change F (unary pc (.proj 0)) ![s,gap,count,spare] = modelNumeral M i.val
      rw [modelUnary, modelProjection]
      have hv : (fun _ : Fin 1 => s) = ![s] := by
        funext j
        exact Fin.cases rfl (fun k => Fin.elim0 k) j
      change F pc (fun _ => s) = modelNumeral M i.val
      rw [hv]
      exact hpc
    · exact modelProjection _ _
    · change F (.comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])) ![s,gap,count,spare] = _
      rw [modelComposition, getCode_pack]
      have hv : (fun j : Fin 3 => F (![.proj 0,.proj 2,.proj 3] j : Code 4) ![s,gap,count,spare]) =
          ![s,count,spare] := by
        funext j
        fin_cases j <;> exact modelProjection _ _
      rw [hv, packedFileCodeCorrect] <;> rfl
  rw [he, rootCode_eval]

#print axioms sourceRoot_eval
#print axioms root_advanced_gap
end models
end PA194ADRoot
