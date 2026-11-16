import PA194HXPhysicalConditional
import PA194HXFrame
import PA194ORRegisterFile
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXRootEncoding
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ZeroRuns PA194Path27Header TableDispatch PackedRootModel
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem zerosDef : 𝚺₁-Function₂ (fun n t : M => F zeros ![n,t]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F zeros e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) zeros)
  convert h using 1
  funext e
  apply congrArg (fun args : Fin 2 → M => F zeros args)
  funext i
  fin_cases i <;> rfl

private theorem equalityDef (f g : M → M → M) (target : M)
    (hf : 𝚺₁-Function₂ f) (hg : 𝚺₁-Function₂ g) :
    𝚺₁-Predicate (fun n => f n target = g n target) := by
  letI := hf
  letI := hg
  definability

theorem modelZeros_eq (n tail : M) : F zeros ![n,tail] = bitPrefix false n tail := by
  let g (n t : M) := F zeros ![n,t]
  have rightDef : 𝚺₁-Function₂ (bitPrefix (V := M) false) := by
    change 𝚺₁-Function₂ (fun n suffix : M => Exp.exp n * suffix)
    definability
  change g n tail = bitPrefix false n tail
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact equalityDef g (bitPrefix false) tail zerosDef rightDef
  | zero =>
    change F zeros ![(0 : M),tail] = _
    rw [modelZerosZero,bitPrefix_zero]
  | succ n ih =>
    change F zeros ![n,tail] = _ at ih
    change F zeros ![F addCode ![n,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelZerosSucc,ih,bitPrefix_succ]
    simp only [two_mul, Bool.toNat_false, Nat.cast_zero,add_zero]

private theorem numeralCast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc,ih,Nat.cast_succ]

theorem packBits (gap : M) (box : BoxSt → M) (bits : List Bool) (rest : List Seg) :
    packSegments gap box (bits.map Seg.bit ++ rest) = modelWord bits (packSegments gap box rest) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.map_cons,List.cons_append,packSegments,modelWord,ih]
    cases b <;> simp [ConPA.Machine.Compressed.push,two_mul]

theorem rootControl : PA194HXRowData.denseControl 84 = 24 := by decide +kernel

/-- HX's generic compressed root has exactly the logical HX source-frame
    encoding whenever its plain symbolic box denotes that register file. -/
theorem rootEncoding (gap : M) (box : BoxSt → M) (site extra : Nat) (effect : Eff)
    (args : Fin 11 → M) (hbox : box (.plain effect) = F PA194HXAllocation.sourceFileCode args) :
    PA194HXPhysicalConditional.root gap box site extra effect =
      PA194HXFrame.frame site (gap+modelNumeral M (48+extra-(PA194SourceProgram.path site).length)) args := by
  simp only [PA194HXPhysicalConditional.root,PA194RuntimeContracts.rootFrame,encode,scanFrame,
    PA194HXFrame.frame,packBits,packSegments,runLength,Nat.cast_one,one_mul,rootControl,numeralCast,
    modelPairCode, hbox, ↓reduceIte]
  rw [modelZeros_eq]
  simp [ConPA.Machine.Compressed.push,two_mul,add_comm]

/-- A checked symbolic source segment reaches the exact HX physical source
    frames, once the physical register-box obligations and endpoint boxes hold. -/
theorem contractFrames (gap : M) {br : Branch} {box : BoxSt → M}
    (hb : BoxAgreement PA194HXDispatch.table PA194HXRowData.denseControl br box)
    (i j extra fuel : Nat) (effect : Eff) (args args' : Fin 11 → M)
    (hbox : box (.plain .none) = F PA194HXAllocation.sourceFileCode args)
    (hbox' : box (.plain effect) = F PA194HXAllocation.sourceFileCode args')
    (cert : PA194HXContractSound.contract br i j extra fuel effect = true) :
    Reach1 PA194HXDispatch.table
      (PA194HXFrame.frame i (gap+modelNumeral M (48-(PA194SourceProgram.path i).length)) args)
      (PA194HXFrame.frame j (gap+modelNumeral M (48+extra-(PA194SourceProgram.path j).length)) args') := by
  have h := PA194HXPhysicalConditional.contract_sound gap hb i j extra fuel effect cert
  rw [rootEncoding gap box i 0 .none args hbox, rootEncoding gap box j extra effect args' hbox'] at h
  simpa only [Nat.add_zero] using h

#print axioms modelZeros_eq
#print axioms packBits
#print axioms rootEncoding
#print axioms contractFrames
end models
end PA194HXRootEncoding
