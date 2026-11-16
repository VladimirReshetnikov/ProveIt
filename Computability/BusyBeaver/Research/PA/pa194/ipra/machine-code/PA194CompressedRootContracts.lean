import PA194FoldedRuntimeRows
import PA194CompressedNormalization
import PA194RuntimeContracts
import PA194SourceSite31Physical
import PA194PhysicalHaltPersistence

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedRootContracts
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion
open PA194BidirectionalRow PA194BidirectionalRunScan PA194CompressedTape
open PA194CompressedExecutor PA194CompressedNormalization PA194FoldedRuntimeRows
open PA194SourceSite31Physical PA194Path27Header PA194StateOne PA194FiniteControls TableDispatch
open PA194RegisterPermutation PA194ZeroRuns
open M6.Runtime

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem packBits (gap : M) (box : BoxSt → M) (bits : List Bool) (rest : List Seg) :
    packSegments gap box (bits.map Seg.bit ++ rest) = modelWord bits (packSegments gap box rest) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.map_cons,List.cons_append,packSegments,PA194SymbolicMove.wordPush,ih]

theorem lengthOneCoefficient (gap : M) (k : Nat) :
    runLength gap 1 k = gap+modelNumeral M k := by
  rw [runLength, modelNumeralOne, one_mul]

/-- Equality of the compressed root frame and the literal source frame when
their register-box encodings agree. -/
theorem rootEncoding (gap : M) (box : BoxSt → M) (site extra : Nat)
    (e : Eff) (args : Fin 11 → M) (hbox : box (.plain e) = F sourceFileCode args) :
    encode denseControl gap box (PA194RuntimeContracts.rootFrame (PA194SourceProgram.path site) extra e) =
      physicalFrame site (gap+modelNumeral M (48+extra-(PA194SourceProgram.path site).length)) args := by
  simp only [PA194RuntimeContracts.rootFrame,encode,root_control,packBits,packSegments,lengthOneCoefficient]
  unfold physicalFrame frame packed
  simp only [↓reduceIte,runCode,Bool.false_eq_true,PA194BidirectionalRow.push,hbox,zero_add]
  have h : F sourceFileCode args + F sourceFileCode args + 1 =
      1 + (F sourceFileCode args + F sourceFileCode args) := by ac_rfl
  rw [h]

def contract (br : Branch) (i j extra fuel : Nat) (e : Eff) : Bool :=
  (exec machine br (fun s => sMatches s
      (PA194RuntimeContracts.rootFrame (PA194SourceProgram.path j) extra e))
      fuel (PA194RuntimeContracts.rootFrame (PA194SourceProgram.path i)) false).isSome

/-- The compressed checker gives a positive exact literal clock between two
source frames. The register operations and the finite certificate are the
remaining hypotheses. -/
theorem contractCorrect (br : Branch) (gap : M) (box : BoxSt → M)
    (hb : BoxAgreement denseControl br box)
    (i j extra fuel : Nat) (eff : Eff) (args args' : Fin 11 → M)
    (hbox : box (.plain .none) = F sourceFileCode args)
    (hbox' : box (.plain eff) = F sourceFileCode args')
    (hc : contract br i j extra fuel eff = true) :
    Reach1
      (physicalFrame i (gap+modelNumeral M (48-(PA194SourceProgram.path i).length)) args)
      (physicalFrame j (gap+modelNumeral M (48+extra-(PA194SourceProgram.path j).length)) args') := by
  let initial := PA194RuntimeContracts.rootFrame (PA194SourceProgram.path i)
  let final := PA194RuntimeContracts.rootFrame (PA194SourceProgram.path j) extra eff
  change (exec machine br (fun s => sMatches s final) fuel initial false).isSome = true at hc
  cases hr : exec machine br (fun s => sMatches s final) fuel initial false with
  | none => simp [hr] at hc
  | some out =>
    obtain ⟨hm,_,hp⟩ := checkedRun agreement gap hb (fun s => sMatches s final) fuel initial out false hr
    have he := matchesCorrect denseControl gap box out final hm
    have hh := hp rfl
    rw [he] at hh
    simpa only [initial,final,rootEncoding gap box i 0 .none args hbox,
      rootEncoding gap box j extra eff args' hbox',Nat.add_zero] using hh

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A segment that reaches a root frame has no literal halt at or before its
endpoint, since the literal halted configuration persists at every later clock. -/
theorem noInteriorHalt (initial : M) (site : Nat) (gap : M) (args : Fin 11 → M)
    (time segmentTime : M) (hbound : time ≤ segmentTime)
    (he : F PA194Stepper.stepper ![segmentTime,initial] = physicalFrame site gap args) :
    pi₁ (F PA194Stepper.stepper ![time,initial]) < modelNumeral M 194 := by
  by_contra h
  have ht := PA194PhysicalHaltPersistence.haltPersists initial time segmentTime hbound h
  apply ht
  rw [he]
  unfold physicalFrame
  rw [modelPairCode,pi₁_pair]
  exact modelNumeralStrict 24 194 (by decide)

#print axioms rootEncoding
#print axioms contractCorrect
#print axioms noInteriorHalt
end models
end PA194CompressedRootContracts
