import PA194RadixSplit
import PA194RadixModel
import DiophantineConsistency.PRAHistoryIterator

set_option autoImplicit false
set_option maxRecDepth 22000
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

namespace PA194RadixRecoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRASelectCode PRAExhaustion PRAQOrder
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194ControllerRunAdd
open PA194PathIterator PA194TargetCantor PA194MachineProjections TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

abbrev quotient (last : Nat) := PA194RadixSplit.quotientCode last
abbrev remainder (last : Nat) := PA194RadixSplit.remainderCode last

def lookup : Code 2 := unary PackedClock.decodeLeft (iterate PackedClock.decodeRight)
def index : Code 2 := unary Code.succ (.proj 0)
def childIndex (last : Nat) (child : Code 1) : Code 2 :=
  unary child (unary (quotient last) index)
def childValue (last : Nat) (child : Code 1) : Code 2 :=
  bin lookup (bin subCode (.proj 0) (childIndex last child)) (.proj 1)
def digit (last : Nat) : Code 2 := unary (remainder last) index

noncomputable def stepValue (sourceLast targetLast : Nat) : Code 2 :=
  let tag := digit sourceLast
  let radix := unary (constantCode (targetLast+1)) (.proj 0)
  let left := childValue sourceLast fixedFirst
  let right := childValue sourceLast fixedSecond
  selectAmong (bin ltBitCode tag radix)
    (bin addCode (bin mulCode radix (bin fixedCantor left right)) tag)
    (.zero 2)

noncomputable def historyStep (sourceLast targetLast : Nat) : Code 2 :=
  bin pairCode (stepValue sourceLast targetLast) (.proj 1)

noncomputable def history (sourceLast targetLast : Nat) : Code 1 :=
  PRAHistoryIterator.valueCode (.zero 0) (historyStep sourceLast targetLast)

noncomputable def recode (sourceLast targetLast : Nat) : Code 1 :=
  unary PackedClock.decodeLeft (history sourceLast targetLast)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

private theorem singleton (x : M) : (![x] : Fin 1 → M) = fun _ => x := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem historyZero (sourceLast targetLast : Nat) :
    F (history sourceLast targetLast) ![(0 : M)] = 0 := by
  rw [singleton]
  exact PRAHistoryIterator.modelValueBase (.zero 0) (historyStep sourceLast targetLast)

theorem historySucc (sourceLast targetLast : Nat) (n : M) :
    F (history sourceLast targetLast) ![n+1] =
      pair (F (stepValue sourceLast targetLast) ![n,F (history sourceLast targetLast) ![n]])
        (F (history sourceLast targetLast) ![n]) := by
  have h := PRAHistoryIterator.modelValueStep (.zero 0) (historyStep sourceLast targetLast) n
  rw [←modelAddOne] at h
  change F (history sourceLast targetLast) (fun _ => n+1) =
    F (historyStep sourceLast targetLast) ![n,F (history sourceLast targetLast) (fun _ => n)] at h
  rw [singleton (n+1),h,historyStep,modelBin,modelProjection,modelPairCode]
  simp only [singleton]
  rfl

theorem modelLookup (offset hist : M) :
    F lookup ![offset,hist] =
      pi₁ (F (iterate PackedClock.decodeRight) ![offset,hist]) := by
  rw [lookup,modelUnary,PackedDecoderModel.modelDecodeLeft]

theorem modelRecode (sourceLast targetLast : Nat) (n : M) :
    F (recode sourceLast targetLast) ![n] = pi₁ (F (history sourceLast targetLast) ![n]) := by
  rw [recode,modelUnary,PackedDecoderModel.modelDecodeLeft]

theorem recodeZero (sourceLast targetLast : Nat) :
    F (recode sourceLast targetLast) ![(0 : M)] = 0 := by
  rw [modelRecode,historyZero]
  have hzero : pair (0 : M) 0 = 0 := by simp [pair]
  exact (congrArg pi₁ hzero.symm).trans (pi₁_pair 0 0)

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lookupZero (hist : M) : F lookup ![0,hist] = pi₁ hist := by
  rw [modelLookup,iterateZero]

theorem lookupSucc (offset head tail : M) :
    F lookup ![offset+1,pair head tail] = F lookup ![offset,tail] := by
  have ht : F (iterate PackedClock.decodeRight) ![(1 : M),pair head tail] = tail := by
    rw [←zero_add (1 : M),iterateSucc,iterateZero,singleton,PackedDecoderModel.modelDecodeRight,pi₂_pair]
  rw [modelLookup,show offset+1 = 1+offset by ac_rfl,iterateAdd,ht,←modelLookup]

private theorem lookupEquationDef (a : M → M) (get : M → M → M)
    (ha : 𝚺₁-Function₁ a) (base result : M) (hlookup : 𝚺₁-Function₂ get) :
    𝚺₁-Predicate (fun i : M => get i (a (base+i)) = result) := by
  haveI := ha
  haveI := hlookup
  definability

theorem lookupHistory (sourceLast targetLast : Nat) (n offset : M) :
    F lookup ![offset,F (history sourceLast targetLast) ![n+offset]] =
      F (recode sourceLast targetLast) ![n] := by
  have hd := lookupEquationDef
    (fun j => F (history sourceLast targetLast) ![j])
    (fun i hist => F lookup ![i,hist])
    (unaryCodeDef _) n (F (recode sourceLast targetLast) ![n]) (binaryCodeDef _)
  induction offset using ISigma1.sigma1_succ_induction with
  | hP => exact hd
  | zero => rw [add_zero,lookupZero,modelRecode]
  | succ offset ih =>
    rw [show n+(offset+1) = (n+offset)+1 by ac_rfl,historySucc,lookupSucc,ih]

theorem lookupOlder (sourceLast targetLast : Nat) (older n : M) (h : older ≤ n) :
    F lookup ![F subCode ![n,older],F (history sourceLast targetLast) ![n]] =
      F (recode sourceLast targetLast) ![older] := by
  obtain ⟨offset,hOffset⟩ := le_iff_exists_add.mp h
  have hsub : F subCode ![older+offset,older] = offset := PRASubAddition.modelSubAdd older offset
  rw [hOffset,hsub]
  exact lookupHistory sourceLast targetLast older offset

#print axioms historySucc
#print axioms lookupOlder
end models
end PA194RadixRecoding
