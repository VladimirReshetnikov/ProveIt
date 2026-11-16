import PA194State42Boundary
import PA194ReturnFileMeaning
import PA194DecrementChoice
import PA194ScanInvariant
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ReturnedDecrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkedFile PA194CarryFile
open PA194ReturnFile PA194ReturnFileMeaning PA194State42Boundary PA194DecrementChoice PA194StateOne
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The genuine marker-return tail is a regular prefix followed by the
selected marked register. The prefix length is arbitrary and standard; its
register values, selected value, and suffix may all be nonstandard. -/
theorem returnedMarkedFile (idx n : Nat) (e : Fin (idx+2) → M)
    (rest : Fin (n+2) → M) (v : M) :
    let tail := F (fileCode (n+1)) rest
    let t := F ones ![v,tail]
    let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
    let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![v,tail])
    w = F (fileCode idx) ep ∧ ep (Fin.last idx) = F markedBlock ![v,tail] := by
  dsimp only
  constructor
  · have hm := modelReturnMeaning idx (fun i : Fin (idx+1) => e i.succ)
      (F markedBlock ![v,F (fileCode (n+1)) rest])
    simpa only [Fin.cases_zero,Fin.cases_succ,modelMarkedBlock] using hm
  · simp [replaceLast]
/-- State 42 with a successor-length residual run enters the decrement box with the
actual marked-file layout. It then executes the selected register's zero or
positive case through an arbitrary finite returned prefix. -/
theorem state42Decrement (idx n : Nat) (e : Fin (idx+2) → M)
    (rest : Fin (n+2) → M) (v l m : M) :
    letI : DecidableEq M := Classical.decEq M
    let tail := F (fileCode (n+1)) rest
    let t := F ones ![v,tail]
    let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
    let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![v,tail])
    let left := F ones ![m,(l+l)+(l+l)]
    let cost := F (costCode idx) ep
    let pred := F predCode (fun _ => v)
    let positive := F (returnCode idx) (Fin.cases (F block ![pred,tail]) ep)
    let zero := F (returnCode idx) (Fin.cases (F block ![(0 : M),tail]) ep)
    let isZero := v = (0 : M)
    F PA194Stepper.stepper ![(modelNumeral M 2+m)+((cost+(if isZero then modelNumeral M 7 else modelNumeral M 4))+cost),
      F pairCode ![modelNumeral M 42,F pairCode ![l,F ones ![m+1,w]+F ones ![m+1,w]]]] =
    if isZero then F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => left),F parityCode (fun _ => left)+zero+zero]]
    else F pairCode ![modelNumeral M 7,F pairCode ![left,positive+positive+1]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let tail := F (fileCode (n+1)) rest
  let t := F ones ![v,tail]
  let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
  let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
  let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![v,tail])
  have ⟨hw,hp⟩ := returnedMarkedFile idx n e rest v
  change w = F (fileCode idx) ep at hw
  change ep (Fin.last idx) = F markedBlock ![v,tail] at hp
  have hr := positiveRun m l w
  dsimp only at hr
  have hs := PA194ScanInvariant.modelFullScan m ((l+l)+(l+l)) w
  rw [←modelNumeralOne] at hs
  change F PA194Stepper.stepper ![F addCode ![F addCode ![modelNumeral M 2,m],_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hr,hs,hw]
  simpa only [modelNumeralOne] using
    modelDecrementChoice idx n ep rest v (F ones ![m,(l+l)+(l+l)]) hp
/-- After the box, the remaining regular prefix is preserved and the
selected marked block is replaced by an ordinary block holding `newValue`.
The first, already-scanned block is on the left tape and is not asserted to
be restored by this equality. -/
theorem returnedUpdatedFile (idx n : Nat) (e : Fin (idx+2) → M)
    (rest : Fin (n+2) → M) (v newValue : M) :
    let tail := F (fileCode (n+1)) rest
    let vals : Fin (idx+1) → M := fun i => e i.succ
    let ep := replaceLast idx vals (F markedBlock ![v,tail])
    F (returnCode idx) (Fin.cases (F block ![newValue,tail]) ep) =
    F (fileCode idx) (replaceLast idx vals (F block ![newValue,tail])) := by
  dsimp only
  rw [modelReturnMeaning]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replaceLast]
  · simp [replaceLast]
#print axioms returnedUpdatedFile
#print axioms returnedMarkedFile
#print axioms state42Decrement
end models
end PA194ReturnedDecrement
