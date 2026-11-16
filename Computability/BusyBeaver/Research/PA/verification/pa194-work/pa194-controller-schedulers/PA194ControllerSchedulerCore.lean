import PA194SchedulerIteration
import ConPACtlWords

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ControllerScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194SchedulerIteration
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open ConPA.Ctl (MPKind mpStore)

/-! ## Codes -/

/-- `0` when the implication matches, the consequent otherwise. -/
noncomputable def mpFail {n : Nat} (t h d x : Code n) : Code n :=
  selectAmong (mpMatches t h d x) (.zero n) (mpArg d x)

/-- The top after MP. -/
noncomputable def mpTopK (k : MPKind) {n : Nat} (t h d x : Code n) : Code n :=
  match k with
  | .cache => .zero n
  | _ => mpTop t h d x

/-- The stack after MP. -/
noncomputable def mpStackK (k : MPKind) {n : Nat} (t w h d x : Code n) : Code n :=
  match k with
  | .push => mpStack t w h d x
  | _ => w

/-- The register `d` after MP. -/
noncomputable def mpDK (k : MPKind) {n : Nat} (t h d x : Code n) : Code n :=
  match k with
  | .cache => mpFail t h d x
  | _ => mpArg d x

/-- The cache after MP. -/
noncomputable def mpHK (k : MPKind) {n : Nat} (t h d x : Code n) : Code n :=
  match k with
  | .cache => mpTop t h d x
  | _ => .zero n

/-- The top after AX: the gate, or `0` in the eleven-entry layout. -/
noncomputable def axTopA (a : Bool) {n : Nat} (A d h y x : Code n) : Code n :=
  match a with
  | true => .zero n
  | false => axTopCode A d h y x

/-- The stack after AX: in the eleven-entry layout the gate is pushed last. -/
noncomputable def axStackA (a : Bool) {n : Nat} (t A d h y x w : Code n) : Code n :=
  match a with
  | true => pair (axTopCode A d h y x) (axStackCode t A d h y x w)
  | false => axStackCode t A d h y x w

/-- The register `d` after AX: the fourth argument in the eleven-entry layout. -/
noncomputable def axDA (a : Bool) {n : Nat} (z : Code n) : Code n :=
  match a with
  | true => z
  | false => .zero n

/-- The fourth field of the seed and the tail after it. -/
noncomputable def zArg {m : Nat} (n l : Code m) : Code m := unary fixedFirst (tail3 n l)
noncomputable def tail4 {m : Nat} (n l : Code m) : Code m := unary fixedSecond (tail3 n l)

/-- The fourth command field: read from the seed only in the eleven-entry layout. -/
noncomputable def zField (a : Bool) {m : Nat} (n l : Code m) : Code m :=
  match a with
  | true => zArg n l
  | false => .zero m

/-- The next continuation pointer. -/
noncomputable def nextLA (a : Bool) {m : Nat} (n l : Code m) : Code m :=
  match a with
  | true => choose0 (head n l) (PA194SchedulerCode.tail n l)
      (choose1 (head n l) (tail2 n l) (tail4 n l))
  | false => PA194SchedulerCode.nextL n l

noncomputable def nextTopK (k : MPKind) (a : Bool) {m : Nat} (n l t _w d h : Code m) : Code m :=
  choose0 (head n l) h (choose1 (head n l) (mpTopK k t h d (yArg n l))
    (axTopA a (axArg n l) d h (yArg n l) (xArg n l)))
noncomputable def nextStackK (k : MPKind) (a : Bool) {m : Nat} (n l t w d h : Code m) : Code m :=
  choose0 (head n l) (shiftStack w) (choose1 (head n l) (mpStackK k t w h d (yArg n l))
    (axStackA a t (axArg n l) d h (yArg n l) (xArg n l) w))
noncomputable def nextDK (k : MPKind) (a : Bool) {m : Nat} (n l t d h : Code m) : Code m :=
  choose0 (head n l) d (choose1 (head n l) (mpDK k t h d (yArg n l)) (axDA a (zField a n l)))
noncomputable def nextCacheK (k : MPKind) {m : Nat} (n l t w d h : Code m) : Code m :=
  choose0 (head n l) (shiftCache w) (choose1 (head n l) (mpHK k t h d (yArg n l)) (.zero m))

/-- One scheduler step on the packed state `⟪n, l, t, w, d, h⟫`. -/
noncomputable def stepK (k : MPKind) (a : Bool) : Code 1 :=
  pack (PA194SchedulerCode.nextN fN fL) (nextLA a fN fL)
    (nextTopK k a fN fL fT fW fD fH) (nextStackK k a fN fL fT fW fD fH)
    (nextDK k a fN fL fT fD fH) (nextCacheK k fN fL fT fW fD fH)

noncomputable def runK (k : MPKind) (a : Bool) : Code 2 := dropCode (stepK k a)

/-- The halting test `h = 1`. -/
noncomputable def shiftHaltC {n : Nat} (h : Code n) : Code n :=
  bin equalityCode h (numeralCode n 1)

/-- The halt bit of a packed state: its step is a SHIFT whose halting test succeeds. -/
noncomputable def haltAtK (ct : Bool) : Code 1 :=
  if ct then choose0 (head fN fL) (shiftHaltC fH) (.zero 1) else haltAt


end PA194ControllerScheduler

#print axioms PA194ControllerScheduler.stepK
#print axioms PA194ControllerScheduler.runK
#print axioms PA194ControllerScheduler.haltAtK
