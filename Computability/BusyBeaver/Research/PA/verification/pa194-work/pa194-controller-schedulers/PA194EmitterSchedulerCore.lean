import PA194ControllerSchedulerCore
import PA194SchedulerHaltCode

/-!
# Codes of the schedulers with a variant axiom emitter

The AX command of the primary table leaves its gate `G(H, D, A)` and pushes `Γ(A)`, the
heads `h₆, …, h₁`, the restricted row `ρ(D, A, H, d)` and the generalization `U(d, h)`.
Other candidates change these entries, independently of each other and of the command
controller:

| Field of `Emitter` | Entry | Primary | Variant |
| --- | --- | --- | --- |
| `gd` | separate diagonal | `Γ(A)` | `Γ(D)` |
| `q` | sixth head | `U(D,A) → (U(D,A→H) → U(D,H))` | `U(D,A→H) → (U(D,A) → U(D,H))` |
| `x` | fifth head | `W(D,H) → 1` | `W(D,H) → A` |
| `ga` | generalization | `U(d, h)` | `U(A, h)` |
| `bundled` | gate, diagonal | `¬(V → Q)`, `Γ` pushed | `¬(Γ(A) → (V → Q))`, no `Γ` pushed |

Here `W(D,H) = U(D, E(H,D) → 1)`, `A` is the label argument of the command, `D = d + x` and
`H = h + y`, and `V = V(H,D,A)`, `Q = Q(H,D,A)` are the two parts of the gate of the primary
table. With `bundled`, AX pushes seven leaves instead of eight; this is the emitter of the
original PA195. The field `gd` has no effect then.

All fields default to `false`, so an emitter is written by its changed fields, for example
`{ q := true, ga := true }`.

This file contains only codes: the changed heads and gate, the stack and the top after AX,
the scheduler step `stepE e k a`, its iteration `runE e k a` and the halt bit
`haltAfterE e k ct a`. The parameters `k`, `ct` and `a` are those of
`PA194ControllerSchedulerCore`.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194EmitterScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194TargetLeaves PA194TargetGate PA194SchedulerIteration PA194SchedulerHaltCode
 PA194ControllerScheduler
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open ConPA.Ctl (MPKind)

/-- The entries of the AX command that differ from the primary emitter. -/
structure Emitter where
  /-- The separate diagonal is `Γ(D)` instead of `Γ(A)`. -/
  gd : Bool := false
  /-- The premises of the sixth head are exchanged. -/
  q : Bool := false
  /-- The fifth head is `W(D, H) → A` instead of `W(D, H) → 1`. -/
  x : Bool := false
  /-- The generalization is `U(A, h)` instead of `U(d, h)`. -/
  ga : Bool := false
  /-- The diagonal is not pushed; the gate is `¬(Γ(A) → (V → Q))`. -/
  bundled : Bool := false

/-- The emitter of the primary table. -/
def Emitter.primary : Emitter := {}

/-- The sixth head with exchanged premises, as a code of `D A H`. -/
noncomputable def head6Q : Code 3 :=
  machineImp (machineAll (.proj 0) (machineImp (.proj 1) (.proj 2)))
    (machineImp (machineAll (.proj 0) (.proj 1)) (machineAll (.proj 0) (.proj 2)))

/-- The fifth head with the consequent `A`, as a code of `D A H`. -/
noncomputable def head5X : Code 3 :=
  machineImp (machineAll (.proj 0) (machineNeg (machineEq (.proj 2) (.proj 0)))) (.proj 1)

/-- The gate with the diagonal bundled, `¬(Γ(c) → (V(a,b,c) → Q(a,b,c)))`, as a code of
`a b c`. -/
noncomputable def bundledGate : Code 3 :=
  machineNeg (machineImp (unary diagonal (.proj 2)) (machineImp memVac separationTail))

/-- The argument of the separate diagonal. -/
noncomputable def diagArg (g : Bool) {n : Nat} (D A : Code n) : Code n :=
  match g with
  | true => D
  | false => A

/-- The sixth head. -/
noncomputable def head6E (q : Bool) {n : Nat} (D A H : Code n) : Code n :=
  match q with
  | true => app3 head6Q D A H
  | false => app3 head6 D A H

/-- The fifth head. -/
noncomputable def head5E (x : Bool) {n : Nat} (D A H : Code n) : Code n :=
  match x with
  | true => app3 head5X D A H
  | false => bin head5 D H

/-- The label of the generalization. -/
noncomputable def genArg (ga : Bool) {n : Nat} (A d : Code n) : Code n :=
  match ga with
  | true => A
  | false => d

/-- The stack entries of AX, top first: ten, or nine when the diagonal is bundled into the
gate. -/
noncomputable def axStackCodeE (e : Emitter) {n : Nat} (t A d h y x w : Code n) : Code n :=
  let D := bin addCode d x
  let H := bin addCode h y
  let rest : Code n :=
    pair (head6E e.q D A H)
      (pair (head5E e.x D A H)
        (pair (app3 head4 D A H)
          (pair (app3 head3 D A H)
            (pair (app3 head2 D A H)
              (pair (bin machineHead1 D H)
                (pair (app4 rho8 D A H d)
                  (pair (machineAll (genArg e.ga A d) h) (pair t w))))))))
  match e.bundled with
  | true => rest
  | false => pair (unary diagonal (diagArg e.gd D A)) rest

/-- The gate of AX with its guard: `0` when `D = A` or `H = A`. -/
noncomputable def axTopCodeE (e : Emitter) {n : Nat} (A d h y x : Code n) : Code n :=
  match e.bundled with
  | true =>
    selectAmong (bin equalityCode (bin addCode d x) A) (.zero n)
      (selectAmong (bin equalityCode (bin addCode h y) A) (.zero n)
        (app3 bundledGate (bin addCode h y) (bin addCode d x) A))
  | false => axTopCode A d h y x

/-- The top after AX: the gate, or `0` in the layout that pushes the gate. -/
noncomputable def axTopEA (e : Emitter) (a : Bool) {n : Nat} (A d h y x : Code n) : Code n :=
  match a with
  | true => .zero n
  | false => axTopCodeE e A d h y x

/-- The stack after AX: in the layout that pushes the gate, the gate is pushed last. -/
noncomputable def axStackEA (e : Emitter) (a : Bool) {n : Nat} (t A d h y x w : Code n) :
    Code n :=
  match a with
  | true => pair (axTopCodeE e A d h y x) (axStackCodeE e t A d h y x w)
  | false => axStackCodeE e t A d h y x w

noncomputable def nextTopE (e : Emitter) (k : MPKind) (a : Bool) {m : Nat}
    (n l t _w d h : Code m) : Code m :=
  choose0 (head n l) h (choose1 (head n l) (mpTopK k t h d (yArg n l))
    (axTopEA e a (axArg n l) d h (yArg n l) (xArg n l)))

noncomputable def nextStackE (e : Emitter) (k : MPKind) (a : Bool) {m : Nat}
    (n l t w d h : Code m) : Code m :=
  choose0 (head n l) (shiftStack w) (choose1 (head n l) (mpStackK k t w h d (yArg n l))
    (axStackEA e a t (axArg n l) d h (yArg n l) (xArg n l) w))

/-- One scheduler step on the packed state `⟪n, l, t, w, d, h⟫`. -/
noncomputable def stepE (e : Emitter) (k : MPKind) (a : Bool) : Code 1 :=
  pack (PA194SchedulerCode.nextN fN fL) (nextLA a fN fL)
    (nextTopE e k a fN fL fT fW fD fH) (nextStackE e k a fN fL fT fW fD fH)
    (nextDK k a fN fL fT fD fH) (nextCacheK k fN fL fT fW fD fH)

noncomputable def runE (e : Emitter) (k : MPKind) (a : Bool) : Code 2 := dropCode (stepE e k a)

/-- The halt bit after a number of steps from the initial state. -/
noncomputable def haltAfterE (e : Emitter) (k : MPKind) (ct a : Bool) : Code 1 :=
  unary (haltAtK ct) (bin (runE e k a) (.proj 0) initialConstant)

end PA194EmitterScheduler

#print axioms PA194EmitterScheduler.stepE
#print axioms PA194EmitterScheduler.runE
#print axioms PA194EmitterScheduler.haltAfterE
