import PA194Site28CarryFile
import PA194CarryFile
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28CarryCodes
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194Site28CarryFile PA194RegisterFile PA194UnaryRuns PA194FiniteControls PA194StateOne PA194BinaryDouble PRAModelIOpenPairing

def timeCode : (n : Nat) → Code (n+2)
  | 0 => .zero 2
  | n+1 => bin addCode (bin addCode PA194CarryFile.two (.proj 0))
      (.comp (timeCode n) (pack (n+2) (fun i => .proj i.succ)))

def advance {n : Nat} : Code (n+4) :=
  bin ones (unary .succ (.proj 1)) (bin addCode (.proj 0) (.proj 0))

def leftCode : (n : Nat) → Code (n+3)
  | 0 => .proj 0
  | n+1 => .comp (leftCode n) (pack (n+3) (Fin.cases advance (fun i => .proj i.succ.succ)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelTime (n : Nat) (e : Fin (n+2) → M) : F (timeCode n) e = carryTime n e := by
  induction n with
  | zero =>
    change F (Code.zero 2) e = F (Code.zero 0) Fin.elim0
    exact PRAMultiplication.modelZero e
  | succ n ih =>
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    rw [timeCode,modelBin,modelBin,PA194CarryFile.modelTwo,modelProjection,modelComposition,getCode_pack]
    have hv : (fun i : Fin (n+2) => F (.proj i.succ) e) = (fun i => e i.succ) := by
      funext i; exact modelProjection i.succ e
    rw [hv,ih]
    change (((1 : M)+1)+e 0)+carryTime n (fun i => e i.succ) =
      ((1 : M)+(e 0+1))+carryTime n (fun i => e i.succ)
    simp only [add_assoc,add_comm,add_left_comm]

theorem modelAdvance {n : Nat} (e : Fin (n+4) → M) :
    F advance e = F ones ![e 1+1,e 0+e 0] := by
  simp only [advance,modelBin,PA194BinaryDouble.modelUnary,modelProjection,←modelAddOne]
  rfl

theorem modelLeft (n : Nat) (e : Fin (n+2) → M) (l : M) :
    F (leftCode n) (Fin.cases l e) = carryLeft n l e := by
  induction n generalizing l with
  | zero =>
    change F (.proj 0) (Fin.cases l e) = l
    rw [modelProjection]
    rfl
  | succ n ih =>
    rw [leftCode,modelComposition,getCode_pack]
    have hv : (fun i : Fin (n+3) => F (Fin.cases advance (fun i => .proj i.succ.succ) i) (Fin.cases l e)) =
        Fin.cases (F ones ![e 0+1,l+l]) (fun i => e i.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cases_zero,modelAdvance]
        rfl
      · rw [Fin.cases_succ,modelProjection]
        rfl
    change F (leftCode n) (fun i => F (Fin.cases advance (fun i => .proj i.succ.succ) i) (Fin.cases l e)) =
      carryLeft n (F ones ![e 0+1,l+l]) (fun i => e i.succ)
    exact (congrArg (F (leftCode n)) hv).trans (ih (fun i => e i.succ) (F ones ![e 0+1,l+l]))

theorem carryFileCoded (n : Nat) (e : Fin (n+2) → M) (l : M) :
    F PA194Stepper.stepper ![F (timeCode n) e,F pairCode ![modelNumeral M 3,
      F pairCode ![l,F ones ![e 0+1,F (fileCode n) (fun i => e i.succ)]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![F (leftCode n) (Fin.cases l e),
      F ones ![e ⟨n,by omega⟩+1,e (Fin.last (n+1))]]] := by
  rw [modelTime,modelLeft]
  exact PA194Site28CarryFile.carryFile n e l
#print axioms modelTime
#print axioms modelLeft
#print axioms carryFileCoded
end models
end PA194Site28CarryCodes
