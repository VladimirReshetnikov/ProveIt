import PA194CarryCell
import PA194RegisterFile
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
namespace PA194CarryFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PA194UnaryRuns PA194RegisterFile PA194CarryCell PA194StateOne PA194BinaryDouble

def two {n : Nat} : Code n := unary (TableDispatch.constantCode 2) (.zero n)
def costCode : (n : Nat) → Code (n+1)
  | 0 => .zero 1
  | n+1 => bin addCode (bin addCode two (.proj 0))
      (.comp (costCode n) (pack (n+1) (fun i => .proj i.succ)))

def advance {n : Nat} : Code (n+3) :=
  bin ones (.proj 1) (bin addCode (unary .succ (bin addCode (.proj 0) (.proj 0)))
    (unary .succ (bin addCode (.proj 0) (.proj 0))))
def leftCode : (n : Nat) → Code (n+2)
  | 0 => .proj 0
  | n+1 => .comp (leftCode n) (pack (n+2) (Fin.cases advance (fun i => .proj i.succ.succ)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelTwo {n : Nat} (e : Fin n → M) : F two e = (1 : M)+1 := by
  rw [two,modelUnary,TableDispatch.modelConstant]
  rw [←modelNumeralOne,←PA194FiniteControls.modelNumeralAdd]

theorem modelCostZero (e : Fin 1 → M) : F (costCode 0) e = (0 : M) := by
  change F (Code.zero 1) e = F (Code.zero 0) Fin.elim0
  exact PRAMultiplication.modelZero e

theorem modelCostSucc (n : Nat) (e : Fin (n+2) → M) :
    F (costCode (n+1)) e = ((1 : M)+1)+e 0 + F (costCode n) (fun i => e i.succ) := by
  rw [costCode,modelBin,modelBin,modelTwo,modelProjection,modelComposition,getCode_pack]
  have hv : (fun i : Fin (n+1) => F (.proj i.succ) e) = fun i => e i.succ := by
    funext i
    exact modelProjection i.succ e
  rw [hv]
  rfl

theorem modelAdvance {n : Nat} (e : Fin (n+3) → M) :
    F advance e = F ones ![e 1,(e 0+e 0+1)+(e 0+e 0+1)] := by
  simp only [advance,modelBin,PA194BinaryDouble.modelUnary,modelProjection,←modelAddOne]
  rfl

theorem modelLeftZero (e : Fin 2 → M) : F (leftCode 0) e = e 0 := by
  exact modelProjection 0 e

theorem modelLeftSucc (n : Nat) (e : Fin (n+3) → M) :
    F (leftCode (n+1)) e = F (leftCode n)
      (Fin.cases (F ones ![e 1,(e 0+e 0+1)+(e 0+e 0+1)]) (fun i => e i.succ.succ)) := by
  rw [leftCode,modelComposition,getCode_pack]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelAdvance e
  · exact modelProjection j.succ.succ e
/-- The carry engine traverses a fixed finite file, with arbitrary model
register values and suffix, using an explicit primitive-recursive clock and
left-tape output code. -/
theorem modelCarryFile (n : Nat) (e : Fin (n+1) → M) (l : M) :
    F PA194Stepper.stepper ![F (costCode n) e,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode n) e]]] =
    F pairCode ![(1 : M),F pairCode ![F (leftCode n) (Fin.cases l e),e (Fin.last n)]] := by
  induction n generalizing l with
  | zero =>
    rw [modelCostZero]
    have hz := PA194Stepper.modelStepperZero (F pairCode ![(1 : M),F pairCode ![l,F (fileCode 0) e]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
    rw [hz]
    change F pairCode ![(1 : M),F pairCode ![l,F (.proj 0) e]] = _
    rw [modelProjection,modelLeftZero]
    rfl
  | succ n ih =>
    let tail : M := F (fileCode n) (fun i => e i.succ)
    let next : M := F ones ![e 0,(l+l+1)+(l+l+1)]
    have hon : F ones ![e 0+1,tail] = F ones ![e 0,tail]+F ones ![e 0,tail]+1 := by
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],tail] = _
      rw [modelAddOne,modelOnesSucc]
    rw [modelCostSucc,modelFileSucc,modelBlock,hon]
    change F PA194Stepper.stepper ![F addCode ![((1 : M)+1)+e 0,F (costCode n) (fun i => e i.succ)],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    have hc := modelCarryCell (e 0) l tail
    dsimp only at hc
    rw [modelNumeralOne] at hc
    rw [hc]
    have hr := ih (fun i => e i.succ) next
    dsimp only [next,tail] at hr
    rw [hr,modelLeftSucc]
    rfl
#print axioms modelCarryFile
#print axioms modelCostSucc
#print axioms modelLeftSucc
end models
end PA194CarryFile
