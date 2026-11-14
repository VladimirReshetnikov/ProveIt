import Mathlib.Tactic.FinCases
import PA194GenericRightScan
import PA194RightRows
import PA194UpdatedHead
import PA194CarryFile
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FileTraversal
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194BinaryDouble PA194RightRows PA194CarryFile PA194UpdatedHead
open PRAModelIOpenPairing TableDispatch

def validRow (q d : Nat) : Prop := q < 194 ∧
  PA194Rows.rows.getD (q+q+1) (0,0,194) = (1,1,q) ∧
  PA194Rows.rows.getD (q+q) (0,0,194) = (0,1,d)
def advance {n : Nat} : Code (n+3) := bin block (.proj 1) (.proj 0)
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
theorem modelAdvance {n : Nat} (e : Fin (n+3) → M) : F advance e = F block ![e 1,e 0] := by
  simp only [advance,modelBin,modelProjection]
theorem modelLeftZero (e : Fin 2 → M) : F (leftCode 0) e = e 0 := modelProjection 0 e
theorem modelLeftSucc (n : Nat) (e : Fin (n+3) → M) :
    F (leftCode (n+1)) e = F (leftCode n)
      (Fin.cases (F block ![e 1,e 0]) (fun i => e i.succ.succ)) := by
  rw [leftCode,modelComposition,getCode_pack]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelAdvance e
  · exact modelProjection j.succ.succ e
/-- Scan a physical block under any pinned one-loop/zero-exit rows. -/
theorem scanBlock (q d : Nat) (hv : validRow q d) (v l t : M) :
    F PA194Stepper.stepper ![((1 : M)+1)+v,F pairCode ![modelNumeral M q,
      F pairCode ![l,F ones ![v+1,t+t]]]] =
    F pairCode ![modelNumeral M d,F pairCode ![F block ![v,l],t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have loop (a b : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![a,b+b+1]]) =
      F pairCode ![modelNumeral M q,F pairCode ![a+a+1,b]] := by
    have h := rightOne q 1 q hv.1 hv.2.1 a b
    simpa only [PA194StateOne.modelNumeralOne] using h
  have hs := PA194GenericRightScan.modelFullScan q loop (v+1) l (t+t)
  have he := rightZero q 0 d hv.1 hv.2.2 (F ones ![v+1,l]) t
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at he
  have hc : ((1 : M)+1)+v = (v+1)+1 := by simp only [add_comm,add_left_comm]
  rw [hc]
  change F PA194Stepper.stepper ![F addCode ![v+1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,he,modelBlock]
/-- A fixed finite sequence of checked controls traverses a file with an
even final tail. Only the number of physical blocks is external and fixed;
all values, tails, and physical runtimes may be nonstandard. -/
theorem scanFile (n : Nat) (qs : Fin (n+1) → Nat)
    (hrows : ∀ i : Fin n, validRow (qs i.castSucc) (qs i.succ))
    (e : Fin (n+1) → M) (l t : M) (ht : e (Fin.last n) = t+t) :
    F PA194Stepper.stepper ![F (costCode n) e,F pairCode ![modelNumeral M (qs 0),
      F pairCode ![l,F halfCode (fun _ => F (fileCode n) e)]]] =
    F pairCode ![modelNumeral M (qs (Fin.last n)),F pairCode ![F (leftCode n) (Fin.cases l e),t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l with
  | zero =>
    rw [modelCostZero]
    have hz := PA194Stepper.modelStepperZero (F pairCode ![modelNumeral M (qs 0),
      F pairCode ![l,F halfCode (fun _ => F (fileCode 0) e)]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
    rw [hz,modelLeftZero]
    change F pairCode ![modelNumeral M (qs 0),F pairCode ![l,F halfCode (fun _ => F (.proj 0) e)]] = _
    change e 0 = t+t at ht
    rw [modelProjection,ht,(modelDouble t).2]
    rfl
  | succ n ih =>
    let rest : Fin (n+1) → M := fun i => e i.succ
    let route : Fin (n+1) → Nat := fun i => qs i.succ
    have hroute : ∀ i : Fin n, validRow (route i.castSucc) (route i.succ) := by
      intro i
      have h := hrows i.succ
      convert h using 1; congr 1
    have hlast : rest (Fin.last n) = t+t := by exact ht
    obtain ⟨z,hz⟩ := fileEvenOfLast n rest t hlast
    have hfirst := hrows (0 : Fin (n+1))
    have hf : F (fileCode (n+1)) e = F block ![e 0,z+z] := by
      rw [modelFileSucc,hz]
    have hh : F halfCode (fun _ => F (fileCode (n+1)) e) = F ones ![e 0+1,z+z] := by
      rw [hf,modelBlock,(modelDouble _).2]
    have hb := scanBlock (qs 0) (qs (1 : Fin (n+2))) hfirst (e 0) l z
    have hr := ih route hroute rest (F block ![e 0,l]) hlast
    rw [modelCostSucc,hh]
    change F PA194Stepper.stepper ![F addCode ![((1 : M)+1)+e 0,F (costCode n) rest],_] = _
    rw [PA194StepperCompose.modelStepperCompose,hb]
    rw [hz,(modelDouble z).2] at hr
    have hroute0 : route 0 = qs (1 : Fin (n+2)) := by congr 1
    rw [hroute0] at hr
    rw [hr,modelLeftSucc]
    rfl
def sevenControls : Fin 8 → Nat := ![106,71,95,114,68,93,113,14]
theorem sevenRows : ∀ i : Fin 7, validRow (sevenControls i.castSucc) (sevenControls i.succ) := by
  intro i
  fin_cases i <;> unfold validRow <;> decide +kernel
/-- Exact seven-block pinned traversal. The eight-entry vector holds seven
model-valued registers and an even remaining-file code. -/
theorem scanSeven (e : Fin 8 → M) (l t : M) (ht : e (Fin.last 7) = t+t) :
    F PA194Stepper.stepper ![F (costCode 7) e,F pairCode ![modelNumeral M 106,
      F pairCode ![l,F halfCode (fun _ => F (fileCode 7) e)]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![F (leftCode 7) (Fin.cases l e),t]] := by
  have h := scanFile 7 sevenControls sevenRows e l t ht
  exact h
#print axioms scanSeven
#print axioms sevenRows
#print axioms scanFile
#print axioms scanBlock
end models
end PA194FileTraversal
