import PA194ReturnFile
import PA194OnesCommute
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PA194ReturnFileMeaning
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194UnaryRuns PA194ReturnFile PA194OnesCommute
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelReturnBlock (v t : M) :
    F ones ![v,t+t+1]+F ones ![v,t+t+1] = F block ![v,t] := by
  rw [modelOnesCommute,modelBlock]
  have hs : F ones ![v+1,t] = F ones ![v,t]+F ones ![v,t]+1 := by
    change F ones ![F addCode ![v,F oneCode Fin.elim0],t] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hs]

/-- The numeric word 6 is the source runtime block for a one-valued
spare register followed by a blank suffix. -/
theorem modelSpareOne : F block ![(1 : M),(0 : M)] =
    ((((1 : M)+1)+1)+(((1 : M)+1)+1)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hs : F Code.succ (fun _ => (0 : M)) = (1 : M) := by
    have h := (modelAddOne (0 : M)).symm
    change F Code.succ (fun _ => (0 : M)) = (0 : M)+1 at h
    simpa using h
  have h1 := modelOnesSucc (0 : M) (0 : M)
  rw [modelOnesZero,hs] at h1
  have h2 := modelOnesSucc (1 : M) (0 : M)
  have hsucc : F Code.succ (fun _ => (1 : M)) = (1 : M)+1 := (modelAddOne (1 : M)).symm
  rw [hsucc,h1] at h2
  rw [modelBlock,h2]
  simp only [zero_add]
#print axioms modelSpareOne

def replaceLast (n : Nat) (e : Fin (n+1) → M) (t : M) : Fin (n+1) → M :=
  Fin.snoc (fun i => e i.castSucc) t

theorem modelReturnMeaning (n : Nat) (e : Fin (n+1) → M) (t : M) :
    F (returnCode n) (Fin.cases t e) = F (fileCode n) (replaceLast n e t) := by
  induction n generalizing t with
  | zero =>
    rw [modelReturnCodeZero]
    change t = F (.proj 0) (replaceLast 0 e t)
    rw [modelProjection]
    rfl
  | succ n ih =>
    rw [modelReturnCodeSucc,modelFileSucc,←modelReturnBlock]
    have hr := ih (fun i => e i.succ) t
    have h0 : (replaceLast (n+1) e t) 0 = e 0 := by
      change Fin.snoc _ _ (Fin.castSucc 0) = _
      rw [Fin.snoc_castSucc]
      rfl
    have hs : (fun i : Fin (n+1) => replaceLast (n+1) e t i.succ) =
        replaceLast n (fun i => e i.succ) t := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [replaceLast]
      · simp only [replaceLast,Fin.snoc_castSucc]
        have hj : j.castSucc.succ = j.succ.castSucc := by apply Fin.ext; rfl
        rw [hj,Fin.snoc_castSucc]
    have h1 : Fin.cases t e (1 : Fin (n+3)) = e 0 := rfl
    rw [h1,h0,hs]
    simp only [Fin.cases_zero,Fin.cases_succ]
    rw [hr]
#print axioms modelReturnBlock
#print axioms modelReturnMeaning
end models
end PA194ReturnFileMeaning
