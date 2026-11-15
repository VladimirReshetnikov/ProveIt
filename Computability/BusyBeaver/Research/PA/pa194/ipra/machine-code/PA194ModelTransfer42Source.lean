import PA194ModelLoopState
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelTransfer42Source
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction PackedDecoderModel PA194GenericRightScan PA194Site28CarryCell PA194Stepper PA194ModelLoopIteration PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch
abbrev T := Semiterm language Nat 1
def add (a b : T) : T := PA194ModelLoopIteration.app2 addCode a b
def pairT (a b : T) : T := PA194ModelLoopIteration.app2 pairCode a b
def sourceT (r : Fin 9 → T) (tail : T) : T :=
  pairT (PA194GenericRightScan.state 42)
    (pairT (r 0) (pairT (r 1) (pairT (r 2) (pairT (r 3) (pairT (r 4)
      (pairT (r 5) (pairT (r 6) (pairT (r 7) (pairT (r 8) tail)))))))))
def initialRegs (i : Fin 9) : T := .fvar i.val
def runningRegs (i : Fin 9) : T :=
  if i.val = 8 then add (.fvar 8) (.bvar 0)
  else if i.val = 7 then PA194ModelLoopIteration.app2 subCode (.fvar 7) (.bvar 0)
  else .fvar i.val
def body (advance : Code 1) : Semiformula language Nat 1 := .or
  (.rel Language.ORing.Rel.lt ![(.fvar 7 : T),(.bvar 0 : T)])
  (.rel Language.ORing.Rel.eq ![
    PA194ModelLoopIteration.app2 (iterCode advance) (.bvar 0) (sourceT initialRegs (.fvar 9)),
    sourceT runningRegs (.fvar 9)])
theorem body_open (advance : Code 1) : (body advance).Open := by simp [body,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
noncomputable def source (r : Fin 9 → M) (tail : M) : M :=
  pair (modelNumeral M 42)
    (pair (r 0) (pair (r 1) (pair (r 2) (pair (r 3) (pair (r 4)
      (pair (r 5) (pair (r 6) (pair (r 7) (pair (r 8) tail)))))))))
def running (r : Fin 9 → M) (i : M) : Fin 9 → M :=
  Function.update (Function.update r 8 (r 8+i)) 7 (F subCode ![r 7,i])
theorem body_eval (advance : Code 1) (x : M) (e : Nat → M) :
    (body advance).Eval ![x] e ↔ e 7 < x ∨
      F (iterCode advance) ![x,source (fun i => e i.val) (e 9)] = source (running (fun i => e i.val) x) (e 9) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (body advance) ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : T) : (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp [sourceT,pairT,add,initialRegs,runningRegs,source,running,PA194ModelLoopIteration.valApp2,
    PA194GenericRightScan.valState,Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one,
    modelPairCode,Function.update]
  rfl
theorem sourceIteration (advance : Code 1) (r : Fin 9 → M) (tail steps : M)
    (hstep : ∀ (v : Fin 9 → M) (m : M), v 7 = m+1 →
      F advance (fun _ => source v tail) = source
        (Function.update (Function.update v 8 (v 8+1)) 7 m) tail) :
    steps ≤ r 7 → F (iterCode advance) ![steps,source r tail] = source (running r steps) tail := by
  classical
  let e : Nat → M := fun j => if h : j<9 then r ⟨j,h⟩ else tail
  have he : (fun i : Fin 9 => e i.val) = r := by
    funext i
    simp [e,i.isLt]
  have he7 : e 7 = r 7 := by simp [e]
  have he9 : e 9 = tail := by simp [e]
  have main : (body advance).Eval ![steps] e := by
    apply modelOpenInduction (M := M) (body advance) (body_open advance) e
    · apply (body_eval advance (0 : M) e).mpr
      right
      rw [he,he9,modelIterZero]
      have hr : running r (0 : M) = r := by
        funext i
        have hz : F subCode ![r 7,(0 : M)]  = r 7 := PRASubtraction.modelSubZero _
        fin_cases i <;> simp [running,hz]
      rw [hr]
    · intro u hu
      apply (body_eval advance (F Code.succ (fun _ => u)) e).mpr
      rw [he,he7,he9]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      by_cases hb : r 7 < u+1
      · exact Or.inl (by rw [hs]; exact hb)
      · right
        have hle : u+1 ≤ r 7 := le_of_not_gt hb
        have hlt : u < r 7 := lt_of_lt_of_le (lt_add_one u) hle
        have prev := (body_eval advance u e).mp hu
        rw [he,he7,he9] at prev
        have prev := prev.resolve_left (not_lt_of_ge (le_of_lt hlt))
        have hsub : F subCode ![r 7,u] = F subCode ![r 7,u+1]+1 := by
          rw [modelSubAsTsub,modelSubAsTsub]
          have hn : (u+1)+(r 7-(u+1))  = r 7 := add_tsub_cancel_of_le hle
          calc
            r 7-u = ((u+1)+(r 7-(u+1)))-u := congrArg (fun z => z-u) hn.symm
            _ = (r 7-(u+1))+1 := by simp [add_assoc,add_comm]
        have hrun7 : running r u 7 = F subCode ![r 7,u+1]+1 := by simpa [running] using hsub
        have hnext := hstep (running r u) (F subCode ![r 7,u+1]) hrun7
        have hrun : Function.update (Function.update (running r u) 8 (running r u 8+1)) 7 (F subCode ![r 7,u+1]) = running r (u+1) := by
          funext i
          fin_cases i <;> simp [running,add_assoc]
        rw [modelIterSucc,prev,hnext,hrun,hs]
  have h := (body_eval advance steps e).mp main
  rw [he,he7,he9] at h
  intro hle
  exact h.resolve_left (not_lt_of_ge hle)
#print axioms sourceIteration
#print axioms body_eval
end models
end PA194ModelTransfer42Source
