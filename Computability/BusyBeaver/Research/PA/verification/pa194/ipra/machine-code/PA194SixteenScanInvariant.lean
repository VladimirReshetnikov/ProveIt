import PA194SixteenTransition
import PA194Stepper
import PackedDecoderModel
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
namespace PA194SixteenScanInvariant
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open PA194UnaryRuns PA194SixteenTransition PA194Stepper PackedDecoderModel TableDispatch

def k : Semiterm language Nat 1 := .bvar 0
def total : Semiterm language Nat 1 := .fvar 0
def left : Semiterm language Nat 1 := .fvar 1
def right : Semiterm language Nat 1 := .fvar 2
def state : Semiterm language Nat 1 := .func (TableDispatch.constantCode 16) ![.func (.zero 0) Fin.elim0]
def one : Semiterm language Nat 1 := .func oneCode Fin.elim0
def app2 (f : Code 2) (a b : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a,b]
def pack (l r : Semiterm language Nat 1) : Semiterm language Nat 1 := app2 pairCode state (app2 pairCode l r)
def beginConfig : Semiterm language Nat 1 := pack (app2 ones total left) (app2 addCode (app2 addCode right right) one)
def endConfig : Semiterm language Nat 1 := pack (app2 ones (app2 subCode total k) left) (app2 ones (app2 addCode k one) right)
def body : Semiformula language Nat 1 := .or
  (.rel Language.ORing.Rel.lt ![total,k])
  (.rel Language.ORing.Rel.eq ![app2 stepper k beginConfig,endConfig])
theorem body_open : body.Open := by simp [body,Semiformula.Open,Semiformula.qr]

def app2Closed (f : Code 2) (a b : TermN 3) : TermN 3 := .func f ![a,b]
def stateClosed : TermN 3 := .func (constantCode 16) ![.func (.zero 0) Fin.elim0]
def packClosed (l r : TermN 3) : TermN 3 := app2Closed pairCode stateClosed (app2Closed pairCode l r)
def fullLeft : TermN 3 := app2Closed stepper #0 (packClosed (app2Closed ones #0 #1) (app2Closed addCode (app2Closed addCode #2 #2) (.func oneCode Fin.elim0)))
def fullRight : TermN 3 := packClosed #1 (app2Closed ones (app2Closed addCode #0 (.func oneCode Fin.elim0)) #2)
def fullScanSentence : Sentence language := equalClosure (n := 3) fullLeft fullRight

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 (x : M) (e : Nat → M) (f : Code 2) (a b : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app2 f a b) = F f ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_pair ![x] e a b

theorem valState (x : M) (e : Nat → M) : Semiterm.val ![x] e state = modelNumeral M 16 := by
  have h : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
    (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,Semiterm.val_func]
  have hv : (Semiterm.val ![x] e ∘ ![(.func (.zero 0) Fin.elim0 : Semiterm language Nat 1)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,h]
    rfl
  rw [hv]
  exact modelConstant 16 _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valOne (x : M) (e : Nat → M) : Semiterm.val ![x] e one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem body_eval (x : M) (e : Nat → M) : body.Eval ![x] e ↔
    e 0 < x ∨
    F stepper ![x,F pairCode ![modelNumeral M 16,F pairCode ![F ones ![e 0,e 1],e 2+e 2+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![F ones ![F subCode ![e 0,x],e 1],F ones ![x+1,e 2]]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    exact val_pair ![x] e a b
  rw [hv]
  simp [k,total,left,right,beginConfig,endConfig,pack,valApp2,valState,valOne,Semiterm.val_bvar,Semiterm.val_fvar, Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

/-- A partial leftward zero scan from any model configuration. -/
theorem modelPartialScan (n time l r : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    time ≤ n →
    F stepper ![time,F pairCode ![modelNumeral M 16,F pairCode ![F ones ![n,l],r+r+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![F ones ![F subCode ![n,time],l],F ones ![time+1,r]]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun i => if i=0 then n else if i=1 then l else r
  have h0 : e 0 = n := by simp [e]
  have h1 : e 1 = l := by simp [e]
  have h2 : e 2 = r := by simp [e]
  have main : body.Eval ![time] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      right
      rw [h0,h1,h2]
      have hz : F stepper ![(0 : M),F pairCode ![modelNumeral M 16,F pairCode ![F ones ![n,l],r+r+1]]] =
          F pairCode ![modelNumeral M 16,F pairCode ![F ones ![n,l],r+r+1]] := modelStepperZero _
      have ho : F ones ![(0 : M)+1,r] = r+r+1 := by
        rw [zero_add]
        have hs : F Code.succ (fun _ => (0 : M)) = (1 : M) := by
          have hh := (modelAddOne (0 : M)).symm
          change F Code.succ (fun _ => (0 : M)) = (0 : M)+1 at hh
          simpa using hh
        have hh := modelOnesSucc (0 : M) r
        rw [modelOnesZero,hs] at hh
        exact hh
      have hsub : F subCode ![n,(0 : M)] = n := PRASubtraction.modelSubZero n
      rw [hz,ho,hsub]
    · intro u hu
      apply (body_eval (F Code.succ (fun _ => u)) e).mpr
      rw [h0,h1,h2]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      by_cases hbound : n < u+1
      · exact Or.inl hbound
      · right
        have hle : u+1 ≤ n := le_of_not_gt hbound
        have hu_lt : u < n := lt_of_lt_of_le (lt_add_one u) hle
        have hu' := (body_eval u e).mp hu
        rw [h0,h1,h2] at hu'
        have prev := hu'.resolve_left (not_lt_of_ge (le_of_lt hu_lt))
        have subeq : F subCode ![n,u] = F subCode ![n,u+1] + 1 := by
          rw [modelSubAsTsub,modelSubAsTsub]
          have hn : (u+1) + (n-(u+1)) = n := add_tsub_cancel_of_le hle
          calc
            n-u = ((u+1)+(n-(u+1)))-u := congrArg (fun z => z-u) hn.symm
            _ = (n-(u+1))+1 := by simp [add_assoc,add_comm]
        have hones : F ones ![F subCode ![n,u],l] =
            F ones ![F subCode ![n,u+1],l] + F ones ![F subCode ![n,u+1],l] + 1 := by
          rw [subeq]
          change F ones ![F addCode ![F subCode ![n,u+1],F oneCode Fin.elim0],l] = _
          rw [modelAddOne,modelOnesSucc]
        have hstep : F stepper ![u+1,F pairCode ![modelNumeral M 16,F pairCode ![F ones ![n,l],r+r+1]]] =
            F PackedClock.encodedStep (fun _ => F stepper ![u,F pairCode ![modelNumeral M 16,F pairCode ![F ones ![n,l],r+r+1]]]) := by
          change F stepper ![F addCode ![u,F oneCode Fin.elim0],_] = _
          rw [modelAddOne,modelStepperSucc]
        have hleft : F ones ![F subCode ![n,u],l] =
            F ones ![F subCode ![n,u+1],l] + F ones ![F subCode ![n,u+1],l] + 1 := hones
        have hright : F ones ![(u+1)+1,r] =
            F ones ![u+1,r] + F ones ![u+1,r] + 1 := by
          change F ones ![F addCode ![u+1,F oneCode Fin.elim0],r] = _
          rw [modelAddOne,modelOnesSucc]
        have hodd : F ones ![u+1,r] = F ones ![u,r]+F ones ![u,r]+1 := by
          change F ones ![F addCode ![u,F oneCode Fin.elim0],r] = _
          rw [modelAddOne,modelOnesSucc]
        rw [hstep,prev,hleft,hodd,modelPackedSixteenTransition,←hodd,←hright]
  have h := (body_eval time e).mp main
  rw [h0,h1,h2] at h
  intro hle
  exact h.resolve_left (not_lt_of_ge hle)

theorem modelFullScan (n l r : M) :
    F stepper ![n,F pairCode ![modelNumeral M 16,F pairCode ![F ones ![n,l],r+r+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![l,F ones ![n+1,r]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelPartialScan n n l r le_rfl
  have hsub : F subCode ![n,n] = (0 : M) := by rw [modelSubAsTsub]; simp
  have hzero : F ones ![(0 : M),l] = l := modelOnesZero l
  rw [hsub,hzero] at h
  exact h

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valClosed2 (e : Fin 3 → M) (f : Code 2) (a b : TermN 3) :
    Semiterm.val e Empty.elim (app2Closed f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2Closed,Semiterm.val_func]
  congr 1
  exact val_term_pair e a b

theorem valClosedState (e : Fin 3 → M) : Semiterm.val e Empty.elim stateClosed = modelNumeral M 16 := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 3)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [stateClosed,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN 3)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant 16 _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valClosedOne (e : Fin 3 → M) : Semiterm.val e Empty.elim (.func oneCode Fin.elim0 : TermN 3) = (1 : M) := by
  simp only [Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem modelFullScanSentence : M↓[language] ⊧ fullScanSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [fullLeft,fullRight,packClosed,valClosed2,valClosedState,valClosedOne,Semiterm.val_bvar]
  exact modelFullScan (e 0) (e 1) (e 2)

#print axioms modelFullScan

#print axioms modelPartialScan

#print axioms body_eval
end models

theorem PRA_proves_fullScanSentence : PRA ⊢ fullScanSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelFullScanSentence
#print axioms PRA_proves_fullScanSentence
end PA194SixteenScanInvariant
