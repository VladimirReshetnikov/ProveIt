import PA194OneSpareIterate
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelLoopIteration
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRAOpenInduction
open PA194OneSpareIterate PA194GenericRightScan PA194StateOne PA194Stepper TableDispatch BinaryTapeCodes PA194UnaryRuns PA194BinaryDouble PA194Site28CarryCell

def iterBody (next : Code 1) : Code 3 := unary next (.proj 1)
def iterCode (next : Code 1) : Code 2 := .prec (.proj 0) (iterBody next)
def timeBody (next cost : Code 1) : Code 3 :=
  bin addCode (.proj 1) (unary cost (bin (iterCode next) (.proj 0) (.proj 2)))
def timeCode (next cost : Code 1) : Code 2 := .prec (.zero 1) (timeBody next cost)
def ix : Semiterm language Nat 1 := .bvar 0
def bound : Semiterm language Nat 1 := .fvar 0
def seed : Semiterm language Nat 1 := .fvar 1
def app1 (f : Code 1) (a : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a]
def app2 (f : Code 2) (a b : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a,b]
def body (next cost frame : Code 1) : Semiformula language Nat 1 := .or
  (.rel Language.ORing.Rel.lt ![bound,ix])
  (.rel Language.ORing.Rel.eq ![app2 stepper (app2 (timeCode next cost) ix seed) (app1 frame seed),app1 frame (app2 (iterCode next) ix seed)])
theorem body_open (next cost frame : Code 1) : (body next cost frame).Open := by simp [body,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelIterZero (next : Code 1) (x : M) : F (iterCode next) ![(0 : M),x] = x := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) (iterBody next) (fun _ => x)
  rw [modelProjection] at h
  have hs : Fin.cases (F (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => x) = ![(0 : M),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h
theorem modelIterSucc (next : Code 1) (n x : M) : F (iterCode next) ![F Code.succ (fun _ => n),x] = F next (fun _ => F (iterCode next) ![n,x]) := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) (iterBody next) ![n,x]
  have hs : Fin.cases (F Code.succ (fun _ => ![n,x] 0)) (fun i => ![n,x] i.succ) = ![F Code.succ (fun _ => n),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  have hv : (fun i : Fin 1 => ![n,x] i.succ) = (fun _ => x) := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  simp only [Matrix.cons_val_zero] at h
  change F (iterCode next) ![F Code.succ (fun _ => n),x] = F (iterBody next) (Fin.cases n (Fin.cases (F (iterCode next) ![n,x]) (fun _ => x))) at h
  rw [h,iterBody,modelUnary,modelProjection]
  rfl
theorem modelTimeZero (next cost : Code 1) (x : M) : F (timeCode next cost) ![(0 : M),x] = (0 : M) := by
  have h := modelBase (M := M) (Code.zero 1) (timeBody next cost) (fun _ => x)
  have hz := PRAMultiplication.modelZero (M := M) (fun _ : Fin 1 => x)
  rw [hz] at h
  have hs : Fin.cases (F (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => x) = ![(0 : M),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h
theorem modelTimeSucc (next cost : Code 1) (n x : M) : F (timeCode next cost) ![F Code.succ (fun _ => n),x] =
    F (timeCode next cost) ![n,x] + F cost (fun _ => F (iterCode next) ![n,x]) := by
  have h := modelStep (M := M) (Code.zero 1) (timeBody next cost) ![n,x]
  have hs : Fin.cases (F Code.succ (fun _ => ![n,x] 0)) (fun i => ![n,x] i.succ) = ![F Code.succ (fun _ => n),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  have hv : (fun i : Fin 1 => ![n,x] i.succ) = (fun _ => x) := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  simp only [Matrix.cons_val_zero] at h
  change F (timeCode next cost) ![F Code.succ (fun _ => n),x] = F (timeBody next cost) (Fin.cases n (Fin.cases (F (timeCode next cost) ![n,x]) (fun _ => x))) at h
  rw [h,timeBody,modelBin,modelUnary,modelBin]
  simp only [modelProjection,Fin.cases_zero,Fin.cases_succ]
  rfl
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 (x : M) (e : Nat → M) (f : Code 1) (a : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app1 f a) = F f (fun _ => Semiterm.val ![x] e a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 (x : M) (e : Nat → M) (f : Code 2) (a b : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app2 f a b) = F f ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  funext i; fin_cases i <;> rfl

theorem body_eval (next cost frame : Code 1) (x : M) (e : Nat → M) :
    (body next cost frame).Eval ![x] e ↔ e 0 < x ∨
      F stepper ![F (timeCode next cost) ![x,e 1],F frame (fun _ => e 1)] =
        F frame (fun _ => F (iterCode next) ![x,e 1]) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (body next cost frame) ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp [ix,bound,seed,valApp1,valApp2,Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

theorem modelIteration (next cost frame : Code 1) (limit start steps : M)
    (hstep : ∀ i, i < limit →
      F stepper ![F cost (fun _ => F (iterCode next) ![i,start]),F frame (fun _ => F (iterCode next) ![i,start])] =
        F frame (fun _ => F next (fun _ => F (iterCode next) ![i,start]))) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    steps ≤ limit → F stepper ![F (timeCode next cost) ![steps,start],F frame (fun _ => start)] =
      F frame (fun _ => F (iterCode next) ![steps,start]) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun j => if j=0 then limit else start
  have h0 : e 0 = limit := by simp [e]
  have h1 : e 1 = start := by simp [e]
  have main : (body next cost frame).Eval ![steps] e := by
    apply modelOpenInduction (M := M) (body next cost frame) (body_open next cost frame) e
    · apply (body_eval next cost frame (0 : M) e).mpr
      right
      rw [h1,modelTimeZero,modelIterZero]
      exact modelStepperZero _
    · intro u hu
      apply (body_eval next cost frame (F Code.succ (fun _ => u)) e).mpr
      rw [h0,h1]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      by_cases hbound : limit < u+1
      · exact Or.inl (by rw [hs]; exact hbound)
      · right
        have hle : u+1 ≤ limit := le_of_not_gt hbound
        have hlt : u < limit := lt_of_lt_of_le (lt_add_one u) hle
        have hu' := (body_eval next cost frame u e).mp hu
        rw [h0,h1] at hu'
        have prev := hu'.resolve_left (not_lt_of_ge (le_of_lt hlt))
        rw [modelTimeSucc,modelIterSucc]
        change F stepper ![F addCode ![F (timeCode next cost) ![u,start],F cost (fun _ => F (iterCode next) ![u,start])],_] = _
        rw [PA194StepperCompose.modelStepperCompose,prev,hstep u hlt]
  have h := (body_eval next cost frame steps e).mp main
  rw [h0,h1] at h
  intro hle
  exact h.resolve_left (not_lt_of_ge hle)
#print axioms modelIteration
#print axioms modelIterZero
#print axioms modelIterSucc
#print axioms modelTimeZero
#print axioms modelTimeSucc
end models
end PA194ModelLoopIteration
