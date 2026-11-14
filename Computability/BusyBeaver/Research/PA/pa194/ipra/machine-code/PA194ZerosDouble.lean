import PA194ZeroRuns
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
namespace PA194ZerosDouble
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open BinaryTapeCodes PA194BinaryDouble PA194ZeroRuns

def param : Semiterm language Nat 1 := .fvar 0
def counter : Semiterm language Nat 1 := .bvar 0
def app2 (f : Code 2) (a b : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a,b]
def body : Semiformula language Nat 1 := .rel Language.ORing.Rel.eq
  ![app2 zeros counter (app2 addCode param param),app2 addCode (app2 zeros counter param) (app2 zeros counter param)]
theorem body_open : body.Open := by simp [body,Semiformula.Open]
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
theorem valApp2 (n : M) (e : Nat → M) (f : Code 2) (a b : Semiterm language Nat 1) :
    Semiterm.val ![n] e (app2 f a b) = F f ![Semiterm.val ![n] e a,Semiterm.val ![n] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_pair ![n] e a b

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 (n : M) (e : Nat → M) (f : Code 1) (a : Semiterm language Nat 1) :
    Semiterm.val ![n] e (.func f ![a]) = F f (fun _ => Semiterm.val ![n] e a) := by
  simp only [Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem body_eval (n : M) (e : Nat → M) : body.Eval ![n] e ↔
    F zeros ![n,e 0+e 0] = F zeros ![n,e 0] + F zeros ![n,e 0] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![n] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![n] e (![a,b] i)) = ![Semiterm.val ![n] e a,Semiterm.val ![n] e b] := by
    exact val_pair ![n] e a b
  have hz : (Semiterm.val ![n] e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [valApp2,Semiterm.val_bvar,Semiterm.val_fvar,
    Matrix.cons_val_zero,Matrix.cons_val_one,param,counter]
  rfl

theorem modelZerosDouble (n x : M) : F zeros ![n,x+x] = F zeros ![n,x] + F zeros ![n,x] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun _ => x
  have main : body.Eval ![n] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      change F zeros ![(0 : M),x+x] = F zeros ![(0 : M),x]+F zeros ![(0 : M),x]
      rw [modelZerosZero,modelZerosZero]
    · intro k hk
      apply (body_eval (F Code.succ (fun _ => k)) e).mpr
      have ih := (body_eval k e).mp hk
      change F zeros ![k,x+x] = F zeros ![k,x]+F zeros ![k,x] at ih
      change F zeros ![F Code.succ (fun _ => k),x+x] =
        F zeros ![F Code.succ (fun _ => k),x]+F zeros ![F Code.succ (fun _ => k),x]
      rw [modelZerosSucc,modelZerosSucc,ih]
  exact (body_eval n e).mp main
#print axioms modelZerosDouble
end models
end PA194ZerosDouble
