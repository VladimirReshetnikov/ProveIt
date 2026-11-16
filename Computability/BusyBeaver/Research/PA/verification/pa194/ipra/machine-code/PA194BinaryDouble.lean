import BinaryTapeCodes
import DiophantineConsistency.PRAModelIOpenPairing
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
namespace PA194BinaryDouble
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open BinaryTapeCodes

def unary {n : Nat} (f : Code 1) (x : Code n) : Code n := .comp f (.cons x (.nil n))

def doubleCode : Code 1 := bin addCode (.proj 0) (.proj 0)
def parityDouble : Code 1 := unary parityCode doubleCode
def halfDouble : Code 1 := unary halfCode doubleCode

def body : Semiformula language Nat 1 := .and
  (.rel Language.ORing.Rel.eq ![.func parityDouble ![.bvar 0],.func (.zero 0) Fin.elim0])
  (.rel Language.ORing.Rel.eq ![.func halfDouble ![.bvar 0],.bvar 0])
theorem body_open : body.Open := by simp [body,Semiformula.Open,Semiformula.qr]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem body_eval (x : M) (e : Nat → M) : body.Eval ![x] e ↔
    F parityDouble (fun _ => x) = (0 : M) ∧ F halfDouble (fun _ => x) = x := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz (v : Fin 1 → M) : (Semiterm.val v e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one, hz]
  intro _
  rfl

theorem double_eval (x : M) : F doubleCode (fun _ => x) = x+x := by
  rw [doubleCode,modelBin,modelProjection]
  rfl

theorem modelUnary {n : Nat} (f : Code 1) (a : Code n) (e : Fin n → M) :
    F (unary f a) e = F f (fun _ => F a e) := by
  rw [unary, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

theorem parityDouble_eval (x : M) : F parityDouble (fun _ => x) = F parityCode (fun _ => x+x) := by
  rw [parityDouble, modelUnary, double_eval]
theorem halfDouble_eval (x : M) : F halfDouble (fun _ => x) = F halfCode (fun _ => x+x) := by
  rw [halfDouble, modelUnary, double_eval]

theorem paritySucc (x : M) : F parityCode (fun _ => x+1) =
    F isZeroCode (fun _ => F parityCode (fun _ => x)) := by
  change F parityCode (fun _ => F addCode ![x,F oneCode Fin.elim0]) = _
  rw [modelAddOne,modelParitySucc]

theorem halfSucc (x : M) : F halfCode (fun _ => x+1) =
    F halfCode (fun _ => x) + F parityCode (fun _ => x) := by
  change F halfCode (fun _ => F addCode ![x,F oneCode Fin.elim0]) = _
  rw [modelAddOne,modelHalfSucc]
  rfl

theorem isZeroZero : F isZeroCode (fun _ => (0 : M)) = (1 : M) := modelIsZeroZero
theorem isZeroOne : F isZeroCode (fun _ => (1 : M)) = (0 : M) := by
  change F isZeroCode (fun _ => F oneCode Fin.elim0) = _
  rw [modelOneSuccZero,modelIsZeroSucc]
  rfl

theorem modelDouble (x : M) :
    F parityCode (fun _ => x+x) = (0 : M) ∧ F halfCode (fun _ => x+x) = x := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun _ => x
  have main : body.Eval ![x] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      rw [parityDouble_eval,halfDouble_eval]
      simp only [zero_add]
      exact ⟨modelParityZero,modelHalfZero⟩
    · intro y hy
      apply (body_eval (F Code.succ (fun _ => y)) e).mpr
      rw [parityDouble_eval,halfDouble_eval]
      have hi := (body_eval y e).mp hy
      rw [parityDouble_eval,halfDouble_eval] at hi
      have hs : F Code.succ (fun _ => y) = y+1 := (modelAddOne y).symm
      rw [hs]
      have hd : (y+1)+(y+1) = ((y+y)+1)+1 := by simp [add_assoc,add_comm,add_left_comm]
      rw [hd,paritySucc,halfSucc,paritySucc,halfSucc,hi.1,hi.2]
      rw [isZeroZero,isZeroOne]
      simp
  have hm := (body_eval x e).mp main
  rw [parityDouble_eval,halfDouble_eval] at hm
  exact hm

theorem modelOdd (x : M) :
    F parityCode (fun _ => (x+x)+1) = (1 : M) ∧ F halfCode (fun _ => (x+x)+1) = x := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelDouble x
  rw [paritySucc,halfSucc,h.1,h.2,isZeroZero]
  simp
#print axioms modelOdd

#print axioms modelDouble

#print axioms body_eval
end models
end PA194BinaryDouble
