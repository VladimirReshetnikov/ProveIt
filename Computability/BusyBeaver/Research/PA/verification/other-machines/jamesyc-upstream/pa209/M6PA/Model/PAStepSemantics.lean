module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAStepFormula
@[expose] public section

namespace M6.Arithmetic.PA.StepFormula
open M6
open NatTape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem controlCode_injective : Function.Injective controlCode := by
  intro a b h
  cases a <;> cases b <;> simp [controlCode] at h ⊢
  · omega
  · omega
  · exact Fin.ext h

theorem rowRelation_step (src : WorkingState) (read : Bool)
    (c c' : NatTape.Configuration)
    (h : rowRelation src read (controlCode c.control) c.left c.right
      (controlCode c'.control) c'.left c'.right) :
    NatTape.step c = some c' := by
  rcases c with ⟨q,l,r⟩
  rcases c' with ⟨q',l',r'⟩
  dsimp [rowRelation] at h
  rcases h with ⟨hq,hq',h⟩
  have hq0 : q = some src := controlCode_injective hq
  have hq1 : q' = (row src read).next := controlCode_injective hq'
  subst q
  subst q'
  cases hd : (row src read).right
  · simp only [hd, Bool.false_eq_true, ite_false] at h
    rcases h with ⟨t,u,e,he,hl,hr,hl',hr'⟩
    subst r
    subst l'
    subst r'
    have hrb : (2 * t + read.toNat).testBit 0 = read := push_head read t
    have hrd : (2 * t + read.toNat) / 2 = t := push_div read t
    simp only [NatTape.step, hrb, Option.map_some, advance, hd,
      Bool.false_eq_true, ite_false, hrd]
    rcases he with he | he <;> subst e <;> subst l
    · simp [push, Nat.testBit_zero, Nat.mul_comm]
    · simp [push, Nat.testBit_zero, Nat.mul_comm]; omega
  · simp only [hd, ite_true] at h
    rcases h with ⟨t,hr,hl,hr'⟩
    subst r
    subst l'
    subst r'
    have hrb : (2 * t + read.toNat).testBit 0 = read := push_head read t
    have hrd : (2 * t + read.toNat) / 2 = t := push_div read t
    simp [NatTape.step,hrb,advance,hd,push,hrd]

theorem nat_split (n : Nat) : n = 2 * (n / 2) + (n.testBit 0).toNat := by
  by_cases h : n % 2 = 1 <;> simp [Nat.testBit_zero, h] <;> omega

theorem step_rowRelation (c c' : NatTape.Configuration)
    (h : NatTape.step c = some c') :
    relation (controlCode c.control) c.left c.right
      (controlCode c'.control) c'.left c'.right := by
  cases hq : c.control with
  | none => simp [NatTape.step,hq] at h
  | some src =>
    simp only [NatTape.step,hq,Option.map_some,Option.some.injEq] at h
    subst c'
    refine ⟨src,c.right.testBit 0,?_,?_,?_⟩
    · rfl
    · cases hd : (row src (c.right.testBit 0)).right <;>
        simp only [advance,hd,Bool.false_eq_true,ite_false,ite_true]
    · cases hd : (row src (c.right.testBit 0)).right
      · simp only [hd,Bool.false_eq_true,ite_false,advance]
        refine ⟨c.right / 2,c.left / 2,(c.left.testBit 0).toNat,?_,
          nat_split c.left,nat_split c.right,rfl,rfl⟩
        cases c.left.testBit 0 <;> simp
      · simp only [hd,ite_true,advance]
        exact ⟨c.right / 2,nat_split c.right,rfl,rfl⟩

theorem relation_iff_step (c c' : NatTape.Configuration) :
    relation (controlCode c.control) c.left c.right
      (controlCode c'.control) c'.left c'.right ↔ NatTape.step c = some c' := by
  constructor
  · rintro ⟨src,read,h⟩
    exact rowRelation_step src read c c' h
  · exact step_rowRelation c c'

/-- Full 430-row arithmetic formula corresponds to the exact machine step.
This is standard-model adequacy; an internal PA trace proof is a separate goal. -/
theorem formula_iff_step (c c' : NatTape.Configuration) :
    (Nat ⊧/![controlCode c.control,c.left,c.right,
      controlCode c'.control,c'.left,c'.right] formula) ↔
        NatTape.step c = some c' :=
  (formula_correct _ _ _ _ _ _).trans (relation_iff_step c c')

#print axioms formula_iff_step
#print axioms rowRelation_step
#print axioms relation_iff_step
end M6.Arithmetic.PA.StepFormula

