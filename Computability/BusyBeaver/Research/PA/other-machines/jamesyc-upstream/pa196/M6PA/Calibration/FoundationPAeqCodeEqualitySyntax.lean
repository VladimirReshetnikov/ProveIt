module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTheory
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
@[expose] public section

/-! Typed wrappers for the existing PAeq numeric constructors, not semantic
equality or an alternative source encoding. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n m : Nat}
noncomputable def typedEq (s t : Bootstrapping.Semiterm V Presentation.language n) :
    Bootstrapping.Semiformula V Presentation.language n := .rel Presentation.Rel.eq ![s,t]
noncomputable def typedZero : Bootstrapping.Semiterm V Presentation.language n :=
  .func Presentation.Func.zero ![]
noncomputable def typedSucc (s : Bootstrapping.Semiterm V Presentation.language n) :
    Bootstrapping.Semiterm V Presentation.language n := .func Presentation.Func.succ ![s]
noncomputable def typedAdd (s t : Bootstrapping.Semiterm V Presentation.language n) :
    Bootstrapping.Semiterm V Presentation.language n := .func Presentation.Func.add ![s,t]
noncomputable def typedMul (s t : Bootstrapping.Semiterm V Presentation.language n) :
    Bootstrapping.Semiterm V Presentation.language n := .func Presentation.Func.mul ![s,t]

@[simp] theorem typedEq_val (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedEq s t).val=equalityCode s.val t.val := by simp [typedEq,equalityCode]; rfl
@[simp] theorem typedZero_val : (typedZero : Bootstrapping.Semiterm V Presentation.language n).val=zeroCode := by
  simp [typedZero,zeroCode]; rfl
@[simp] theorem typedSucc_val (s : Bootstrapping.Semiterm V Presentation.language n) :
    (typedSucc s).val=qqFunc 1 1 (s.val∷0) := by
  simp [typedSucc]
  change ((1:Nat):V)=1
  simp
@[simp] theorem typedAdd_val (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedAdd s t).val=qqFunc 2 2 (s.val∷t.val∷0) := by simp [typedAdd]; rfl
@[simp] theorem typedMul_val (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedMul s t).val=qqFunc 2 3 (s.val∷t.val∷0) := by simp [typedMul]; rfl

@[simp] theorem typedEq_subst (w : SemitermVec V Presentation.language n m) (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedEq s t).subst w=typedEq (s.subst w) (t.subst w) := by simp [typedEq]
@[simp] theorem typedEq_shift (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedEq s t).shift=typedEq s.shift t.shift := by simp [typedEq]
@[simp] theorem typedZero_subst (w : SemitermVec V Presentation.language n m) :
    (typedZero : Bootstrapping.Semiterm V Presentation.language n).subst w=typedZero := by simp [typedZero]
@[simp] theorem typedSucc_subst (w : SemitermVec V Presentation.language n m) (s : Bootstrapping.Semiterm V Presentation.language n) :
    (typedSucc s).subst w=typedSucc (s.subst w) := by simp [typedSucc]
@[simp] theorem typedAdd_subst (w : SemitermVec V Presentation.language n m) (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedAdd s t).subst w=typedAdd (s.subst w) (t.subst w) := by simp [typedAdd]
@[simp] theorem typedMul_subst (w : SemitermVec V Presentation.language n m) (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedMul s t).subst w=typedMul (s.subst w) (t.subst w) := by simp [typedMul]
@[simp] theorem typedZero_shift : (typedZero : Bootstrapping.Semiterm V Presentation.language n).shift=typedZero := by simp [typedZero]
@[simp] theorem typedSucc_shift (s : Bootstrapping.Semiterm V Presentation.language n) :
    (typedSucc s).shift=typedSucc s.shift := by simp [typedSucc]
@[simp] theorem typedAdd_shift (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedAdd s t).shift=typedAdd s.shift t.shift := by simp [typedAdd]
@[simp] theorem typedMul_shift (s t : Bootstrapping.Semiterm V Presentation.language n) :
    (typedMul s t).shift=typedMul s.shift t.shift := by simp [typedMul]

@[simp] theorem typed_quote_eq (s t : SyntacticSemiterm Presentation.language n) :
    (⌜Presentation.eq s t⌝ : Bootstrapping.Semiformula V Presentation.language n)=typedEq ⌜s⌝ ⌜t⌝ := by
  simp [Presentation.eq,typedEq]; rfl
@[simp] theorem typed_quote_zero : (⌜(Presentation.zero : SyntacticSemiterm Presentation.language n)⌝ : Bootstrapping.Semiterm V Presentation.language n)=typedZero := by
  simp [Presentation.zero,typedZero]; funext i; exact i.elim0
@[simp] theorem typed_quote_succ (s : SyntacticSemiterm Presentation.language n) :
    (⌜Presentation.succ s⌝ : Bootstrapping.Semiterm V Presentation.language n)=typedSucc ⌜s⌝ := by
  simp [Presentation.succ,typedSucc]; funext i; fin_cases i; rfl
@[simp] theorem typed_quote_add (s t : SyntacticSemiterm Presentation.language n) :
    (⌜Presentation.add s t⌝ : Bootstrapping.Semiterm V Presentation.language n)=typedAdd ⌜s⌝ ⌜t⌝ := by
  simp [Presentation.add,typedAdd]; funext i; fin_cases i <;> rfl
@[simp] theorem typed_quote_mul (s t : SyntacticSemiterm Presentation.language n) :
    (⌜Presentation.mul s t⌝ : Bootstrapping.Semiterm V Presentation.language n)=typedMul ⌜s⌝ ⌜t⌝ := by
  simp [Presentation.mul,typedMul]; funext i; fin_cases i <;> rfl
#print axioms typedEq_val
#print axioms typedZero_val
#print axioms typedSucc_val
#print axioms typedAdd_val
#print axioms typedMul_val
#print axioms typedEq_subst
#print axioms typedEq_shift
#print axioms typedZero_subst
#print axioms typedSucc_subst
#print axioms typedAdd_subst
#print axioms typedMul_subst
#print axioms typedZero_shift
#print axioms typedSucc_shift
#print axioms typedAdd_shift
#print axioms typedMul_shift
#print axioms typed_quote_eq
#print axioms typed_quote_zero
#print axioms typed_quote_succ
#print axioms typed_quote_add
#print axioms typed_quote_mul
end M6.PA.FoundationPAeqCode
