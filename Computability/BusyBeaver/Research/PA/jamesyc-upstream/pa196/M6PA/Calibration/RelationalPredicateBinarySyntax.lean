module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryND
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
abbrev SF (n : Nat) := Bootstrapping.Semiformula V L n
abbrev ST (n : Nat) := Bootstrapping.Semiterm V L n

noncomputable def unary (P : SF (V:=V) 1) (x : ST (V:=V) n) : SF (V:=V) n := P.subst ![x]
noncomputable def ternary (R : SF (V:=V) 3) (x y z : ST (V:=V) n) : SF (V:=V) n := R.subst ![x,y,z]
noncomputable def witness (D P : SF (V:=V) 1) : SF (V:=V) 0 := ∃¹ (D ⋏ P)
noncomputable def result (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1) : SF (V:=V) 0 :=
  ∃¹ (unary D (Semiterm.bvar 0) ⋏
    (∃¹ ∃¹ (unary P (Semiterm.bvar 1) ⋏
      (unary Q (Semiterm.bvar 0) ⋏ ternary R (Semiterm.bvar 1) (Semiterm.bvar 0) (Semiterm.bvar 2)))))
noncomputable def outputAt (D : SF (V:=V) 1) (R : SF (V:=V) 3) (x y : ST (V:=V) n) : SF (V:=V) n :=
  ∃¹ (unary D (Semiterm.bvar 0) ⋏ ternary R x.bShift y.bShift (Semiterm.bvar 0))
noncomputable def totality (D : SF (V:=V) 1) (R : SF (V:=V) 3) : SF (V:=V) 0 :=
  ∀¹ (unary D (Semiterm.bvar 0) 🡒
    ∀¹ (unary D (Semiterm.bvar 0) 🡒 outputAt D R (Semiterm.bvar 1) (Semiterm.bvar 0)))
noncomputable def statement (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1) : SF (V:=V) 0 :=
  (witness D P ⋏ witness D Q) 🡒 result D R P Q

@[simp] theorem unary_shift (P : SF (V:=V) 1) (x : ST (V:=V) n) :
    (unary P x).shift=unary P.shift x.shift := by simp [unary,Bootstrapping.Semiformula.shift_substs]
@[simp] theorem ternary_shift (R : SF (V:=V) 3) (x y z : ST (V:=V) n) :
    (ternary R x y z).shift=ternary R.shift x.shift y.shift z.shift := by
  simp [ternary,Bootstrapping.Semiformula.shift_substs,Matrix.comp_vecCons'']
@[simp] theorem unary_subst (P : SF (V:=V) 1) (x : ST (V:=V) n) (w : Bootstrapping.SemitermVec V L n m) :
    (unary P x).subst w=unary P (x.subst w) := by
  simp [unary,Bootstrapping.Semiformula.substs_substs,Matrix.comp_vecCons'']
@[simp] theorem ternary_subst (R : SF (V:=V) 3) (x y z : ST (V:=V) n) (w : Bootstrapping.SemitermVec V L n m) :
    (ternary R x y z).subst w=ternary R (x.subst w) (y.subst w) (z.subst w) := by
  simp [ternary,Bootstrapping.Semiformula.substs_substs,Matrix.comp_vecCons'']

#print axioms unary_shift
#print axioms ternary_shift
#print axioms unary_subst
#print axioms ternary_subst
end M6.PA.RelationalPredicateBinary

