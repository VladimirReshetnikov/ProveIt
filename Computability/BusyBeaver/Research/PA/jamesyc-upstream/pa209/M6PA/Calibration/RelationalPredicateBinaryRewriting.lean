module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinarySyntax
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

@[simp] theorem witness_shift (D P : SF (V:=V) 1) :
    (witness D P).shift=witness D.shift P.shift := by simp [witness]
@[simp] theorem result_shift (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1) :
    (result D R P Q).shift=result D.shift R.shift P.shift Q.shift := by simp [result]
@[simp] theorem outputAt_shift (D : SF (V:=V) 1) (R : SF (V:=V) 3) (x y : ST (V:=V) n) :
    (outputAt D R x y).shift=outputAt D.shift R.shift x.shift y.shift := by
  simp [outputAt,Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem totality_shift (D : SF (V:=V) 1) (R : SF (V:=V) 3) :
    (totality D R).shift=totality D.shift R.shift := by simp [totality]
@[simp] theorem outputAt_subst (D : SF (V:=V) 1) (R : SF (V:=V) 3)
    (x y : ST (V:=V) n) (w : Bootstrapping.SemitermVec V L n m) :
    (outputAt D R x y).subst w=outputAt D R (x.subst w) (y.subst w) := by
  simp [outputAt]
@[simp] theorem outputAt_free (D : SF (V:=V) 1) (R : SF (V:=V) 3) (x y : ST (V:=V) 0) :
    (unary D (Semiterm.bvar 0) ⋏ ternary R x.bShift y.bShift (Semiterm.bvar 0)).free=
      unary D.shift (Semiterm.fvar 0) ⋏ ternary R.shift x.shift y.shift (Semiterm.fvar 0) := by
  simp [Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm]

#print axioms result_shift
#print axioms outputAt_subst
#print axioms outputAt_free
end M6.PA.RelationalPredicateBinary

