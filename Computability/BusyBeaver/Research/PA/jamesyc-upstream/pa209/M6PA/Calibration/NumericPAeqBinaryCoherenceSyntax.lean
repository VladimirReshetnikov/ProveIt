module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorSyntax
public import M6PA.Calibration.RelationalPredicateBinaryRewriting
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def binaryPoint (D:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2)
    (x y b c r s:ST (V:=V) n) : SF (V:=V) n :=
  (unary D y ⋏ (unary D b ⋏ (unary D c ⋏ (binary R x y ⋏ (binary R b c ⋏
    (ternary F x b r ⋏ ternary F y c s)))))) 🡒 binary R r s
@[simp] theorem binaryPoint_shift (D:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2)
    (x y b c r s:ST (V:=V) n) : (binaryPoint D F R x y b c r s).shift=
    binaryPoint D.shift F.shift R.shift x.shift y.shift b.shift c.shift r.shift s.shift := by simp [binaryPoint]
@[simp] theorem binaryPoint_subst (D:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2)
    (x y b c r s:ST (V:=V) n) (w:Bootstrapping.SemitermVec V L n m) :
    (binaryPoint D F R x y b c r s).subst w=
    binaryPoint D F R (x.subst w) (y.subst w) (b.subst w) (c.subst w) (r.subst w) (s.subst w) := by simp [binaryPoint]
noncomputable def binaryRelation (D:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ (unary D (Semiterm.bvar 0) 🡒 ∀¹ ∀¹ ∀¹ ∀¹ ∀¹
    binaryPoint D F R (Semiterm.bvar 5) (Semiterm.bvar 4) (Semiterm.bvar 3)
      (Semiterm.bvar 2) (Semiterm.bvar 1) (Semiterm.bvar 0))
@[simp] theorem binaryRelation_shift (D:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2) :
    (binaryRelation D F R).shift=binaryRelation D.shift F.shift R.shift := by simp [binaryRelation]
noncomputable def binaryOutput (D P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (z:ST (V:=V) n) : SF (V:=V) n :=
  unary D z ⋏ (∃¹ ∃¹ (unary P (Semiterm.bvar 1) ⋏
    (unary Q (Semiterm.bvar 0) ⋏ ternary F (Semiterm.bvar 1) (Semiterm.bvar 0) z.bShift.bShift)))
@[simp] theorem binaryOutput_shift (D P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (z:ST (V:=V) n) :
    (binaryOutput D P Q F z).shift=binaryOutput D.shift P.shift Q.shift F.shift z.shift := by
  simp [binaryOutput,Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem binaryOutput_subst (D P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (z:ST (V:=V) n)
    (w:Bootstrapping.SemitermVec V L n m) : (binaryOutput D P Q F z).subst w=
      binaryOutput D P Q F (z.subst w) := by
  simp [binaryOutput]
  simp [SemitermVec.q]
#print axioms binaryRelation_shift
#print axioms binaryOutput_shift
#print axioms binaryOutput_subst
end M6.PA.NumericPAeqValueCoherence
