module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceSyntax
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def binaryRemainder (P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (x z:ST (V:=V) n) : SF (V:=V) n :=
  ∃¹ (unary P x.bShift ⋏ (unary Q (Semiterm.bvar 0) ⋏ ternary F x.bShift (Semiterm.bvar 0) z.bShift))
@[simp] theorem binaryRemainder_shift (P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (x z:ST (V:=V) n) :
    (binaryRemainder P Q F x z).shift=binaryRemainder P.shift Q.shift F.shift x.shift z.shift := by
  simp [binaryRemainder,Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem binaryOuter_free (P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (z:ST (V:=V) 0) :
    (∃¹ (unary P (Semiterm.bvar 1) ⋏ (unary Q (Semiterm.bvar 0) ⋏
      ternary F (Semiterm.bvar 1) (Semiterm.bvar 0) z.bShift.bShift))).free=
    binaryRemainder P.shift Q.shift F.shift (Semiterm.fvar 0) z.shift := by
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_exs,
    Bootstrapping.Semiformula.shift_and,Bootstrapping.Semiformula.substs_ex,
    Bootstrapping.Semiformula.substs_and,unary_shift,ternary_shift,unary_subst,ternary_subst,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Bootstrapping.Semiterm.bShift_substs_q,
    Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.shift_bvar,
    Bootstrapping.Semiterm.substs_bvar]
  simp [binaryRemainder,SemitermVec.q]
@[simp] theorem binaryInner_free (P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (x z:ST (V:=V) 0) :
    (unary P x.bShift ⋏ (unary Q (Semiterm.bvar 0) ⋏ ternary F x.bShift (Semiterm.bvar 0) z.bShift)).free=
      unary P.shift x.shift ⋏ (unary Q.shift (Semiterm.fvar 0) ⋏ ternary F.shift x.shift (Semiterm.fvar 0) z.shift) := by
  simp [Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm]
#print axioms binaryOuter_free
#print axioms binaryInner_free
end M6.PA.NumericPAeqValueCoherence
