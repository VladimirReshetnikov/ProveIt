module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableTyped
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def substitutionVariableTyped (D P : SF (V:=V) 1) (E R : SF (V:=V) 2)
    (a : ST (V:=V) 0) : SF (V:=V) 0 :=
  (unary P a ⋏ pairwise P P R) 🡒 pairwise P (variablePredicate D E a) R
variable {T : InternalTheory V L}
noncomputable def substitutionVariableProof (D P : SF (V:=V) 1) (E R : SF (V:=V) 2)
    (a : ST (V:=V) 0) :
    ND.Proof (T:=T) (insert (∼rightTransportTyped E R) ∅) (substitutionVariableTyped D P E R a) := by
  apply ND.impIntro
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [pairwise,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,unary_shift,binary_shift,unary_subst,binary_subst]
  apply ND.impIntro
  let r : ST (V:=V) 0 := Semiterm.fvar 1
  let s : ST (V:=V) 0 := Semiterm.fvar 0
  let A := unary P.shift.shift r ⋏ unary (variablePredicate D.shift.shift E.shift.shift a.shift.shift) s
  let B := unary P a ⋏ pairwise P P R
  let C : ND.Seq (V:=V) := insert (∼A)
    ((insert (∼B) (insert (∼rightTransportTyped E R) ∅) : ND.Seq (V:=V)).shift.shift)
  have hp : ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have ht : ND.Proof (T:=T) C (rightTransportTyped E.shift.shift R.shift.shift) := by
    apply ND.assumption; simp [C]
  have hb : ND.Proof (T:=T) C (unary P.shift.shift a.shift.shift ⋏ pairwise P.shift.shift P.shift.shift R.shift.shift) := by
    apply ND.assumption; simp [C,B]
  have hi := pairwiseAt P.shift.shift P.shift.shift R.shift.shift r a.shift.shift
    (ND.andRight hb) (ND.andLeft hp) (ND.andLeft hb)
  have he : ND.Proof (T:=T) C (binary E.shift.shift s a.shift.shift) := by
    have hh := ND.andRight hp
    rw [unary_variablePredicate] at hh
    exact ND.andRight hh
  have out := rightTransportAt E.shift.shift R.shift.shift r a.shift.shift s ht hi he
  simpa [C,A,B,r,s,SemitermVec.q,pairwise] using out
#print axioms substitutionVariableProof
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
