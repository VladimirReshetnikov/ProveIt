module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaLogicalCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplates
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def liftClosed (H:SF (V:=V) 0):SF (V:=V) 1 := H.subst ![]
noncomputable def uniformPremise (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1):SF (V:=V) 0 :=
  ∀¹ (liftClosed H 🡒 (D 🡒 ((P 🡒 Q) ⋏ (Q 🡒 P))))
noncomputable def guardedAll (D P:SF (V:=V) 1):SF (V:=V) 0 := ∀¹ (D 🡒 P)
noncomputable def guardedExs (D P:SF (V:=V) 1):SF (V:=V) 0 := ∃¹ (D ⋏ P)
@[simp] theorem liftClosed_shift (H:SF (V:=V) 0):(liftClosed H).shift=liftClosed H.shift := by
  simp [liftClosed,Bootstrapping.Semiformula.shift_substs]
@[simp] theorem liftClosed_subst (H:SF (V:=V) 0) (t:ST (V:=V) 0):
    (liftClosed H).subst ![t]=H := by
  simp [liftClosed,Bootstrapping.Semiformula.substs_substs]
@[simp] theorem liftClosed_free (H:SF (V:=V) 0):(liftClosed H).free=H.shift := by
  simp [Bootstrapping.Semiformula.free]
@[simp] theorem uniformPremise_shift (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1):
    (uniformPremise H D P Q).shift=uniformPremise H.shift D.shift P.shift Q.shift := by
  simp [uniformPremise]
@[simp] theorem guardedAll_shift (D P:SF (V:=V) 1):(guardedAll D P).shift=guardedAll D.shift P.shift := by
  simp [guardedAll]
@[simp] theorem guardedExs_shift (D P:SF (V:=V) 1):(guardedExs D P).shift=guardedExs D.shift P.shift := by
  simp [guardedExs]
#print axioms liftClosed_free
#print axioms uniformPremise_shift
end PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplates

