module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplatesSyntax
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplates
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaLogical
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def uniformPremiseCode (H D P Q:V):V := qqAll (imp L H (imp L D (biCode P Q)))
noncomputable def allTemplateCode (H D P Q:V):V :=
  imp L (uniformPremiseCode H D P Q) (imp L H (biCode (qqAll (imp L D P)) (qqAll (imp L D Q))))
noncomputable def exsTemplateCode (H D P Q:V):V :=
  imp L (uniformPremiseCode H D P Q) (imp L H (biCode (qqExs (qqAnd D P)) (qqExs (qqAnd D Q))))
theorem liftClosed_val (H:SF (V:=V) 0):(liftClosed H).val=H.val := by
  change subst L 0 H.val=H.val
  exact subst_eq_self H.isSemiformula (by simp) (by simp)
theorem uniformPremise_val (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1):
    (uniformPremise H D P Q).val=uniformPremiseCode H.val D.val P.val Q.val := by
  simp [uniformPremise,uniformPremiseCode,biCode,liftClosed_val]
theorem allTemplate_val (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1):
    (uniformPremise H D P Q 🡒 (H 🡒 bi (guardedAll D P) (guardedAll D Q))).val=
      allTemplateCode H.val D.val P.val Q.val := by
  simp [allTemplateCode,uniformPremise_val,bi,biCode,guardedAll]
theorem exsTemplate_val (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1):
    (uniformPremise H D P Q 🡒 (H 🡒 bi (guardedExs D P) (guardedExs D Q))).val=
      exsTemplateCode H.val D.val P.val Q.val := by
  simp [exsTemplateCode,uniformPremise_val,bi,biCode,guardedExs]
#print axioms liftClosed_val
#print axioms uniformPremise_val
#print axioms allTemplate_val
#print axioms exsTemplate_val
end PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplates

