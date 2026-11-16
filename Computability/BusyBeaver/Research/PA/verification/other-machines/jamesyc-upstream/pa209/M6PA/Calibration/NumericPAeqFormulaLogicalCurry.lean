module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaLogicalCertificate
@[expose] public section
namespace M6.PA.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def curry (p q r:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅ (((p ⋏ q) 🡒 r) 🡒 (p 🡒 (q 🡒 r))) := by
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  exact ND.mp (ND.andIntro (ND.assumption p (by simp)) (ND.assumption q (by simp)))
    (ND.assumption ((p ⋏ q) 🡒 r) (by simp))
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem curry_requested_certificate (p q r native lo z:V)
    (hp:IsFormula L p) (hq:IsFormula L q) (hr:IsFormula L r)
    (hc:FormulaCovered 0 native lo z (imp L (imp L (qqAnd p q) r) (imp L p (imp L q r)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp L (imp L (qqAnd p q) r) (imp L p (imp L q r)))+1 :=
  empty_requested_certificate _ (curry ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩) native lo z hc
#print axioms curry_requested_certificate
end M6.PA.NumericPAeqFormulaLogical

