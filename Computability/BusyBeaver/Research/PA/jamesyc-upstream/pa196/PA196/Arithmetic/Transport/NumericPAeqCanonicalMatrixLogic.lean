module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaLogicalCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqCanonicalMatrix
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker NumericPAeqFormulaLogical
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def useBi (P Q:SF (V:=V) 0):ND.Proof (T:=(∅:Theory L).internalize V) ∅ ((P ⋏ bi P Q) 🡒 Q) := by
  apply ND.impIntro
  have h := ND.assumption (T:=(∅:Theory L).internalize V) (P ⋏ bi P Q)
    (by simp : ∼(P ⋏ bi P Q)∈insert (∼(P ⋏ bi P Q)) ∅)
  exact ND.mp (ND.andLeft h) (ND.andLeft (ND.andRight h))
theorem useBi_requested_certificate (p q native lo z:V) (hp:IsFormula L p) (hq:IsFormula L q)
    (hc:FormulaCovered 0 native lo z (imp L (qqAnd p (biCode p q)) q)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (imp L (qqAnd p (biCode p q)) q)+1 := by
  let P:SF (V:=V) 0 :=⟨p,hp⟩
  let Q:SF (V:=V) 0 :=⟨q,hq⟩
  exact empty_requested_certificate ((P ⋏ bi P Q) 🡒 Q) (useBi P Q) native lo z hc
#print axioms useBi
#print axioms useBi_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqCanonicalMatrix

