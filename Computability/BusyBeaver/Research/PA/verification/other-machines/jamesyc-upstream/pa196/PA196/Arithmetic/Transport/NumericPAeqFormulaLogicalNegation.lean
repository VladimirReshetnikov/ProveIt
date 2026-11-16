module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaLogicalCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def contradiction {T:InternalTheory V L} {Γ:ND.Seq (V:=V)} {p q:SF (V:=V) 0}
    (d:ND.Proof (T:=T) Γ p) (e:ND.Proof (T:=T) Γ (∼p)):ND.Proof (T:=T) Γ q := by
  apply TDerivation.cut (φ:=p)
  · exact d.wk (by intro x hx; simp at hx ⊢; tauto)
  · exact e.wk (by intro x hx; simp at hx ⊢; tauto)
noncomputable def negDirection {T:InternalTheory V L} {Γ:ND.Seq (V:=V)} {p q:SF (V:=V) 0}
    (d:ND.Proof (T:=T) Γ (p 🡒 q)):ND.Proof (T:=T) Γ ((∼q) 🡒 (∼p)) := by
  apply ND.impIntro
  have arrow : ND.Proof (T:=T) (insert (∼(∼q)) Γ) ((∼p) ⋎ q) := by
    simpa only [Bootstrapping.Semiformula.imp_def] using ND.up d (∼q)
  apply orCases arrow
  · exact ND.assumption (∼p) (by simp)
  · exact contradiction (ND.assumption q (by simp)) (ND.assumption (∼q) (by simp))
noncomputable def negBi (p q:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅ ((bi p q) 🡒 bi (∼p) (∼q)) := by
  apply ND.impIntro
  have h := ND.assumption (T:=(∅:Theory L).internalize V) (bi p q)
    (by simp : ∼(bi p q)∈insert (∼(bi p q)) ∅)
  exact ND.andIntro (negDirection (ND.andRight h)) (negDirection (ND.andLeft h))
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem negBi_requested_certificate (p q native lo z:V) (hp:IsFormula L p) (hq:IsFormula L q)
    (hc:FormulaCovered 0 native lo z (imp L (biCode p q) (biCode (neg L p) (neg L q)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp L (biCode p q) (biCode (neg L p) (neg L q)))+1 := by
  let P:SF (V:=V) 0 := ⟨p,hp⟩
  let Q:SF (V:=V) 0 := ⟨q,hq⟩
  exact empty_requested_certificate _ (negBi P Q) native lo z hc
#print axioms negBi
#print axioms negBi_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqFormulaLogical

