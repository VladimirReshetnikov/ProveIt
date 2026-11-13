module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityValidity
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityBinaryShape
public import M6PA.Calibration.NumericPAeqValueBinaryShape
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainProjection
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryDuplicateCode
public import PA196.Arithmetic.Transport.RelationalPredicateBinarySupply
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueTotality


/-! Actual independent two-child semantic arithmetic branches. The common
domain duplication and all fixed add/mul totality suppliers are paid. -/
namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem binary_from_supply (R:RelationalSource.Ordinal.Formula 3)
    {s b f u v out:V} (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language s u) (hv:IsSemiterm Presentation.language s v)
    (hub:FreeSupported (len f) u) (hvb:FreeSupported (len f) v)
    (heout:out=qqExs (binaryValue R (qqBvar 0)
      (substs1 language (qqBvar 1) (valueSyntax (parameters b f (qqBvar 0)) u))
      (substs1 language (qqBvar 0) (valueSyntax (parameters b f (qqBvar 0)) v))))
    (hs:∀P Q g lo z : V, IsSemiformula language 1 P → IsSemiformula language 1 Q →
      RelationalSource.Numeric.FormulaCovered 0 g lo z (RelationalPredicateBinary.binaryTotalityCode R P Q) →
      ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
        (RelationalPredicateBinary.binaryTotalityCode R P Q)+1)
    (g lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z
      (imp language (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v)) out)) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v)) out)+1 := by
  let P := valueSyntax (parameters b f (qqBvar (0:V))) u
  let Q := valueSyntax (parameters b f (qqBvar (0:V))) v
  have hp : IsSemiformula language 1 P := by
    have h := valueTotality_isSemiformula hb hf hu hub
    rw [valueTotality_zero_environments hb hf] at h
    simpa [P] using IsSemiformula.exs.mp h
  have hq : IsSemiformula language 1 Q := by
    have h := valueTotality_isSemiformula hb hf hv hvb
    rw [valueTotality_zero_environments hb hf] at h
    simpa [Q] using IsSemiformula.exs.mp h
  have hd : IsSemiformula language 1 (domainCode (qqBvar (0:V))) := domainCode_isSemiformula (by simp)
  rw [valueTotality_zero_environments hb hf,valueTotality_zero_environments hb hf] at hc ⊢
  have hab := IsSemiformula.imp.mp hc.2.1
  let mid := qqAnd (qqExs (qqAnd (domainCode (qqBvar (0:V))) P)) (qqExs (qqAnd (domainCode (qqBvar 0)) Q))
  have hm : IsFormula language mid := by
    apply IsSemiformula.and.mpr
    constructor <;> apply IsSemiformula.exs.mpr <;> apply IsSemiformula.and.mpr
    · simpa using And.intro hd hp
    · simpa using And.intro hd hq
  apply source_implication_compose _ mid out g lo z (by simpa using hab.1) hm (by simpa using hab.2) hc
  · intro g lo z hcov
    obtain ⟨p,hep⟩ := valueSyntax_domain_shape (parameters b f (qqBvar (0:V))) u hu.isUTerm
    obtain ⟨q,heq⟩ := valueSyntax_domain_shape (parameters b f (qqBvar (0:V))) v hv.isUTerm
    simp only [parameters_result] at hep heq
    change P=qqAnd (domainCode (qqBvar 0)) p at hep
    change Q=qqAnd (domainCode (qqBvar 0)) q at heq
    have hpp := (IsSemiformula.and.mp (hep ▸ hp)).2
    have hqq := (IsSemiformula.and.mp (heq ▸ hq)).2
    change RelationalSource.Numeric.FormulaCovered 0 g lo z
      (imp language (qqAnd (qqExs P) (qqExs Q)) mid) at hcov
    change ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (qqAnd (qqExs P) (qqExs Q)) mid)+1
    dsimp [mid] at hcov ⊢
    rw [hep,heq] at hcov ⊢
    exact duplicateBothDomain_supply _ p q g lo z hd hpp hqq hcov
  · intro g lo z hcov
    rw [heout] at hcov ⊢
    exact hs P Q g lo z hp hq hcov

theorem addition_requested_certificate {s b f u v:V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language s u) (hv:IsSemiterm Presentation.language s v)
    (hub:FreeSupported (len f) u) (hvb:FreeSupported (len f) v) (g lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z
      (imp language (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v))
        (valueTotalityCode b f (qqFunc 2 2 (u∷(v∷0)))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v))
        (valueTotalityCode b f (qqFunc 2 2 (u∷(v∷0)))))+1 :=
  binary_from_supply additionTemplate hb hf hu hv hub hvb (valueTotality_addition_shape hb hf hu hv hub hvb)
    RelationalPredicateBinary.addition_supply g lo z hc

theorem multiplication_requested_certificate {s b f u v:V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language s u) (hv:IsSemiterm Presentation.language s v)
    (hub:FreeSupported (len f) u) (hvb:FreeSupported (len f) v) (g lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z
      (imp language (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v))
        (valueTotalityCode b f (qqFunc 2 3 (u∷(v∷0)))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v))
        (valueTotalityCode b f (qqFunc 2 3 (u∷(v∷0)))))+1 :=
  binary_from_supply multiplicationTemplate hb hf hu hv hub hvb (valueTotality_multiplication_shape hb hf hu hv hub hvb)
    RelationalPredicateBinary.multiplication_supply g lo z hc

#print axioms addition_requested_certificate
#print axioms multiplication_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueTotality

