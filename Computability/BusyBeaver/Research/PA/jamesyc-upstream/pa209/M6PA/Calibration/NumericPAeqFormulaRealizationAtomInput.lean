module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorRealization
public import M6PA.Calibration.NumericPAeqSupportedVectorRealizationTotality
public import M6PA.Calibration.NumericPAeqValueCertificatePair
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization NumericPAeqValueCoherence
open NumericPAeqSupportedVectorRealization NumericPAeqSupportedValueCoherence
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def SourceArrowSupply (A B:V):Prop := ∀g lo z:V,FormulaCovered 0 g lo z (imp language A B)→
  ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 g lo z) (imp language A B)+1
theorem sourceArrowSupply_and {A B C:V} (ha:IsFormula language A) (hb:IsFormula language B)
    (hc:IsFormula language C) (ab:SourceArrowSupply A B) (ac:SourceArrowSupply A C):
    SourceArrowSupply A (qqAnd B C) := by
  intro g lo z h
  exact source_implication_pair A B C g lo z ha hb hc h ab ac
noncomputable def atomInput (b f a w t u:V):V :=
  qqAnd (vectorComparison b f a w t) (qqAnd (vectorComparison b f a w u)
    (qqAnd (qqExs (valuePredicate b f (termSubst Presentation.language w t)))
      (qqAnd (qqExs (valuePredicate b f (termSubst Presentation.language w u)))
        (qqAnd (qqExs (valuePredicate a f t)) (qqExs (valuePredicate a f u))))))
theorem atomInput_valid {s r b f a w t u:V}
    (ht:SupportedVectorEnvironment s r b f a w t) (hu:SupportedVectorEnvironment s r b f a w u):
    IsFormula language (atomInput b f a w t u) := by
  have htL := valuePredicate_valid (substituted_environment ht)
  have huL := valuePredicate_valid (substituted_environment hu)
  have htR := valuePredicate_valid (original_environment ht)
  have huR := valuePredicate_valid (original_environment hu)
  exact IsSemiformula.and.mpr ⟨vectorComparison_valid ht,IsSemiformula.and.mpr ⟨vectorComparison_valid hu,
    IsSemiformula.and.mpr ⟨IsSemiformula.exs.mpr (by simpa using htL),
    IsSemiformula.and.mpr ⟨IsSemiformula.exs.mpr (by simpa using huL),
    IsSemiformula.and.mpr ⟨IsSemiformula.exs.mpr (by simpa using htR),IsSemiformula.exs.mpr (by simpa using huR)⟩⟩⟩⟩⟩
theorem atomInput_supply {s r b f a w t u:V}
    (ht:SupportedVectorEnvironment s r b f a w t) (hu:SupportedVectorEnvironment s r b f a w u):
    SourceArrowSupply (vectorInput s r b f a w) (atomInput b f a w t u) := by
  have hH := vectorInput_valid ht
  have h1 := vectorComparison_valid ht
  have h2 := vectorComparison_valid hu
  have h3 : IsFormula language (qqExs (valuePredicate b f (termSubst Presentation.language w t))) :=
    IsSemiformula.exs.mpr (by simpa using valuePredicate_valid (substituted_environment ht))
  have h4 : IsFormula language (qqExs (valuePredicate b f (termSubst Presentation.language w u))) :=
    IsSemiformula.exs.mpr (by simpa using valuePredicate_valid (substituted_environment hu))
  have h5 : IsFormula language (qqExs (valuePredicate a f t)) :=
    IsSemiformula.exs.mpr (by simpa using valuePredicate_valid (original_environment ht))
  have h6 : IsFormula language (qqExs (valuePredicate a f u)) :=
    IsSemiformula.exs.mpr (by simpa using valuePredicate_valid (original_environment hu))
  have s1 : SourceArrowSupply (vectorInput s r b f a w) (vectorComparison b f a w t) :=
    open_source_vector_realization_certificate ht
  have s2 : SourceArrowSupply (vectorInput s r b f a w) (vectorComparison b f a w u) :=
    open_source_vector_realization_certificate hu
  have s3 : SourceArrowSupply (vectorInput s r b f a w) (qqExs (valuePredicate b f (termSubst Presentation.language w t))) := by
    simpa only [SourceArrowSupply,valuePredicate,valueTotality_zero_environments ht.1 ht.2.1] using vector_substituted_totality ht
  have s4 : SourceArrowSupply (vectorInput s r b f a w) (qqExs (valuePredicate b f (termSubst Presentation.language w u))) := by
    simpa only [SourceArrowSupply,valuePredicate,valueTotality_zero_environments hu.1 hu.2.1] using vector_substituted_totality hu
  have s5 : SourceArrowSupply (vectorInput s r b f a w) (qqExs (valuePredicate a f t)) := by
    simpa only [SourceArrowSupply,valuePredicate,valueTotality_zero_environments ht.2.2.1 ht.2.1] using vector_original_totality ht
  have s6 : SourceArrowSupply (vectorInput s r b f a w) (qqExs (valuePredicate a f u)) := by
    simpa only [SourceArrowSupply,valuePredicate,valueTotality_zero_environments hu.2.2.1 hu.2.1] using vector_original_totality hu
  exact sourceArrowSupply_and hH h1 (IsSemiformula.and.mpr ⟨h2,IsSemiformula.and.mpr ⟨h3,IsSemiformula.and.mpr ⟨h4,IsSemiformula.and.mpr ⟨h5,h6⟩⟩⟩⟩) s1
    (sourceArrowSupply_and hH h2 (IsSemiformula.and.mpr ⟨h3,IsSemiformula.and.mpr ⟨h4,IsSemiformula.and.mpr ⟨h5,h6⟩⟩⟩) s2
      (sourceArrowSupply_and hH h3 (IsSemiformula.and.mpr ⟨h4,IsSemiformula.and.mpr ⟨h5,h6⟩⟩) s3
        (sourceArrowSupply_and hH h4 (IsSemiformula.and.mpr ⟨h5,h6⟩) s4
          (sourceArrowSupply_and hH h5 h6 s5 s6))))
#print axioms sourceArrowSupply_and
#print axioms atomInput_valid
#print axioms atomInput_supply
end M6.PA.NumericPAeqFormulaRealization

