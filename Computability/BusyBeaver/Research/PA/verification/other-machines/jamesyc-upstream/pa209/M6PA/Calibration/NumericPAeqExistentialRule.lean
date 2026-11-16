module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqExistentialElimination
public import M6PA.Calibration.NumericPAeqExistentialTotality
@[expose] public section
namespace M6.PA.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqValueCoherence NumericPAeqValueTotality RelationalPredicateBinary
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem uncurry_requested_certificate (p q r native lo z:V)
    (hp:IsFormula language p) (hq:IsFormula language q) (hr:IsFormula language r)
    (hc:FormulaCovered 0 native lo z (imp language (imp language p (imp language q r)) (imp language (qqAnd p q) r))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp language (imp language p (imp language q r)) (imp language (qqAnd p q) r))+1 :=by
  let P:SF (V:=V) 0 :=⟨p,hp⟩
  let Q:SF (V:=V) 0 :=⟨q,hq⟩
  let R:SF (V:=V) 0 :=⟨r,hr⟩
  have d:ND.Proof (T:=(∅:Theory language).internalize V) ∅ ((P 🡒 (Q 🡒 R)) 🡒 ((P ⋏ Q) 🡒 R)) :=by
    apply ND.impIntro
    apply ND.impIntro
    have h:ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼(P ⋏ Q)) (insert (∼(P 🡒 (Q 🡒 R))) ∅)) (P ⋏ Q) :=ND.assumption _ (by simp)
    have a:ND.Proof (T:=(∅:Theory language).internalize V) (insert (∼(P ⋏ Q)) (insert (∼(P 🡒 (Q 🡒 R))) ∅)) (P 🡒 (Q 🡒 R)) :=ND.assumption _ (by simp)
    exact ND.mp (ND.andRight h) (ND.mp (ND.andLeft h) a)
  exact empty_requested_certificate _ d native lo z hc
noncomputable def existentialRuleCode (f p u:V):V :=
  imp language (qqAnd (freeDomain f) (instanceFormula f p u)) (existentialFormula f p)
theorem existential_rule_requested_certificate {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (existentialRuleCode f p u)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (existentialRuleCode f p u)+1 :=by
  let H:=freeDomain f
  let B:=instanceFormula f p u
  let E:=qqExs (valuePredicate 0 f u)
  let C:=existentialFormula f p
  have hH:=freeDomain_valid hf
  have hB:=instanceFormula_valid hf hp hu hs hus
  have hC:=existentialFormula_valid hf hp hs
  have hE:IsFormula language E :=by
    apply IsSemiformula.exs.mpr
    simpa [valuePredicate] using NumericPAeqTerm.valueSyntax_supported_isSemiformula (valuePredicate_covered hf hu hus)
  have hBC:IsFormula language (imp language B C):=IsSemiformula.imp.mpr ⟨hB,hC⟩
  have hcur:IsFormula language (imp language H (imp language B C)):=IsSemiformula.imp.mpr ⟨hH,hBC⟩
  apply source_certificate_mp (imp language H (imp language B C)) (existentialRuleCode f p u) native lo z hcur
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hH,hB⟩,hC⟩) hc
  · intro g l z hc
    apply source_implication_compose H (qqAnd H E) (imp language B C) g l z hH (IsSemiformula.and.mpr ⟨hH,hE⟩) hBC hc
    · intro g l z hc
      apply source_implication_pair H H E g l z hH hH hE hc
      · intro g l z _
        exact source_identity_certificate (parameters 0 g l z) H hH.isUFormula
      · exact existence_requested_certificate hf hu hus
    · exact elimination_requested_certificate hf hp hu hs hus
  · intro g l z hc
    exact uncurry_requested_certificate H B C g l z hH hB hC hc
#print axioms uncurry_requested_certificate
#print axioms existential_rule_requested_certificate
end M6.PA.NumericPAeqExistentialInterpretation

