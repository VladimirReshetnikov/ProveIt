module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqVariableCoherenceCalibration
public import M6PA.Calibration.RelationalClosedCertificateOrdinalSeeds
@[expose] public section
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

noncomputable def selfVariableReflexivityTyped : SF (V:=V) 0 :=
  ∀¹ binary equalityPredicate (Semiterm.bvar 0) (Semiterm.bvar 0)
theorem selfVariableReflexivityTyped_quote : selfVariableReflexivityTyped (V:=V) =
    ⌜RelationalSource.reflexivityFormula⌝ := by
  simp [selfVariableReflexivityTyped,RelationalSource.reflexivityFormula,RelationalSource.eqAtom,
    ←FFL.FirstOrder.Semiterm.typed_quote_bvar,RelationalSource.ND.eq]
  rfl

variable {T : InternalTheory V L}
noncomputable def selfVariableProof (x : ST (V:=V) 0) :
    ND.Proof (T:=T) (insert (∼selfVariableReflexivityTyped) ∅)
      (unary domain x 🡒 (unary domain x ⋏ binary equalityPredicate x x)) := by
  apply ND.impIntro
  have hd : ND.Proof (T:=T) (insert (∼unary domain x) (insert (∼selfVariableReflexivityTyped) ∅))
      (unary domain x) := ND.assumption _ (by simp)
  have hr : ND.Proof (T:=T) (insert (∼unary domain x) (insert (∼selfVariableReflexivityTyped) ∅))
      (selfVariableReflexivityTyped (V:=V)) := ND.assumption _ (by simp)
  have he : ND.Proof (T:=T) (insert (∼unary domain x) (insert (∼selfVariableReflexivityTyped) ∅))
      (binary equalityPredicate x x) := by
    simpa [selfVariableReflexivityTyped] using ND.allElim hr x
  exact ND.andIntro hd he

theorem selfVariable_instance_val (x : ST (V:=V) 0) :
    (unary domain x 🡒 (unary domain x ⋏ binary equalityPredicate x x)).val =
      imp L (NumericPAeqTerm.domainCode x.val) (NumericPAeqTerm.variableValue x.val x.val) := by
  rfl
#print axioms selfVariableReflexivityTyped_quote
#print axioms selfVariableProof
#print axioms selfVariable_instance_val
end M6.PA.NumericPAeqValueTotality

