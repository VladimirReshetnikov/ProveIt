module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueSelfVariableProof
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSuccessorCalibration
public import M6PA.Calibration.NumericPAeqValueClosedEnvironment
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorValue
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence NumericPAeqValueTotality NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def input (x y : ST (V:=V) 0) : SF (V:=V) 0 :=
  unary domain x ⋏ (unary domain y ⋏ binary successorPredicate x y)
noncomputable def output (x y : ST (V:=V) 0) : SF (V:=V) 0 :=
  unary domain y ⋏ (∃¹ ((unary domain (Semiterm.bvar 0) ⋏ binary equalityPredicate (Semiterm.bvar 0) x.bShift) ⋏
    binary successorPredicate (Semiterm.bvar 0) y.bShift))
variable {T : InternalTheory V L}
noncomputable def successorValueProof (x y : ST (V:=V) 0) :
    ND.Proof (T:=T) (insert (∼selfVariableReflexivityTyped) ∅) (input x y 🡒 output x y) := by
  apply ND.impIntro
  let C : ND.Seq (V:=V) := insert (∼input x y) (insert (∼selfVariableReflexivityTyped) ∅)
  have hi : ND.Proof (T:=T) C (input x y) := ND.assumption _ (by simp [C])
  have hr : ND.Proof (T:=T) C (selfVariableReflexivityTyped (V:=V)) := ND.assumption _ (by simp [C])
  have he : ND.Proof (T:=T) C (binary equalityPredicate x x) := by
    simpa [selfVariableReflexivityTyped] using ND.allElim hr x
  apply ND.andIntro (ND.andLeft (ND.andRight hi))
  apply ND.exsIntro _ x
  simpa using ND.andIntro (ND.andIntro (ND.andLeft hi) he) (ND.andRight (ND.andRight hi))

theorem input_val (x y : ST (V:=V) 0) :
    (input x y).val=qqAnd (domainCode x.val) (qqAnd (domainCode y.val) (successorCode x.val y.val)) := rfl

theorem output_val (x y : ST (V:=V) 0) :
    (output x y).val=successorValue y.val (variableValue (qqBvar 0) x.val) := by
  simp [output,successorValue,variableValue,unary,binary,RelationalPredicateBinary.domain,
    successorPredicate,equalityPredicate,domainCode,successorCode,equalityCode,templateOne,templateTwo,substs1,
    targetTerm_bShift_zero x.isSemiterm]
  refine ⟨rfl,⟨?_,rfl⟩,rfl⟩
  exact (domainCode_quote (V:=V) (FFL.FirstOrder.Semiterm.bvar (n:=1) 0)).symm

theorem successor_syntax_shape {x y f : V} (hx:IsSemiterm L 0 x)
    (hf:IsSemitermVec L (len f) 0 f) :
    valueSyntax (parameters (x∷0) f y) (qqFunc 1 1 (qqBvar 0∷0))=
      successorValue y (variableValue (qqBvar 0) x) := by
  rw [valueSyntax_successor _ _ (by simp),parameters_result,
    childParameters_zero_environments (IsSemitermVec.singleton.mpr hx) hf]
  simp
#print axioms successorValueProof
#print axioms input_val
#print axioms output_val
#print axioms successor_syntax_shape
end PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorValue
