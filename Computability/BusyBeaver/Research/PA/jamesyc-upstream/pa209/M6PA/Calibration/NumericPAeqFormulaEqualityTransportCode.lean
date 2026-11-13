module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportTyped
public import M6PA.Calibration.NumericPAeqValueCoherencePairwiseCode
@[expose] public section
namespace M6.PA.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def equalityAtomCode (A B : V) : V :=
  NumericPAeqFormula.equalityCode (substs1 L (qqBvar 1) A) (substs1 L (qqBvar 0) B)
noncomputable def withDomain (P : V) : V := qqAnd (NumericPAeqTerm.domainCode (qqBvar 0)) P
noncomputable def transportInput (P Q U W : V) : V :=
  qqAnd (pairwiseCode (withDomain P) (withDomain U))
    (qqAnd (pairwiseCode (withDomain Q) (withDomain W))
      (qqAnd (qqExs (withDomain P)) (qqAnd (qqExs (withDomain Q))
        (qqAnd (qqExs (withDomain U)) (qqExs (withDomain W))))))
noncomputable def transportCode (P Q U W : V) : V :=
  imp L (transportInput P Q U W)
    (qqAnd (imp L (equalityAtomCode (withDomain P) (withDomain Q)) (equalityAtomCode (withDomain U) (withDomain W)))
      (imp L (equalityAtomCode (withDomain U) (withDomain W)) (equalityAtomCode (withDomain P) (withDomain Q))))
noncomputable def transportStatement (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2) : SF (V:=V) 0 :=
  (pairwise (D ⋏ P) (D ⋏ U) R ⋏ (pairwise (D ⋏ Q) (D ⋏ W) R ⋏
    ((∃¹ (D ⋏ P)) ⋏ ((∃¹ (D ⋏ Q)) ⋏ ((∃¹ (D ⋏ U)) ⋏ (∃¹ (D ⋏ W))))))) 🡒
    ((equalityAtom (D ⋏ P) (D ⋏ Q) R 🡒 equalityAtom (D ⋏ U) (D ⋏ W) R) ⋏
      (equalityAtom (D ⋏ U) (D ⋏ W) R 🡒 equalityAtom (D ⋏ P) (D ⋏ Q) R))

theorem equalityAtom_val (A B : SF (V:=V) 1) :
    (equalityAtom A B isoPredicate).val=equalityAtomCode A.val B.val := by
  simp [equalityAtom,equalityAtomCode,NumericPAeqFormula.equalityCode,NumericPAeqFormula.equalityTail,
    unary,binary,isoPredicate,NumericPAeqValueIsoGuard.isoCode,NumericPAeqValueIsoGuard.isoTemplate,
    NumericPAeqTerm.templateTwo,substs1]
  change NumericPAeqValueIsoGuard.isoCode (qqBvar (1:V)) (qqBvar 0) = _
  simpa using NumericPAeqValueIsoGuard.isoCode_quote (V:=V) (FFL.FirstOrder.Semiterm.bvar (n:=2) 1) (FFL.FirstOrder.Semiterm.bvar 0)

theorem domain_val : (RelationalPredicateBinary.domain (V:=V)).val = NumericPAeqTerm.domainCode (qqBvar 0) := by
  exact (NumericPAeqTerm.domainCode_quote (V:=V) (FFL.FirstOrder.Semiterm.bvar (n:=1) 0)).symm

theorem withDomain_val (P : SF (V:=V) 1) : ((RelationalPredicateBinary.domain (V:=V)) ⋏ P).val=withDomain P.val := by
  rw [Bootstrapping.Semiformula.val_and,domain_val]
  rfl

theorem transportStatement_val (P Q U W : SF (V:=V) 1) :
    (transportStatement domain P Q U W isoPredicate).val=transportCode P.val Q.val U.val W.val := by
  simp only [transportStatement,Bootstrapping.Semiformula.val_imp,domain_val,
    Bootstrapping.Semiformula.val_and,Bootstrapping.Semiformula.val_exs,pairwise_val,equalityAtom_val]
  rfl
#print axioms domain_val
#print axioms equalityAtom_val
#print axioms withDomain_val
#print axioms transportStatement_val
end M6.PA.NumericPAeqFormulaEqualityTransport

