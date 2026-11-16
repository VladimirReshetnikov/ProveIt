module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionStepTemplateSyntax
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportCode
@[expose] public section
namespace M6.PA.NumericPAeqInductionStepTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence NumericPAeqTerm NumericPAeqFormulaLogical
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def uniformMatrixCode (F P R:V):V := imp L F
  (imp L (qqAnd (domainCode (qqBvar 1)) (qqAnd (domainCode (qqBvar 0)) (successorCode (qqBvar 1) (qqBvar 0))))
    (biCode (substs1 L (qqBvar 1) R) (substs1 L (qqBvar 0) P)))
noncomputable def uniformCode (F P R:V):V := qqAll (qqAll (uniformMatrixCode F P R))
noncomputable def sourceStepCode (P R:V):V := qqAll (imp L (domainCode (qqBvar 0)) (imp L P R))
noncomputable def targetStepMatrixCode (P:V):V :=
  imp L (qqAnd (domainCode (qqBvar 1)) (qqAnd (domainCode (qqBvar 0))
    (qqAnd (successorCode (qqBvar 1) (qqBvar 0)) (substs1 L (qqBvar 1) P)))) (substs1 L (qqBvar 0) P)
noncomputable def targetStepCode (P:V):V := qqAll (qqAll (targetStepMatrixCode P))
noncomputable def stepCode (F P R:V):V := imp L (uniformCode F P R)
  (imp L (qqAnd F (sourceStepCode P R)) (targetStepCode P))
noncomputable def uniformMatrix (F:SF (V:=V) 0) (P R:SF (V:=V) 1):SF (V:=V) 2 :=
  closedAt F 2 🡒 ((unary domain (Semiterm.bvar 1) ⋏
    (unary domain (Semiterm.bvar 0) ⋏ binary successorPredicate (Semiterm.bvar 1) (Semiterm.bvar 0))) 🡒
      ((unary R (Semiterm.bvar 1) 🡒 unary P (Semiterm.bvar 0)) ⋏
        (unary P (Semiterm.bvar 0) 🡒 unary R (Semiterm.bvar 1))))
noncomputable def targetMatrix (P:SF (V:=V) 1):SF (V:=V) 2 :=
  (unary domain (Semiterm.bvar 1) ⋏ (unary domain (Semiterm.bvar 0) ⋏
    (binary successorPredicate (Semiterm.bvar 1) (Semiterm.bvar 0) ⋏ unary P (Semiterm.bvar 1)))) 🡒 unary P (Semiterm.bvar 0)
theorem closedAt_val (F:SF (V:=V) 0) (n:Nat):(closedAt F n).val=F.val := by
  change subst L 0 F.val=F.val
  exact subst_eq_self F.isSemiformula (by simp) (by simp)
theorem unary_val (P:SF (V:=V) 1) (x:ST (V:=V) n):
    (unary P x).val=substs1 L x.val P.val := rfl
theorem domainAt_val (x:ST (V:=V) n):(unary domain x).val=domainCode x.val := rfl
theorem successorAt_val (x y:ST (V:=V) n):(binary successorPredicate x y).val=successorCode x.val y.val := rfl

theorem uniformMatrix_val (F:SF (V:=V) 0) (P R:SF (V:=V) 1):
    (uniformMatrix F P R).val=uniformMatrixCode F.val P.val R.val := by
  simp only [uniformMatrix,Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_and,
    closedAt_val,domainAt_val,successorAt_val]
  simp only [unary_val]
  simp [uniformMatrixCode,biCode]
theorem targetMatrix_val (P:SF (V:=V) 1):(targetMatrix P).val=targetStepMatrixCode P.val := by
  simp only [targetMatrix,Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_and,
    domainAt_val,successorAt_val]
  simp only [unary_val]
  simp [targetStepMatrixCode]
theorem uniform_val (F:SF (V:=V) 0) (P R:SF (V:=V) 1):
    (uniform F domain P R successorPredicate).val=uniformCode F.val P.val R.val := by
  change qqAll (qqAll (uniformMatrix F P R).val)=_
  rw [uniformMatrix_val]; rfl
theorem sourceStep_val (P R:SF (V:=V) 1):(sourceStep domain P R).val=sourceStepCode P.val R.val := by
  simp only [sourceStep,Bootstrapping.Semiformula.val_all,Bootstrapping.Semiformula.val_imp,
    NumericPAeqFormulaEqualityTransport.domain_val]
  rfl
theorem targetStep_val (P:SF (V:=V) 1):(targetStep domain P successorPredicate).val=targetStepCode P.val := by
  change qqAll (qqAll (targetMatrix P).val)=_
  rw [targetMatrix_val]; rfl
theorem step_val (F:SF (V:=V) 0) (P R:SF (V:=V) 1):
    (uniform F domain P R successorPredicate 🡒 ((F ⋏ sourceStep domain P R) 🡒 targetStep domain P successorPredicate)).val=
      stepCode F.val P.val R.val := by
  simp only [Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_and,uniform_val,sourceStep_val,targetStep_val]
  rfl
#print axioms closedAt_val
#print axioms unary_val
#print axioms domainAt_val
#print axioms successorAt_val
#print axioms uniformMatrix_val
#print axioms targetMatrix_val
#print axioms uniform_val
#print axioms sourceStep_val
#print axioms targetStep_val
#print axioms step_val
end M6.PA.NumericPAeqInductionStepTemplate

