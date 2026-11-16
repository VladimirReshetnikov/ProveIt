import PA194PAeqUniversalFormulaCongruence
import PA194PAeqAddOneAt
import PA194PAeqArithmeticInduction
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionAddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic PA194PAeq.UniversalTermCongruence
open PA194PAeqTermBlueprint PA194PAeq.UniversalTermCongruence Entailment Entailment.FiniteContext Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

noncomputable def zTerm {n : Nat} : Semiterm V language n :=
  ⟨^func 0 0 0,by simp [source_functions]⟩
noncomputable def sTerm {n : Nat} (t : Semiterm V language n) : Semiterm V language n :=
  ⟨SuccCongruence.succTerm t.val,by simp [SuccCongruence.succTerm,source_functions,t.isSemiterm]⟩
noncomputable def aTerm {n : Nat} (t u : Semiterm V language n) : Semiterm V language n :=
  ⟨AddCongruenceInternal.addTerm t.val u.val,by simp [AddCongruenceInternal.addTerm,source_functions,t.isSemiterm,u.isSemiterm]⟩

theorem addOne_at (t : Term V language) : (ordinaryPAeq.internalize V) ⊢ (aTerm t (sTerm zTerm) ≐ₚ sTerm t) := by
  have d := AddOne.addOneAt t
  have h : (ordinaryPAeq.internalize V) ⊢ (⌜AddOne.prop⌝ : Semiformula V language 1).subst ![t] := ⟨d⟩
  have heq : (⌜AddOne.prop⌝ : Semiformula V language 1).subst ![t] = (aTerm t (sTerm zTerm) ≐ₚ sTerm t) := by
    ext
    simp [AddOne.prop,PA194PAeq.eq,PA194PAeq.add,PA194PAeq.succ,PA194PAeq.zero,
      typedEq,aTerm,sTerm,zTerm,AddCongruenceInternal.addTerm,SuccCongruence.succTerm,
      equalityCode,source_functions,source_relations,Matrix.vecHead,Matrix.vecTail,
      Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,t.isSemiterm.isUTerm]
    refine ⟨rfl,⟨?_,?_,rfl⟩,?_⟩
    · change (↑(Encodable.encode (Func.add : language.Func 2)) : V) = 2
      simp [PA194PAeq.functionEncodable,Encodable.encode]
    · change (↑(Encodable.encode (Func.succ : language.Func 1)) : V) = 1
      simp [PA194PAeq.functionEncodable,Encodable.encode]
    · change (↑(Encodable.encode (Func.succ : language.Func 1)) : V) = 1
      simp [PA194PAeq.functionEncodable,Encodable.encode]
  simpa [heq] using h
@[simp] theorem sTerm_shift {n : Nat} (t : Semiterm V language n) : (sTerm t).shift = sTerm t.shift := by
  ext; simp [sTerm,SuccCongruence.succTerm,termShift_func,source_functions,t.isSemiterm.isUTerm]
@[simp] theorem aTerm_shift {n : Nat} (t u : Semiterm V language n) : (aTerm t u).shift = aTerm t.shift u.shift := by
  ext; simp [aTerm,AddCongruenceInternal.addTerm,termShift_func,source_functions,t.isSemiterm.isUTerm,u.isSemiterm.isUTerm]
@[simp] theorem zTerm_shift {n : Nat} : (zTerm (V:=V) (n:=n)).shift = zTerm := by
  ext; simp [zTerm,termShift_func,source_functions]
@[simp] theorem sTerm_subst {n m : Nat} (t : Semiterm V language n) (v : SemitermVec V language n m) :
    (sTerm t).subst v = sTerm (t.subst v) := by
  ext; simp [sTerm,SuccCongruence.succTerm,termSubst_func,source_functions,t.isSemiterm.isUTerm]
@[simp] theorem aTerm_subst {n m : Nat} (t u : Semiterm V language n) (v : SemitermVec V language n m) :
    (aTerm t u).subst v = aTerm (t.subst v) (u.subst v) := by
  ext; simp [aTerm,AddCongruenceInternal.addTerm,termSubst_func,source_functions,t.isSemiterm.isUTerm,u.isSemiterm.isUTerm]
@[simp] theorem zTerm_subst {n m : Nat} (v : SemitermVec V language n m) :
    (zTerm (V:=V) (n:=n)).subst v = zTerm := by
  ext; simp [zTerm,termSubst_func,source_functions]

theorem step (p : Semiformula V language 1) :
    (ordinaryPAeq.internalize V) ⊢
      (∀⁰ (p 🡒 p.subst ![aTerm (Semiterm.bvar 0) (sTerm zTerm)])) 🡒
      (∀⁰ (p 🡒 p.subst ![sTerm (Semiterm.bvar 0)])) := by
  let T := ordinaryPAeq.internalize V
  let x : Term V language := Semiterm.fvar 0
  let plus : Term V language := aTerm x (sTerm zTerm)
  let next : Term V language := sTerm x
  have heq : T ⊢ plus ≐ₚ next := addOne_at x
  have hc : T ⊢ (plus ≐ₚ next) 🡒 p.shift.subst ![plus] 🡒 p.shift.subst ![next] :=
    UniversalFormulaCongruence.replace p.shift plus next
  have hdir : T ⊢ p.shift.subst ![plus] 🡒 p.shift.subst ![next] := hc ⨀ heq
  have hOpen : ([] : List (Formula V language)) ⊢[T]
      (p 🡒 p.subst ![aTerm (Semiterm.bvar 0) (sTerm zTerm)]).free 🡒
      (p 🡒 p.subst ![sTerm (Semiterm.bvar 0)]).free := by
    have h : T ⊢ (p.shift.subst ![x] 🡒 p.shift.subst ![plus]) 🡒
        (p.shift.subst ![x] 🡒 p.shift.subst ![next]) := by cl_prover [hdir]
    have hopen := (of'! h : ([] : List (Formula V language)) ⊢[T] _)
    simpa [Bootstrapping.Semiformula.free, SemitermVec.q,
      Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,x,plus,next] using hopen
  have hAll : ([] : List (Formula V language)) ⊢[T]
      (∀⁰ (p 🡒 p.subst ![aTerm (Semiterm.bvar 0) (sTerm zTerm)])) 🡒
      (∀⁰ (p 🡒 p.subst ![sTerm (Semiterm.bvar 0)])) := by
    apply TProof.all_imp_all!
    simpa using hOpen
  exact ⟨Entailment.FiniteContext.emptyPrf hAll.some⟩
noncomputable def oldBody (p : Semiformula V language 1) : Formula V language :=
  p.subst ![zTerm] 🡒 (∀⁰ (p 🡒 p.subst ![sTerm (Semiterm.bvar 0)])) 🡒 ∀⁰ p
noncomputable def addOneBody (p : Semiformula V language 1) : Formula V language :=
  p.subst ![zTerm] 🡒 (∀⁰ (p 🡒 p.subst ![aTerm (Semiterm.bvar 0) (sTerm zTerm)])) 🡒 ∀⁰ p

theorem body_implication (p : Semiformula V language 1) :
    (ordinaryPAeq.internalize V) ⊢ oldBody p 🡒 addOneBody p := by
  have h := step p
  unfold oldBody addOneBody
  cl_prover [h]

theorem oldBody_val (p : Semiformula V language 1) :
    (oldBody p).val = PA194PAeqBind.inductionBody p.val := by
  simp [oldBody,PA194PAeqBind.inductionBody,PA194PAeqBind.zeroCode,PA194PAeqBind.succVarCode,
    Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_all,Bootstrapping.Semiformula.val_substs,
    SemitermVec.val_succ,substs1,zTerm,sTerm,SuccCongruence.succTerm]

theorem addOneBody_val (p : Semiformula V language 1) :
    (addOneBody p).val = PA194PAeqBind.inductionBodyAddOne p.val := by
  simp [addOneBody,PA194PAeqBind.inductionBodyAddOne,PA194PAeqBind.arithmeticSuccVariable_code,
    PA194PAeqBind.zeroCode,Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,substs1,zTerm,sTerm,aTerm,
    SuccCongruence.succTerm,AddCongruenceInternal.addTerm]

theorem addOneBody_provable {p : V} (hp : IsSemiformula language 1 p)
    (h : Provable ordinaryPAeq (PA194PAeqBind.inductionBody p)) :
    Provable ordinaryPAeq (PA194PAeqBind.inductionBodyAddOne p) := by
  let P : Semiformula V language 1 := ⟨p,by simpa using hp⟩
  have hOld : (ordinaryPAeq.internalize V) ⊢ oldBody P := (TProvable.iff_provable).mpr (by simpa [P,oldBody_val,instΔ₁Theory,Theory.internalize] using h)
  have hNew : (ordinaryPAeq.internalize V) ⊢ addOneBody P := body_implication P ⨀ hOld
  have hraw := (TProvable.iff_provable).mp hNew
  simpa [P,addOneBody_val,instΔ₁Theory,Theory.internalize] using hraw

#print axioms addOneBody_provable
#print axioms body_implication
#print axioms oldBody_val
#print axioms addOneBody_val
#print axioms step
#print axioms addOne_at
end PA194PAeq.InductionAddOne
