module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplatesCode
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSuccessorCalibration
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionStepTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def closedAt (F:SF (V:=V) 0) (n:Nat) : SF (V:=V) n := F.subst ![]
@[simp] theorem closedAt_shift (F:SF (V:=V) 0) (n:Nat) : (closedAt F n).shift=closedAt F.shift n := by
  simp [closedAt,Bootstrapping.Semiformula.shift_substs]
@[simp] theorem closedAt_subst (F:SF (V:=V) 0) (w:Bootstrapping.SemitermVec V RelationalSource.language n m) :
    (closedAt F n).subst w=closedAt F m := by simp [closedAt,Bootstrapping.Semiformula.substs_substs]
@[simp] theorem closedAt_zero (F:SF (V:=V) 0) : closedAt F 0=F := by simp [closedAt]
noncomputable def uniform (F:SF (V:=V) 0) (D P R:SF (V:=V) 1) (S:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ (closedAt F 2 🡒 ((unary D (Semiterm.bvar 1) ⋏
    (unary D (Semiterm.bvar 0) ⋏ binary S (Semiterm.bvar 1) (Semiterm.bvar 0))) 🡒
      ((unary R (Semiterm.bvar 1) 🡒 unary P (Semiterm.bvar 0)) ⋏
        (unary P (Semiterm.bvar 0) 🡒 unary R (Semiterm.bvar 1)))))
noncomputable def sourceStep (D P R:SF (V:=V) 1) : SF (V:=V) 0 :=
  ∀¹ (D 🡒 (P 🡒 R))
noncomputable def targetStep (D P:SF (V:=V) 1) (S:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ((unary D (Semiterm.bvar 1) ⋏ (unary D (Semiterm.bvar 0) ⋏
    (binary S (Semiterm.bvar 1) (Semiterm.bvar 0) ⋏ unary P (Semiterm.bvar 1)))) 🡒 unary P (Semiterm.bvar 0))
@[simp] theorem uniform_shift (F:SF (V:=V) 0) (D P R:SF (V:=V) 1) (S:SF (V:=V) 2) :
    (uniform F D P R S).shift=uniform F.shift D.shift P.shift R.shift S.shift := by simp [uniform]
@[simp] theorem sourceStep_shift (D P R:SF (V:=V) 1) :
    (sourceStep D P R).shift=sourceStep D.shift P.shift R.shift := by simp [sourceStep]
@[simp] theorem targetStep_shift (D P:SF (V:=V) 1) (S:SF (V:=V) 2) :
    (targetStep D P S).shift=targetStep D.shift P.shift S.shift := by simp [targetStep]
variable {T:InternalTheory V RelationalSource.language}
noncomputable def uniformAt {Γ:ND.Seq (V:=V)} (F:SF (V:=V) 0) (D P R:SF (V:=V) 1) (S:SF (V:=V) 2)
    (x y:ST (V:=V) 0) (h:ND.Proof (T:=T) Γ (uniform F D P R S)) :
    ND.Proof (T:=T) Γ (F 🡒 ((unary D x ⋏ (unary D y ⋏ binary S x y)) 🡒
      ((unary R x 🡒 unary P y) ⋏ (unary P y 🡒 unary R x)))) := by
  have h1 : ND.Proof (T:=T) Γ (∀¹ (closedAt F 1 🡒 ((unary D x.bShift ⋏
      (unary D (Semiterm.bvar 0) ⋏ binary S x.bShift (Semiterm.bvar 0))) 🡒
      ((unary R x.bShift 🡒 unary P (Semiterm.bvar 0)) ⋏ (unary P (Semiterm.bvar 0) 🡒 unary R x.bShift))))) := by
    simpa [uniform,SemitermVec.q] using ND.allElim h x
  simpa using ND.allElim h1 y
#print axioms closedAt_shift
#print axioms closedAt_subst
#print axioms closedAt_zero
#print axioms uniform_shift
#print axioms sourceStep_shift
#print axioms targetStep_shift
#print axioms uniformAt
end PA196.Arithmetic.Transport.NumericPAeqInductionStepTemplate

