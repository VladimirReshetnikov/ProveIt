module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceTyped
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def pairwise (P Q:SF (V:=V) 1) (R:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ((unary P (Semiterm.bvar 1) ⋏ unary Q (Semiterm.bvar 0)) 🡒 binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
@[simp] theorem pairwise_shift (P Q:SF (V:=V) 1) (R:SF (V:=V) 2) :
    (pairwise P Q R).shift=pairwise P.shift Q.shift R.shift := by simp [pairwise]
noncomputable def successorRelation (D:SF (V:=V) 1) (S R:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ∀¹ ∀¹ ((unary D (Semiterm.bvar 3) ⋏ (unary D (Semiterm.bvar 2) ⋏
    (binary S (Semiterm.bvar 3) (Semiterm.bvar 1) ⋏ (binary S (Semiterm.bvar 2) (Semiterm.bvar 0) ⋏
    binary R (Semiterm.bvar 3) (Semiterm.bvar 2))))) 🡒 binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
@[simp] theorem successorRelation_shift (D:SF (V:=V) 1) (S R:SF (V:=V) 2) :
    (successorRelation D S R).shift=successorRelation D.shift S.shift R.shift := by simp [successorRelation]
noncomputable def successorOutput (D P:SF (V:=V) 1) (S:SF (V:=V) 2) (r:ST (V:=V) n) : SF (V:=V) n :=
  unary D r ⋏ (∃¹ (unary P (Semiterm.bvar 0) ⋏ binary S (Semiterm.bvar 0) r.bShift))
@[simp] theorem successorOutput_shift (D P:SF (V:=V) 1) (S:SF (V:=V) 2) (r:ST (V:=V) n) :
    (successorOutput D P S r).shift=successorOutput D.shift P.shift S.shift r.shift := by simp [successorOutput,Bootstrapping.Semiterm.bShift_shift_comm]
variable {T:InternalTheory V RelationalSource.language}
noncomputable def pairwiseAt {Γ:ND.Seq (V:=V)} (P Q:SF (V:=V) 1) (R:SF (V:=V) 2) (x y:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (pairwise P Q R)) (hp:ND.Proof (T:=T) Γ (unary P x))
    (hq:ND.Proof (T:=T) Γ (unary Q y)) : ND.Proof (T:=T) Γ (binary R x y) := by
  have first : ND.Proof (T:=T) Γ (∀¹ ((unary P x.bShift ⋏ unary Q (Semiterm.bvar 0)) 🡒 binary R x.bShift (Semiterm.bvar 0))) := by
    simpa [pairwise,Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,SemitermVec.q] using ND.allElim h x
  have last : ND.Proof (T:=T) Γ ((unary P x ⋏ unary Q y) 🡒 binary R x y) := by
    simpa [Bootstrapping.Semiformula.substs_imp,Bootstrapping.Semiformula.substs_and,SemitermVec.q] using ND.allElim first y
  exact ND.mp (ND.andIntro hp hq) last
#print axioms pairwise_shift
#print axioms successorRelation_shift
#print axioms successorOutput_shift
#print axioms pairwiseAt
end M6.PA.NumericPAeqValueCoherence

