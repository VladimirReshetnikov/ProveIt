module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorSyntax
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T:InternalTheory V RelationalSource.language}
noncomputable def successorRelationAt {Γ:ND.Seq (V:=V)} (D:SF (V:=V) 1) (S R:SF (V:=V) 2)
    (a b r s:ST (V:=V) 0) (h:ND.Proof (T:=T) Γ (successorRelation D S R))
    (ha:ND.Proof (T:=T) Γ (unary D a)) (hb:ND.Proof (T:=T) Γ (unary D b))
    (har:ND.Proof (T:=T) Γ (binary S a r)) (hbs:ND.Proof (T:=T) Γ (binary S b s))
    (hab:ND.Proof (T:=T) Γ (binary R a b)) : ND.Proof (T:=T) Γ (binary R r s) := by
  have h1 : ND.Proof (T:=T) Γ (∀¹ ∀¹ ∀¹
      ((unary D a.bShift.bShift.bShift ⋏ (unary D (Semiterm.bvar 2) ⋏
      (binary S a.bShift.bShift.bShift (Semiterm.bvar 1) ⋏ (binary S (Semiterm.bvar 2) (Semiterm.bvar 0) ⋏
      binary R a.bShift.bShift.bShift (Semiterm.bvar 2))))) 🡒 binary R (Semiterm.bvar 1) (Semiterm.bvar 0))) := by
    simpa [successorRelation,Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,Bootstrapping.Semiterm.bShift_substs_succ,SemitermVec.q] using ND.allElim h a
  have h2 : ND.Proof (T:=T) Γ (∀¹ ∀¹
      ((unary D a.bShift.bShift ⋏ (unary D b.bShift.bShift ⋏
      (binary S a.bShift.bShift (Semiterm.bvar 1) ⋏ (binary S b.bShift.bShift (Semiterm.bvar 0) ⋏
      binary R a.bShift.bShift b.bShift.bShift)))) 🡒 binary R (Semiterm.bvar 1) (Semiterm.bvar 0))) := by
    have he := ND.allElim h1 b
    simp only [Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,unary_subst,binary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing] at he
    simpa [SemitermVec.q] using he
  have h3 : ND.Proof (T:=T) Γ (∀¹
      ((unary D a.bShift ⋏ (unary D b.bShift ⋏
      (binary S a.bShift r.bShift ⋏ (binary S b.bShift (Semiterm.bvar 0) ⋏
      binary R a.bShift b.bShift)))) 🡒 binary R r.bShift (Semiterm.bvar 0))) := by
    have he := ND.allElim h2 r
    simp only [Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,unary_subst,binary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing] at he
    simpa [SemitermVec.q] using he
  have h4 : ND.Proof (T:=T) Γ ((unary D a ⋏ (unary D b ⋏ (binary S a r ⋏ (binary S b s ⋏ binary R a b)))) 🡒 binary R r s) := by
    simpa [Bootstrapping.Semiformula.substs_imp,Bootstrapping.Semiformula.substs_and,Bootstrapping.Semiterm.bShift_substs_succ,SemitermVec.q] using ND.allElim h3 s
  exact ND.mp (ND.andIntro ha (ND.andIntro hb (ND.andIntro har (ND.andIntro hbs hab)))) h4
#print axioms successorRelationAt
end M6.PA.NumericPAeqValueCoherence

