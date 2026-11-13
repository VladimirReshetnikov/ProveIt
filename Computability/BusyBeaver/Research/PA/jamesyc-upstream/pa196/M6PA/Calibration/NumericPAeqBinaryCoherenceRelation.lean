module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceSyntax
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def binaryRelationAt {Γ:ND.Seq (V:=V)} (D:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2)
    (x y b c r s:ST (V:=V) 0) (h:ND.Proof (T:=T) Γ (binaryRelation D F R))
    (hx:ND.Proof (T:=T) Γ (unary D x)) (hy:ND.Proof (T:=T) Γ (unary D y))
    (hb:ND.Proof (T:=T) Γ (unary D b)) (hc:ND.Proof (T:=T) Γ (unary D c))
    (hi:ND.Proof (T:=T) Γ (binary R x y)) (hj:ND.Proof (T:=T) Γ (binary R b c))
    (hr:ND.Proof (T:=T) Γ (ternary F x b r)) (hs:ND.Proof (T:=T) Γ (ternary F y c s)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  have h0 : ND.Proof (T:=T) Γ (unary D x 🡒 ∀¹ ∀¹ ∀¹ ∀¹ ∀¹ binaryPoint D F R x.bShift.bShift.bShift.bShift.bShift (Semiterm.bvar 4) (Semiterm.bvar 3) (Semiterm.bvar 2) (Semiterm.bvar 1) (Semiterm.bvar 0)) := by
    simpa [binaryRelation,SemitermVec.q] using ND.allElim h x
  have h1 := ND.mp hx h0
  have h2 : ND.Proof (T:=T) Γ (∀¹ ∀¹ ∀¹ ∀¹ binaryPoint D F R x.bShift.bShift.bShift.bShift y.bShift.bShift.bShift.bShift (Semiterm.bvar 3) (Semiterm.bvar 2) (Semiterm.bvar 1) (Semiterm.bvar 0)) := by
    have hh := ND.allElim h1 y
    simp only [Bootstrapping.Semiformula.substs_all,binaryPoint_subst,
      Bootstrapping.Semiterm.bShift_substs_q,Bootstrapping.Semiterm.bShift_substs_sing,
      Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have h3 : ND.Proof (T:=T) Γ (∀¹ ∀¹ ∀¹ binaryPoint D F R x.bShift.bShift.bShift y.bShift.bShift.bShift b.bShift.bShift.bShift (Semiterm.bvar 2) (Semiterm.bvar 1) (Semiterm.bvar 0)) := by
    have hh := ND.allElim h2 b
    simp only [Bootstrapping.Semiformula.substs_all,binaryPoint_subst,
      Bootstrapping.Semiterm.bShift_substs_q,Bootstrapping.Semiterm.bShift_substs_sing,
      Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have h4 : ND.Proof (T:=T) Γ (∀¹ ∀¹ binaryPoint D F R x.bShift.bShift y.bShift.bShift b.bShift.bShift c.bShift.bShift (Semiterm.bvar 1) (Semiterm.bvar 0)) := by
    have hh := ND.allElim h3 c
    simp only [Bootstrapping.Semiformula.substs_all,binaryPoint_subst,
      Bootstrapping.Semiterm.bShift_substs_q,Bootstrapping.Semiterm.bShift_substs_sing,
      Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have h5 : ND.Proof (T:=T) Γ (∀¹ binaryPoint D F R x.bShift y.bShift b.bShift c.bShift r.bShift (Semiterm.bvar 0)) := by
    have hh := ND.allElim h4 r
    simp only [Bootstrapping.Semiformula.substs_all,binaryPoint_subst,
      Bootstrapping.Semiterm.bShift_substs_q,Bootstrapping.Semiterm.bShift_substs_sing,
      Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have h6 : ND.Proof (T:=T) Γ (binaryPoint D F R x y b c r s) := by
    have hh := ND.allElim h5 s
    simp only [Bootstrapping.Semiformula.substs_all,binaryPoint_subst,
      Bootstrapping.Semiterm.bShift_substs_q,Bootstrapping.Semiterm.bShift_substs_sing,
      Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  exact ND.mp (ND.andIntro hy (ND.andIntro hb (ND.andIntro hc (ND.andIntro hi (ND.andIntro hj (ND.andIntro hr hs)))))) h6
#print axioms binaryRelationAt
end M6.PA.NumericPAeqValueCoherence
