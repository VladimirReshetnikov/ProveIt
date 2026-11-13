module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorBoth
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T:InternalTheory V RelationalSource.language}
@[simp] theorem successorOutput_subst (D P:SF (V:=V) 1) (S:SF (V:=V) 2) (r:ST (V:=V) n)
    (w:Bootstrapping.SemitermVec V RelationalSource.language n m) :
    (successorOutput D P S r).subst w=successorOutput D P S (r.subst w) := by simp [successorOutput]
noncomputable def successorComparisonTyped (D P Q:SF (V:=V) 1) (S R:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ((successorOutput D (D ⋏ P) S (Semiterm.bvar 1) ⋏ successorOutput D (D ⋏ Q) S (Semiterm.bvar 0)) 🡒
    binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
noncomputable def successorComparisonProof (D P Q:SF (V:=V) 1) (S R:SF (V:=V) 2) :
    ND.Proof (T:=T) (insert (∼successorRelation D S R) ∅)
      (pairwise (D ⋏ P) (D ⋏ Q) R 🡒 successorComparisonTyped D P Q S R) := by
  apply ND.impIntro
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_imp,
    Bootstrapping.Semiformula.shift_and,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,successorOutput_shift,successorOutput_subst,binary_shift,binary_subst]
  apply ND.impIntro
  let r : ST (V:=V) 0 := Semiterm.fvar 1
  let s : ST (V:=V) 0 := Semiterm.fvar 0
  let A := successorOutput D.shift.shift (D.shift.shift ⋏ P.shift.shift) S.shift.shift r ⋏
    successorOutput D.shift.shift (D.shift.shift ⋏ Q.shift.shift) S.shift.shift s
  let C : ND.Seq (V:=V) := insert (∼A)
    ((insert (∼pairwise (D ⋏ P) (D ⋏ Q) R) (insert (∼successorRelation D S R) ∅) : ND.Seq (V:=V)).shift.shift)
  have hpair : ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have hi : ND.Proof (T:=T) C (pairwise (D.shift.shift ⋏ P.shift.shift) (D.shift.shift ⋏ Q.shift.shift) R.shift.shift) := by
    apply ND.assumption
    simp [C]
  have hs : ND.Proof (T:=T) C (successorRelation D.shift.shift S.shift.shift R.shift.shift) := by
    apply ND.assumption
    simp [C]
  have out := successorBothWitnesses D.shift.shift P.shift.shift Q.shift.shift S.shift.shift R.shift.shift r s
    (ND.andLeft hpair) (ND.andRight hpair) hi hs
  simpa [C,A,r,s,SemitermVec.q] using out
#print axioms successorOutput_subst
#print axioms successorComparisonProof
end M6.PA.NumericPAeqValueCoherence

