module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportForward
@[expose] public section
namespace M6.PA.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def pairwiseReverse {Γ : ND.Seq (V:=V)} (D P U : SF (V:=V) 1) (R : SF (V:=V) 2)
    (hs : ND.Proof (T:=T) Γ (symmetry D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R)) :
    ND.Proof (T:=T) Γ (pairwise (D ⋏ U) (D ⋏ P) R) := by
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [pairwise,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,unary_shift,binary_shift,unary_subst,binary_subst]
  apply ND.impIntro
  let c : ST (V:=V) 0 := Semiterm.fvar 1
  let a : ST (V:=V) 0 := Semiterm.fvar 0
  let A := unary (D.shift.shift ⋏ U.shift.shift) c ⋏ unary (D.shift.shift ⋏ P.shift.shift) a
  let C : ND.Seq (V:=V) := insert (∼A) Γ.shift.shift
  have hh : ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have hs' : ND.Proof (T:=T) C (symmetry D.shift.shift R.shift.shift) := by simpa [C] using ND.up (ND.shift (ND.shift hs)) A
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift.shift ⋏ P.shift.shift) (D.shift.shift ⋏ U.shift.shift) R.shift.shift) := by
    simpa [C] using ND.up (ND.shift (ND.shift hi)) A
  have hac := pairwiseAt _ _ _ a c hi' (ND.andRight hh) (ND.andLeft hh)
  have hp : ND.Proof (T:=T) C (unary D.shift.shift a ⋏ unary P.shift.shift a) := by
    simpa [A,unary] using ND.andRight hh
  simpa [C,A,c,a,SemitermVec.q] using symmetryAt _ _ a c hs' (ND.andLeft hp) hac

noncomputable def transportArrow {Γ : ND.Seq (V:=V)} (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2)
    (hs : ND.Proof (T:=T) Γ (symmetry D R)) (ht : ND.Proof (T:=T) Γ (transitivity D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj : ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hu : ND.Proof (T:=T) Γ (∃¹ (D ⋏ U))) (hw : ND.Proof (T:=T) Γ (∃¹ (D ⋏ W))) :
    ND.Proof (T:=T) Γ (equalityAtom (D ⋏ P) (D ⋏ Q) R 🡒 equalityAtom (D ⋏ U) (D ⋏ W) R) := by
  apply ND.impIntro
  let A := equalityAtom (D ⋏ P) (D ⋏ Q) R
  have ha : ND.Proof (T:=T) (insert (∼A) Γ) A := ND.assumption _ (by simp)
  exact transportForward D P Q U W R (ND.up hs A) (ND.up ht A) (ND.up hi A) (ND.up hj A) ha (ND.up hu A) (ND.up hw A)

noncomputable def transportBoth {Γ : ND.Seq (V:=V)} (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2)
    (hs : ND.Proof (T:=T) Γ (symmetry D R)) (ht : ND.Proof (T:=T) Γ (transitivity D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj : ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hp : ND.Proof (T:=T) Γ (∃¹ (D ⋏ P))) (hq : ND.Proof (T:=T) Γ (∃¹ (D ⋏ Q)))
    (hu : ND.Proof (T:=T) Γ (∃¹ (D ⋏ U))) (hw : ND.Proof (T:=T) Γ (∃¹ (D ⋏ W))) :
    ND.Proof (T:=T) Γ ((equalityAtom (D ⋏ P) (D ⋏ Q) R 🡒 equalityAtom (D ⋏ U) (D ⋏ W) R) ⋏
      (equalityAtom (D ⋏ U) (D ⋏ W) R 🡒 equalityAtom (D ⋏ P) (D ⋏ Q) R)) :=
  ND.andIntro (transportArrow D P Q U W R hs ht hi hj hu hw)
    (transportArrow D U W P Q R hs ht (pairwiseReverse D P U R hs hi) (pairwiseReverse D Q W R hs hj) hp hq)
#print axioms pairwiseReverse
#print axioms transportArrow
#print axioms transportBoth
end M6.PA.NumericPAeqFormulaEqualityTransport
