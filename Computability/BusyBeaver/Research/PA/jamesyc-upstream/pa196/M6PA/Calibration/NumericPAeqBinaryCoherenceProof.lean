module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceLeft
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
@[simp] theorem binaryOutput_unary (D P Q:SF (V:=V) 1) (F:SF (V:=V) 3) (z:ST (V:=V) n) :
    unary (binaryOutput D P Q F (Semiterm.bvar 0)) z=binaryOutput D P Q F z := by simp [unary]
noncomputable def binaryComparison (D P Q U W:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2) : SF (V:=V) 0 :=
  pairwise (binaryOutput D (D ⋏ P) (D ⋏ Q) F (Semiterm.bvar 0))
    (binaryOutput D (D ⋏ U) (D ⋏ W) F (Semiterm.bvar 0)) R
noncomputable def binaryCoherenceStatement (D P Q U W:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2) : SF (V:=V) 0 :=
  (pairwise (D ⋏ P) (D ⋏ U) R ⋏ pairwise (D ⋏ Q) (D ⋏ W) R) 🡒 binaryComparison D P Q U W F R
variable {T : InternalTheory V RelationalSource.language}
noncomputable def binaryCoherenceProof (D P Q U W:SF (V:=V) 1) (F:SF (V:=V) 3) (R:SF (V:=V) 2) :
    ND.Proof (T:=T) (insert (∼binaryRelation D F R) ∅) (binaryCoherenceStatement D P Q U W F R) := by
  apply ND.impIntro
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,unary_shift,binary_shift,unary_subst,binary_subst]
  apply ND.impIntro
  let r : ST (V:=V) 0 := Semiterm.fvar 1
  let s : ST (V:=V) 0 := Semiterm.fvar 0
  let I := pairwise (D ⋏ P) (D ⋏ U) R ⋏ pairwise (D ⋏ Q) (D ⋏ W) R
  let A := binaryOutput D.shift.shift (D.shift.shift ⋏ P.shift.shift) (D.shift.shift ⋏ Q.shift.shift) F.shift.shift r ⋏
    binaryOutput D.shift.shift (D.shift.shift ⋏ U.shift.shift) (D.shift.shift ⋏ W.shift.shift) F.shift.shift s
  let C : ND.Seq (V:=V) := insert (∼A) ((insert (∼I) (insert (∼binaryRelation D F R) ∅) : ND.Seq (V:=V)).shift.shift)
  have hp : ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have ht : ND.Proof (T:=T) C (binaryRelation D.shift.shift F.shift.shift R.shift.shift) := by
    apply ND.assumption
    simp [C]
  have hi : ND.Proof (T:=T) C (pairwise (D.shift.shift ⋏ P.shift.shift) (D.shift.shift ⋏ U.shift.shift) R.shift.shift ⋏
      pairwise (D.shift.shift ⋏ Q.shift.shift) (D.shift.shift ⋏ W.shift.shift) R.shift.shift) := by
    apply ND.assumption
    simp [C,I]
  have out := binaryOutputsCoherent D.shift.shift P.shift.shift Q.shift.shift U.shift.shift W.shift.shift
    F.shift.shift R.shift.shift r s ht (ND.andLeft hi) (ND.andRight hi) (ND.andLeft hp) (ND.andRight hp)
  simpa [C,A,I,r,s,SemitermVec.q] using out
#print axioms binaryCoherenceProof
end M6.PA.NumericPAeqValueCoherence
