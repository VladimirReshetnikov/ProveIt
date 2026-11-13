module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportTyped
@[expose] public section
namespace M6.PA.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def transportRight {Γ : ND.Seq (V:=V)} (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2) (a b c : ST (V:=V) 0)
    (hs : ND.Proof (T:=T) Γ (symmetry D R))
    (ht : ND.Proof (T:=T) Γ (transitivity D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj : ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hp : ND.Proof (T:=T) Γ (unary (D ⋏ P) a))
    (hq : ND.Proof (T:=T) Γ (unary (D ⋏ Q) b))
    (hu : ND.Proof (T:=T) Γ (unary (D ⋏ U) c))
    (hab : ND.Proof (T:=T) Γ (binary R a b))
    (hw : ND.Proof (T:=T) Γ (∃¹ (D ⋏ W)))
    : ND.Proof (T:=T) Γ (equalityAtom (D ⋏ U) (D ⋏ W) R) := by
  let body := D ⋏ W
  apply ND.exsElim (p:=body) hw
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  let d : ST (V:=V) 0 := Semiterm.fvar 0
  have hd : ND.Proof (T:=T) C (unary (D.shift ⋏ W.shift) d) := by
    simpa [body,unary,d,Bootstrapping.Semiformula.free] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hs' : ND.Proof (T:=T) C (symmetry D.shift R.shift) := by simpa [C] using ND.up (ND.shift hs) body.free
  have ht' : ND.Proof (T:=T) C (transitivity D.shift R.shift) := by simpa [C] using ND.up (ND.shift ht) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hp' : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) a.shift) := by simpa [C] using ND.up (ND.shift hp) body.free
  have hq' : ND.Proof (T:=T) C (unary (D.shift ⋏ Q.shift) b.shift) := by simpa [C] using ND.up (ND.shift hq) body.free
  have hu' : ND.Proof (T:=T) C (unary (D.shift ⋏ U.shift) c.shift) := by simpa [C] using ND.up (ND.shift hu) body.free
  have hab' : ND.Proof (T:=T) C (binary R.shift a.shift b.shift) := by simpa [C] using ND.up (ND.shift hab) body.free
  have hac := pairwiseAt _ _ _ a.shift c.shift hi' hp' hu'
  have hbd := pairwiseAt _ _ _ b.shift d hj' hq' hd
  simp only [unary,Bootstrapping.Semiformula.substs_and] at hp' hu'
  have ha : ND.Proof (T:=T) C (unary D.shift a.shift) := by simpa [unary] using ND.andLeft hp'
  have hc : ND.Proof (T:=T) C (unary D.shift c.shift) := by simpa [unary] using ND.andLeft hu'
  have hca := symmetryAt _ _ a.shift c.shift hs' ha hac
  have hcb := transitivityAt _ _ c.shift a.shift b.shift ht' hc hca hab'
  have hcd := transitivityAt _ _ c.shift b.shift d ht' hc hcb hbd
  simpa using equalityAtomIntro _ _ _ c.shift d (by simpa [unary] using hu') hd hcd
#print axioms transportRight
end M6.PA.NumericPAeqFormulaEqualityTransport
