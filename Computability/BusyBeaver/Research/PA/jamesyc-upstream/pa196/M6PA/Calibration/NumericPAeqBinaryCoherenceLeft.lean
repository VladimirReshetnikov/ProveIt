module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceRight
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def binaryLeftRemainder {Γ:ND.Seq (V:=V)} (D P Q U W:SF (V:=V) 1)
    (F:SF (V:=V) 3) (R:SF (V:=V) 2) (x r s:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (binaryRelation D F R))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj:ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hr:ND.Proof (T:=T) Γ (binaryRemainder (D ⋏ P) (D ⋏ Q) F x r))
    (hs:ND.Proof (T:=T) Γ (binaryOutput D (D ⋏ U) (D ⋏ W) F s)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  let body := unary (D ⋏ P) x.bShift ⋏
    (unary (D ⋏ Q) (Semiterm.bvar 0) ⋏ ternary F x.bShift (Semiterm.bvar 0) r.bShift)
  apply ND.exsElim (p:=body) hr
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hh : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) x.shift ⋏
      (unary (D.shift ⋏ Q.shift) (Semiterm.fvar 0) ⋏ ternary F.shift x.shift (Semiterm.fvar 0) r.shift)) := by
    simpa [body] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have h' : ND.Proof (T:=T) C (binaryRelation D.shift F.shift R.shift) := by simpa [C] using ND.up (ND.shift h) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hs' : ND.Proof (T:=T) C (binaryOutput D.shift (D.shift ⋏ U.shift) (D.shift ⋏ W.shift) F.shift s.shift) := by simpa [C] using ND.up (ND.shift hs) body.free
  simpa using binaryRightOutput D.shift P.shift Q.shift U.shift W.shift F.shift R.shift
    x.shift (Semiterm.fvar 0) r.shift s.shift h' hi' hj' (ND.andLeft hh)
    (ND.andLeft (ND.andRight hh)) (ND.andRight (ND.andRight hh)) hs'

noncomputable def binaryOutputsCoherent {Γ:ND.Seq (V:=V)} (D P Q U W:SF (V:=V) 1)
    (F:SF (V:=V) 3) (R:SF (V:=V) 2) (r s:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (binaryRelation D F R))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj:ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hr:ND.Proof (T:=T) Γ (binaryOutput D (D ⋏ P) (D ⋏ Q) F r))
    (hs:ND.Proof (T:=T) Γ (binaryOutput D (D ⋏ U) (D ⋏ W) F s)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  let body := ∃¹ (unary (D ⋏ P) (Semiterm.bvar 1) ⋏
    (unary (D ⋏ Q) (Semiterm.bvar 0) ⋏ ternary F (Semiterm.bvar 1) (Semiterm.bvar 0) r.bShift.bShift))
  apply ND.exsElim (p:=body) (ND.andRight hr)
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hh : ND.Proof (T:=T) C (binaryRemainder (D.shift ⋏ P.shift) (D.shift ⋏ Q.shift) F.shift (Semiterm.fvar 0) r.shift) := by
    simpa [body] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have h' : ND.Proof (T:=T) C (binaryRelation D.shift F.shift R.shift) := by simpa [C] using ND.up (ND.shift h) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hs' : ND.Proof (T:=T) C (binaryOutput D.shift (D.shift ⋏ U.shift) (D.shift ⋏ W.shift) F.shift s.shift) := by simpa [C] using ND.up (ND.shift hs) body.free
  simpa using binaryLeftRemainder D.shift P.shift Q.shift U.shift W.shift F.shift R.shift
    (Semiterm.fvar 0) r.shift s.shift h' hi' hj' hh hs'
#print axioms binaryLeftRemainder
#print axioms binaryOutputsCoherent
end M6.PA.NumericPAeqValueCoherence
