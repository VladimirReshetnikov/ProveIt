module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherencePoint
public import M6PA.Calibration.NumericPAeqBinaryCoherenceOpening
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def binaryRightRemainder {Γ:ND.Seq (V:=V)} (D P Q U W:SF (V:=V) 1)
    (F:SF (V:=V) 3) (R:SF (V:=V) 2) (x y b r s:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (binaryRelation D F R))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj:ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hp:ND.Proof (T:=T) Γ (unary (D ⋏ P) x)) (hq:ND.Proof (T:=T) Γ (unary (D ⋏ Q) b))
    (hr:ND.Proof (T:=T) Γ (ternary F x b r))
    (hs:ND.Proof (T:=T) Γ (binaryRemainder (D ⋏ U) (D ⋏ W) F y s)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  let body := unary (D ⋏ U) y.bShift ⋏
    (unary (D ⋏ W) (Semiterm.bvar 0) ⋏ ternary F y.bShift (Semiterm.bvar 0) s.bShift)
  apply ND.exsElim (p:=body) hs
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hh : ND.Proof (T:=T) C (unary (D.shift ⋏ U.shift) y.shift ⋏
      (unary (D.shift ⋏ W.shift) (Semiterm.fvar 0) ⋏ ternary F.shift y.shift (Semiterm.fvar 0) s.shift)) := by
    simpa [body] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have h' : ND.Proof (T:=T) C (binaryRelation D.shift F.shift R.shift) := by simpa [C] using ND.up (ND.shift h) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hp' : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) x.shift) := by simpa [C] using ND.up (ND.shift hp) body.free
  have hq' : ND.Proof (T:=T) C (unary (D.shift ⋏ Q.shift) b.shift) := by simpa [C] using ND.up (ND.shift hq) body.free
  have hr' : ND.Proof (T:=T) C (ternary F.shift x.shift b.shift r.shift) := by simpa [C] using ND.up (ND.shift hr) body.free
  simpa using binaryCoherenceAt D.shift P.shift Q.shift U.shift W.shift F.shift R.shift
    x.shift y.shift b.shift (Semiterm.fvar 0) r.shift s.shift h' hi' hj' hp' (ND.andLeft hh)
    hq' (ND.andLeft (ND.andRight hh)) hr' (ND.andRight (ND.andRight hh))

noncomputable def binaryRightOutput {Γ:ND.Seq (V:=V)} (D P Q U W:SF (V:=V) 1)
    (F:SF (V:=V) 3) (R:SF (V:=V) 2) (x b r s:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (binaryRelation D F R))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj:ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hp:ND.Proof (T:=T) Γ (unary (D ⋏ P) x)) (hq:ND.Proof (T:=T) Γ (unary (D ⋏ Q) b))
    (hr:ND.Proof (T:=T) Γ (ternary F x b r))
    (hs:ND.Proof (T:=T) Γ (binaryOutput D (D ⋏ U) (D ⋏ W) F s)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  let body := ∃¹ (unary (D ⋏ U) (Semiterm.bvar 1) ⋏
    (unary (D ⋏ W) (Semiterm.bvar 0) ⋏ ternary F (Semiterm.bvar 1) (Semiterm.bvar 0) s.bShift.bShift))
  apply ND.exsElim (p:=body) (ND.andRight hs)
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hh : ND.Proof (T:=T) C (binaryRemainder (D.shift ⋏ U.shift) (D.shift ⋏ W.shift) F.shift (Semiterm.fvar 0) s.shift) := by
    simpa [body] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have h' : ND.Proof (T:=T) C (binaryRelation D.shift F.shift R.shift) := by simpa [C] using ND.up (ND.shift h) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hp' : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) x.shift) := by simpa [C] using ND.up (ND.shift hp) body.free
  have hq' : ND.Proof (T:=T) C (unary (D.shift ⋏ Q.shift) b.shift) := by simpa [C] using ND.up (ND.shift hq) body.free
  have hr' : ND.Proof (T:=T) C (ternary F.shift x.shift b.shift r.shift) := by simpa [C] using ND.up (ND.shift hr) body.free
  simpa using binaryRightRemainder D.shift P.shift Q.shift U.shift W.shift F.shift R.shift
    x.shift (Semiterm.fvar 0) b.shift r.shift s.shift h' hi' hj' hp' hq' hr' hh
#print axioms binaryRightRemainder
#print axioms binaryRightOutput
end M6.PA.NumericPAeqValueCoherence
