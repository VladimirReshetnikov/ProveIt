module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransportDestination
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def transportRemainder {Γ : ND.Seq (V:=V)} (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2) (a : ST (V:=V) 0)
    (hs : ND.Proof (T:=T) Γ (symmetry D R))
    (ht : ND.Proof (T:=T) Γ (transitivity D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj : ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hr : ND.Proof (T:=T) Γ (equalityRemainder (D ⋏ P) (D ⋏ Q) R a))
    (hu : ND.Proof (T:=T) Γ (∃¹ (D ⋏ U)))
    (hw : ND.Proof (T:=T) Γ (∃¹ (D ⋏ W)))
    : ND.Proof (T:=T) Γ (equalityAtom (D ⋏ U) (D ⋏ W) R) := by
  let body := unary (D ⋏ P) a.bShift ⋏
    (unary (D ⋏ Q) (Semiterm.bvar 0) ⋏ binary R a.bShift (Semiterm.bvar 0))
  apply ND.exsElim (p:=body) hr
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  let b : ST (V:=V) 0 := Semiterm.fvar 0
  have hh : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) a.shift ⋏
      (unary (D.shift ⋏ Q.shift) b ⋏ binary R.shift a.shift b)) := by
    simpa [body,b,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hs' : ND.Proof (T:=T) C (symmetry D.shift R.shift) := by simpa [C] using ND.up (ND.shift hs) body.free
  have ht' : ND.Proof (T:=T) C (transitivity D.shift R.shift) := by simpa [C] using ND.up (ND.shift ht) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hu' : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ U.shift)) := by simpa [C] using ND.up (ND.shift hu) body.free
  have hw' : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ W.shift)) := by simpa [C] using ND.up (ND.shift hw) body.free
  simpa using transportDestination D.shift P.shift Q.shift U.shift W.shift R.shift a.shift b
    hs' ht' hi' hj' (ND.andLeft hh) (ND.andLeft (ND.andRight hh)) (ND.andRight (ND.andRight hh)) hu' hw'

noncomputable def transportForward {Γ : ND.Seq (V:=V)} (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2)
    (hs : ND.Proof (T:=T) Γ (symmetry D R))
    (ht : ND.Proof (T:=T) Γ (transitivity D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj : ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hr : ND.Proof (T:=T) Γ (equalityAtom (D ⋏ P) (D ⋏ Q) R))
    (hu : ND.Proof (T:=T) Γ (∃¹ (D ⋏ U)))
    (hw : ND.Proof (T:=T) Γ (∃¹ (D ⋏ W)))
    : ND.Proof (T:=T) Γ (equalityAtom (D ⋏ U) (D ⋏ W) R) := by
  let body : SF (V:=V) 1 := ∃¹ (unary (D ⋏ P) (Semiterm.bvar 1) ⋏
    (unary (D ⋏ Q) (Semiterm.bvar 0) ⋏ binary R (Semiterm.bvar 1) (Semiterm.bvar 0)))
  apply ND.exsElim (p:=body) hr
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  let a : ST (V:=V) 0 := Semiterm.fvar 0
  have hh : ND.Proof (T:=T) C (equalityRemainder (D.shift ⋏ P.shift) (D.shift ⋏ Q.shift) R.shift a) := by
    simpa [body,a,equalityRemainder,Bootstrapping.Semiformula.free,SemitermVec.q] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hs' : ND.Proof (T:=T) C (symmetry D.shift R.shift) := by simpa [C] using ND.up (ND.shift hs) body.free
  have ht' : ND.Proof (T:=T) C (transitivity D.shift R.shift) := by simpa [C] using ND.up (ND.shift ht) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hu' : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ U.shift)) := by simpa [C] using ND.up (ND.shift hu) body.free
  have hw' : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ W.shift)) := by simpa [C] using ND.up (ND.shift hw) body.free
  simpa using transportRemainder D.shift P.shift Q.shift U.shift W.shift R.shift a
    hs' ht' hi' hj' hh hu' hw'
#print axioms transportRemainder
#print axioms transportForward
end PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransport
