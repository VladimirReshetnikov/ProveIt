module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportRight
@[expose] public section
namespace M6.PA.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def transportDestination {Γ : ND.Seq (V:=V)} (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2) (a b : ST (V:=V) 0)
    (hs : ND.Proof (T:=T) Γ (symmetry D R))
    (ht : ND.Proof (T:=T) Γ (transitivity D R))
    (hi : ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ U) R))
    (hj : ND.Proof (T:=T) Γ (pairwise (D ⋏ Q) (D ⋏ W) R))
    (hp : ND.Proof (T:=T) Γ (unary (D ⋏ P) a))
    (hq : ND.Proof (T:=T) Γ (unary (D ⋏ Q) b))
    (hab : ND.Proof (T:=T) Γ (binary R a b))
    (hu : ND.Proof (T:=T) Γ (∃¹ (D ⋏ U)))
    (hw : ND.Proof (T:=T) Γ (∃¹ (D ⋏ W)))
    : ND.Proof (T:=T) Γ (equalityAtom (D ⋏ U) (D ⋏ W) R) := by
  let body := D ⋏ U
  apply ND.exsElim (p:=body) hu
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  let c : ST (V:=V) 0 := Semiterm.fvar 0
  have hc : ND.Proof (T:=T) C (unary (D.shift ⋏ U.shift) c) := by
    simpa [body,unary,c,Bootstrapping.Semiformula.free] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hs' : ND.Proof (T:=T) C (symmetry D.shift R.shift) := by simpa [C] using ND.up (ND.shift hs) body.free
  have ht' : ND.Proof (T:=T) C (transitivity D.shift R.shift) := by simpa [C] using ND.up (ND.shift ht) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ U.shift) R.shift) := by simpa [C] using ND.up (ND.shift hi) body.free
  have hj' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ Q.shift) (D.shift ⋏ W.shift) R.shift) := by simpa [C] using ND.up (ND.shift hj) body.free
  have hp' : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) a.shift) := by simpa [C] using ND.up (ND.shift hp) body.free
  have hq' : ND.Proof (T:=T) C (unary (D.shift ⋏ Q.shift) b.shift) := by simpa [C] using ND.up (ND.shift hq) body.free
  have hab' : ND.Proof (T:=T) C (binary R.shift a.shift b.shift) := by simpa [C] using ND.up (ND.shift hab) body.free
  have hw' : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ W.shift)) := by simpa [C] using ND.up (ND.shift hw) body.free
  simpa using transportRight D.shift P.shift Q.shift U.shift W.shift R.shift a.shift b.shift c
    hs' ht' hi' hj' hp' hq' hc hab' hw'
#print axioms transportDestination
end M6.PA.NumericPAeqFormulaEqualityTransport
