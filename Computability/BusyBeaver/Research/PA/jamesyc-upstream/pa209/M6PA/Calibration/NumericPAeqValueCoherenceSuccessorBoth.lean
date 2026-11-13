module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorWitness
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T:InternalTheory V RelationalSource.language}
noncomputable def successorBothWitnesses {Γ:ND.Seq (V:=V)} (D P Q:SF (V:=V) 1) (S R:SF (V:=V) 2)
    (r s:ST (V:=V) 0) (hp:ND.Proof (T:=T) Γ (successorOutput D (D ⋏ P) S r))
    (hq:ND.Proof (T:=T) Γ (successorOutput D (D ⋏ Q) S s))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ Q) R))
    (hs:ND.Proof (T:=T) Γ (successorRelation D S R)) : ND.Proof (T:=T) Γ (binary R r s) := by
  let body : SF (V:=V) 1 := unary (D ⋏ P) (Semiterm.bvar 0) ⋏ binary S (Semiterm.bvar 0) r.bShift
  apply ND.exsElim (p:=body) (ND.andRight hp)
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hpair : ND.Proof (T:=T) C
      (unary (D.shift ⋏ P.shift) (Semiterm.fvar 0) ⋏ binary S.shift (Semiterm.fvar 0) r.shift) := by
    simpa [body,Bootstrapping.Semiformula.free,SemitermVec.q,←Bootstrapping.Semiterm.bShift_shift_comm] using
      ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hq' : ND.Proof (T:=T) C (successorOutput D.shift (D.shift ⋏ Q.shift) S.shift s.shift) := by
    simpa [C] using ND.up (ND.shift hq) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ Q.shift) R.shift) := by
    simpa [C] using ND.up (ND.shift hi) body.free
  have hs' : ND.Proof (T:=T) C (successorRelation D.shift S.shift R.shift) := by
    simpa [C] using ND.up (ND.shift hs) body.free
  simpa using successorRightWitness D.shift P.shift Q.shift S.shift R.shift (Semiterm.fvar 0) r.shift s.shift
    (ND.andLeft hpair) (ND.andRight hpair) hq' hi' hs'
#print axioms successorBothWitnesses
end M6.PA.NumericPAeqValueCoherence

