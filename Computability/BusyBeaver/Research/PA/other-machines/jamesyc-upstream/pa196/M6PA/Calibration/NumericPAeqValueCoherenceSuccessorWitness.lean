module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorAt
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T:InternalTheory V RelationalSource.language}
noncomputable def successorRightWitness {Γ:ND.Seq (V:=V)} (D P Q:SF (V:=V) 1) (S R:SF (V:=V) 2)
    (a r s:ST (V:=V) 0) (hp:ND.Proof (T:=T) Γ (unary (D ⋏ P) a))
    (har:ND.Proof (T:=T) Γ (binary S a r))
    (hq:ND.Proof (T:=T) Γ (successorOutput D (D ⋏ Q) S s))
    (hi:ND.Proof (T:=T) Γ (pairwise (D ⋏ P) (D ⋏ Q) R))
    (hs:ND.Proof (T:=T) Γ (successorRelation D S R)) : ND.Proof (T:=T) Γ (binary R r s) := by
  let body : SF (V:=V) 1 := unary (D ⋏ Q) (Semiterm.bvar 0) ⋏ binary S (Semiterm.bvar 0) s.bShift
  apply ND.exsElim (p:=body) (ND.andRight hq)
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hpair : ND.Proof (T:=T) C
      (unary (D.shift ⋏ Q.shift) (Semiterm.fvar 0) ⋏ binary S.shift (Semiterm.fvar 0) s.shift) := by
    simpa [body,Bootstrapping.Semiformula.free,SemitermVec.q,←Bootstrapping.Semiterm.bShift_shift_comm] using
      ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hp' : ND.Proof (T:=T) C (unary (D.shift ⋏ P.shift) a.shift) := by
    simpa [C] using ND.up (ND.shift hp) body.free
  have har' : ND.Proof (T:=T) C (binary S.shift a.shift r.shift) := by
    simpa [C] using ND.up (ND.shift har) body.free
  have hi' : ND.Proof (T:=T) C (pairwise (D.shift ⋏ P.shift) (D.shift ⋏ Q.shift) R.shift) := by
    simpa [C] using ND.up (ND.shift hi) body.free
  have hs' : ND.Proof (T:=T) C (successorRelation D.shift S.shift R.shift) := by
    simpa [C] using ND.up (ND.shift hs) body.free
  have hpa : ND.Proof (T:=T) C (unary D.shift a.shift ⋏ unary P.shift a.shift) := by simpa [unary] using hp'
  have hqb : ND.Proof (T:=T) C (unary D.shift (Semiterm.fvar 0) ⋏ unary Q.shift (Semiterm.fvar 0)) := by
    simpa [unary] using ND.andLeft hpair
  have hab := pairwiseAt (D.shift ⋏ P.shift) (D.shift ⋏ Q.shift) R.shift a.shift (Semiterm.fvar 0)
    hi' hp' (ND.andLeft hpair)
  simpa using successorRelationAt D.shift S.shift R.shift a.shift (Semiterm.fvar 0) r.shift s.shift
    hs' (ND.andLeft hpa) (ND.andLeft hqb) har' (ND.andRight hpair) hab
#print axioms successorRightWitness
end M6.PA.NumericPAeqValueCoherence

