module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionAtomicWitnesses
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal Ordinal.domain PairGraph.orderIso

def realizedEqualityBackward {Γ : List Form} {n k : Nat}
    (t v : SourceTerm n) (σ : Rew Presentation.language Nat n Nat k)
    (A : SubstitutionPremises Γ) (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0)
    (Ht : TermRealization Γ σ b f c g t) (Hv : TermRealization Γ σ b f c g v)
    (h : ND.Proof Γ (equal t v c g)) : ND.Proof Γ (equal (σ t) (σ v) b f) := by
  apply valueElim (σ t) b f _ (termTotality A.totality (σ t) b f (TermRealization.imageCoverage t Ht))
  let p := value (σ t) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  let A1 := A.shift.up p
  have Hv1 := TermRealization.up v (TermRealization.shift v Hv) p
  apply valueElim (σ v) (freeShiftEnv b) (freeShiftEnv f) _
    (termTotality A1.totality (σ v) _ _ (TermRealization.imageCoverage v Hv1))
  let q := value (σ v) (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0)
  have hq : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value (σ t) (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1)) := by
    convert up (shiftProof hp) q using 1 <;> (dsimp [p]; coherenceShiftSyntax; rfl)
  let A2 := A1.shift.up q
  have Ht2 := TermRealization.up t (TermRealization.shift t
    (TermRealization.up t (TermRealization.shift t Ht) p)) q
  have Hv2 := TermRealization.up v (TermRealization.shift v Hv1) q
  have h2 : ND.Proof (q :: shifted (p :: shifted Γ))
      (equal t v (freeShiftEnv (freeShiftEnv c)) (freeShiftEnv (freeShiftEnv g))) := by
    convert up (shiftProof (up (shiftProof h) p)) q using 1 <;> interpretedWitnessSyntax
  have out := realizedEqualityBackwardAt t v σ A2 _ _ _ _ Ht2 Hv2 _ _ hp' hq h2
  convert out using 1 <;> interpretedWitnessSyntax

#print axioms realizedEqualityBackward
end M6.PA.ForwardRelational
