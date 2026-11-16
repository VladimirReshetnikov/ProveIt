module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionAtomicWitnesses
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal Ordinal.domain PairGraph.orderIso

def realizedEqualityForward {Γ : List Form} {n k : Nat}
    (t v : SourceTerm n) (σ : Rew Presentation.language Nat n Nat k)
    (A : SubstitutionPremises Γ) (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0)
    (Ht : TermRealization Γ σ b f c g t) (Hv : TermRealization Γ σ b f c g v)
    (h : ND.Proof Γ (equal (σ t) (σ v) b f)) : ND.Proof Γ (equal t v c g) := by
  apply valueElim t c g _ (termTotality A.totality t c g (TermRealization.sourceCoverage t Ht))
  let p := value t (freeShiftEnv c) (freeShiftEnv g) (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  let A1 := A.shift.up p
  have Hv1 := TermRealization.up v (TermRealization.shift v Hv) p
  apply valueElim v (freeShiftEnv c) (freeShiftEnv g) _
    (termTotality A1.totality v _ _ (TermRealization.sourceCoverage v Hv1))
  let q := value v (freeShiftEnv (freeShiftEnv c)) (freeShiftEnv (freeShiftEnv g)) (.fvar 0)
  have hq : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value t (freeShiftEnv (freeShiftEnv c)) (freeShiftEnv (freeShiftEnv g)) (.fvar 1)) := by
    convert up (shiftProof hp) q using 1 <;> (dsimp [p]; coherenceShiftSyntax; rfl)
  let A2 := A1.shift.up q
  have Ht2 := TermRealization.up t (TermRealization.shift t
    (TermRealization.up t (TermRealization.shift t Ht) p)) q
  have Hv2 := TermRealization.up v (TermRealization.shift v Hv1) q
  have h2 : ND.Proof (q :: shifted (p :: shifted Γ))
      (equal (σ t) (σ v) (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f))) := by
    convert up (shiftProof (up (shiftProof h) p)) q using 1 <;> interpretedWitnessSyntax
  have out := realizedEqualityForwardAt t v σ A2 _ _ _ _ Ht2 Hv2 _ _ hp' hq h2
  convert out using 1 <;> interpretedWitnessSyntax

#print axioms realizedEqualityForward
end M6.PA.ForwardRelational
