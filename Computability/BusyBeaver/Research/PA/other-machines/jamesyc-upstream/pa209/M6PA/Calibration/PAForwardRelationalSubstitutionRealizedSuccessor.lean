module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionRealization
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain Ordinal.successor value orderIso

def realizedSuccessor {n : Nat} (t : SourceTerm n)
    (ih : RealizedTermCompatible t) : RealizedTermCompatible (Presentation.succ t) := by
  intro k σ Γ A b f c g H r s hr hs
  have hsub : σ (Presentation.succ t) = Presentation.succ (σ t) := by
    simp only [Presentation.succ, Rew.func, Function.comp_apply]
    congr 1
    funext i
    fin_cases i
    rfl
  have hr' : ND.Proof Γ (value (Presentation.succ (σ t)) b f r) := by simpa only [hsub] using hr
  apply successorValueElim (σ t) b f r _ hr'
  let p := value (σ t) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift r)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have hs' : ND.Proof (p :: shifted Γ)
      (value (Presentation.succ t) (freeShiftEnv c) (freeShiftEnv g) (Rew.shift s)) := by
    simpa only [value_shift] using up (shiftProof hs) p
  apply successorValueElim t _ _ _ _ hs'
  let q := value t (freeShiftEnv (freeShiftEnv c))
    (freeShiftEnv (freeShiftEnv g)) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift (Rew.shift s))
  have hq : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value (σ t) (freeShiftEnv (freeShiftEnv b))
        (freeShiftEnv (freeShiftEnv f)) (.fvar 1) ⋏
        Ordinal.successor (.fvar 1) (Rew.shift (Rew.shift r))) := by
    convert up (shiftProof hp) q using 1 <;> (dsimp [p]; coherenceShiftSyntax; rfl)
  let A' := (A.shift.up p).shift.up q
  have H' := TermRealization.up t (TermRealization.shift t
    (TermRealization.up t (TermRealization.shift t (H 0)) p)) q
  have hi := ih σ A' _ _ _ _ H' _ _ (andLeft hp') (andLeft hq)
  have out := successorIsoAt A'.coherence _ _ _ _
    (valueDomain _ _ _ _ (andLeft hp')) (valueDomain _ _ _ _ (andLeft hq))
    (andRight hp') (andRight hq) hi
  convert out using 1 <;> coherenceShiftSyntax

#print axioms realizedSuccessor
end M6.PA.ForwardRelational
