module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitution
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain Ordinal.successor value orderIso

def substitutionSuccessor {n : Nat} (t : SourceTerm (n+1))
    (ih : SubstitutionCompatible t) : SubstitutionCompatible (Presentation.succ t) := by
  intro u Γ A b f a Hu Ht ha r s hr hs
  have hsub : singleBoundSubst u (Presentation.succ t) =
      Presentation.succ (singleBoundSubst u t) := by
    simp only [Presentation.succ, singleBoundSubst_func]
    congr 1
    funext i
    fin_cases i
    rfl
  have hr' : ND.Proof Γ (value (Presentation.succ (singleBoundSubst u t)) b f r) := by
    simpa only [hsub] using hr
  apply successorValueElim (singleBoundSubst u t) b f r _ hr'
  let p := value (singleBoundSubst u t) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift r)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have hs' : ND.Proof (p :: shifted Γ)
      (value (Presentation.succ t) (freeShiftEnv (Fin.cases a b)) (freeShiftEnv f) (Rew.shift s)) := by
    simpa only [value_shift] using up (shiftProof hs) p
  apply successorValueElim t _ _ _ _ hs'
  let q := value t (freeShiftEnv (freeShiftEnv (Fin.cases a b)))
    (freeShiftEnv (freeShiftEnv f)) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift (Rew.shift s))
  have hq : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value (singleBoundSubst u t) (freeShiftEnv (freeShiftEnv b))
        (freeShiftEnv (freeShiftEnv f)) (.fvar 1) ⋏
        Ordinal.successor (.fvar 1) (Rew.shift (Rew.shift r))) := by
    convert up (shiftProof hp) q using 1 <;> (dsimp [p]; coherenceShiftSyntax; rfl)
  let A' := (A.shift.up p).shift.up q
  have Hu' := IsoCoverage.up u (IsoCoverage.shift u
    (IsoCoverage.up u (IsoCoverage.shift u Hu) p)) q
  have Ht' := IsoCoverage.up t (IsoCoverage.shift t
    (IsoCoverage.up t (IsoCoverage.shift t (Ht 0)) p)) q
  have ha' := up (shiftProof (up (shiftProof ha) p)) q
  have hi := ih u A' _ _ (Rew.shift (Rew.shift a)) Hu'
    (by simpa only [freeShiftEnv_cons] using Ht')
    (by simpa only [value_shift] using ha') (.fvar 1) (.fvar 0) (andLeft hp')
    (by simpa only [freeShiftEnv_cons] using andLeft hq)
  have out := successorIsoAt A' _ _ _ _
    (valueDomain _ _ _ _ (andLeft hp')) (valueDomain _ _ _ _ (andLeft hq))
    (andRight hp') (andRight hq) hi
  convert out using 1 <;> coherenceShiftSyntax

#print axioms substitutionSuccessor
end M6.PA.ForwardRelational
