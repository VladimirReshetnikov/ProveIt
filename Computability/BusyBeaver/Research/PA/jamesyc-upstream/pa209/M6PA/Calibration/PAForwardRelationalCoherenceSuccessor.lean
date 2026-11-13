module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherenceWitnesses
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain Ordinal.successor value orderIso

macro "coherenceShiftSyntax" : tactic => `(tactic|
  simp only [value_shift,Semiformula.shift,Rewriting.shift,app_eq_rewAux,
    Semiformula.rewAux,Ordinal.successor_rew,Ordinal.domain_rew,
    orderIso_rew,BinaryOperation.result_rew,value_rew,Rew.shift_fvar])

def successorIsoAt {Γ : List Form} (A : CoherencePremises Γ)
    (x y r s : Term 0)
    (hx : ND.Proof Γ (Ordinal.domain x)) (hy : ND.Proof Γ (Ordinal.domain y))
    (hr : ND.Proof Γ (Ordinal.successor x r))
    (hs : ND.Proof Γ (Ordinal.successor y s))
    (hi : ND.Proof Γ (orderIso x y)) : ND.Proof Γ (orderIso r s) := by
  obtain ⟨x,rfl⟩ := groundName x
  obtain ⟨y,rfl⟩ := groundName y
  obtain ⟨r,rfl⟩ := groundName r
  obtain ⟨s,rfl⟩ := groundName s
  exact orderIsoSuccessor A.equality x y r s A.empty A.adjunction hx hy hr hs hi

def successorValuesCoherent {n : Nat} (t : SourceTerm n) (ih : ValuesCoherent t) :
    ValuesCoherent (Presentation.succ t) := by
  intro Γ A b b' f f' H r s hr hs
  apply successorValueElim t b f r _ hr
  let p := value t (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift r)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have hs' : ND.Proof (p :: shifted Γ)
      (value (Presentation.succ t) (freeShiftEnv b') (freeShiftEnv f') (Rew.shift s)) := by
    simpa only [value_shift] using up (shiftProof hs) p
  apply successorValueElim t _ _ _ _ hs'
  let q := value t (freeShiftEnv (freeShiftEnv b')) (freeShiftEnv (freeShiftEnv f')) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift (Rew.shift s))
  have hq : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value t (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1) ⋏
        Ordinal.successor (.fvar 1) (Rew.shift (Rew.shift r))) := by
    convert up (shiftProof hp) q using 1 <;> (dsimp [p]; coherenceShiftSyntax; rfl)
  let A' := (A.shift.up p).shift.up q
  have hc := IsoCoverage.up t (IsoCoverage.shift t
    (IsoCoverage.up t (IsoCoverage.shift t (H 0)) p)) q
  have hi := ih A' _ _ _ _ hc _ _ (andLeft hp') (andLeft hq)
  have out := successorIsoAt A' _ _ _ _
    (valueDomain t _ _ _ (andLeft hp')) (valueDomain t _ _ _ (andLeft hq))
    (andRight hp') (andRight hq) hi
  convert out using 1 <;> coherenceShiftSyntax

#print axioms successorIsoAt
#print axioms successorValuesCoherent
end M6.PA.ForwardRelational
