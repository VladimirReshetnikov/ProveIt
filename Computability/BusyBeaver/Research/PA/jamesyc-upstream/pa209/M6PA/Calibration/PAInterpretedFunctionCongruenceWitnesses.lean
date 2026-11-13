module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualityWitnesses
public import M6PA.Calibration.PAForwardRelationalCoherence
@[expose] public section

/-! Elimination of two actual value witnesses for fixed function-congruence
images. No representative is selected and equality remains order isomorphism. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def equalOfTotalValues {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (hs : ND.Proof Γ (hasValue s b f)) (ht : ND.Proof Γ (hasValue t b f))
    (hi : ND.Proof
      (value t (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0) ::
        shifted (value s (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) :: shifted Γ))
      (PairGraph.orderIso (.fvar 1) (.fvar 0))) : ND.Proof Γ (equal s t b f) := by
  apply valueElim s b f _ hs
  let p := value s (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  have ht' : ND.Proof (p :: shifted Γ)
      (hasValue t (freeShiftEnv b) (freeShiftEnv f)) := by
    simpa only [hasValue_shift] using up (shiftProof ht) p
  apply valueElim t _ _ _ ht'
  let q := value t (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0)
  have hs' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value s (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using up (shiftProof (assumption (Γ := p :: shifted Γ) (p := p) (by simp))) q
  have ht'' : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have out := equalityValueIntro s t _ _ (.fvar 1) (.fvar 0) hs' ht'' hi
  convert out using 1 <;> (dsimp [p,q,freeShiftEnv]; interpretedWitnessSyntax)

#print axioms equalOfTotalValues
end M6.PA.ForwardRelational
