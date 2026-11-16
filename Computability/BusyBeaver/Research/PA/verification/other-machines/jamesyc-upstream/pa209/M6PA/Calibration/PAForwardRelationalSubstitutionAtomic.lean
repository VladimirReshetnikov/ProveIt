module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionAtomicForward
public import M6PA.Calibration.PAForwardRelationalSubstitutionAtomicBackward
public import M6PA.Calibration.PAForwardRelationalSubstitutionLift
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def termRealizationFromOccurrences {Γ : List Form} {n k : Nat} (t : SourceTerm n)
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0} {f : Nat → Term 0}
    {c : Fin n → Term 0} {g : Nat → Term 0}
    (H : ∀ v, TermOccurs v t → SubstitutionLeaf Γ (σ v.term) b f (v.lookup c g)) :
    TermRealization Γ σ b f c g t := by
  cases t with
  | bvar i => exact H (.inl i) .variable
  | fvar i => exact H (.inr i) .variable
  | func fn ts => exact fun i => termRealizationFromOccurrences (ts i) (fun v h => H v (.func i h))

/-- Atomic source-substitution compatibility is an actual ND biconditional,
with independent real witnesses on both sides and all domain guards retained. -/
def realizedEqualityIff {Γ : List Form} {n k : Nat}
    (t v : SourceTerm n) (σ : Rew Presentation.language Nat n Nat k)
    (A : SubstitutionPremises Γ) (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0)
    (Ht : TermRealization Γ σ b f c g t) (Hv : TermRealization Γ σ b f c g v) :
    ND.Proof Γ ((equal (σ t) (σ v) b f 🡒 equal t v c g) ⋏
      (equal t v c g 🡒 equal (σ t) (σ v) b f)) := by
  apply andIntro
  · apply impIntro
    exact realizedEqualityForward t v σ (A.up _) b f c g
      (TermRealization.up t Ht _) (TermRealization.up v Hv _) (assumption (by simp))
  · apply impIntro
    exact realizedEqualityBackward t v σ (A.up _) b f c g
      (TermRealization.up t Ht _) (TermRealization.up v Hv _) (assumption (by simp))

#print axioms termRealizationFromOccurrences
#print axioms realizedEqualityIff
end M6.PA.ForwardRelational
