module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionEqualityElim
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] value orderIso Ordinal.domain equal

def realizedEqualityForwardAt {Γ : List Form} {n k : Nat}
    (t v : SourceTerm n) (σ : Rew Presentation.language Nat n Nat k)
    (A : SubstitutionPremises Γ) (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0)
    (Ht : TermRealization Γ σ b f c g t) (Hv : TermRealization Γ σ b f c g v)
    (x y : Term 0) (hx : ND.Proof Γ (value t c g x)) (hy : ND.Proof Γ (value v c g y))
    (h : ND.Proof Γ (equal (σ t) (σ v) b f)) : ND.Proof Γ (equal t v c g) := by
  apply equalityValueElim (σ t) (σ v) b f _ h
  let p := equalityWitness (σ t) (σ v) b f
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  let A' := A.shift.shift.up p
  have Ht' := TermRealization.up t (TermRealization.shift t (TermRealization.shift t Ht)) p
  have Hv' := TermRealization.up v (TermRealization.shift v (TermRealization.shift v Hv)) p
  have hx' : ND.Proof (p :: shifted (shifted Γ))
      (value t (freeShiftEnv (freeShiftEnv c)) (freeShiftEnv (freeShiftEnv g))
        (Rew.shift (Rew.shift x))) := by simpa only [value_shift] using up (shiftProof (shiftProof hx)) p
  have hy' : ND.Proof (p :: shifted (shifted Γ))
      (value v (freeShiftEnv (freeShiftEnv c)) (freeShiftEnv (freeShiftEnv g))
        (Rew.shift (Rew.shift y))) := by simpa only [value_shift] using up (shiftProof (shiftProof hy)) p
  have hi := realizedTermCompatible t σ A' _ _ _ _ Ht' _ _ (andLeft hp) hx'
  have hj := realizedTermCompatible v σ A' _ _ _ _ Hv' _ _ (andLeft (andRight hp)) hy'
  have hd := valueDomain _ _ _ _ (andLeft hp)
  have outIso := interpretedIsoTransitivity _ _ _ A'.transitivity
    (valueDomain _ _ _ _ hx') (substitutionIsoSymmetry A' _ _ hd hi)
    (interpretedIsoTransitivity _ _ _ A'.transitivity hd (andRight (andRight hp)) hj)
  have out := equalityValueIntro t v _ _ _ _ hx' hy' outIso
  convert out using 1 <;> interpretedWitnessSyntax

def realizedEqualityBackwardAt {Γ : List Form} {n k : Nat}
    (t v : SourceTerm n) (σ : Rew Presentation.language Nat n Nat k)
    (A : SubstitutionPremises Γ) (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0)
    (Ht : TermRealization Γ σ b f c g t) (Hv : TermRealization Γ σ b f c g v)
    (x y : Term 0) (hx : ND.Proof Γ (value (σ t) b f x)) (hy : ND.Proof Γ (value (σ v) b f y))
    (h : ND.Proof Γ (equal t v c g)) : ND.Proof Γ (equal (σ t) (σ v) b f) := by
  apply equalityValueElim t v c g _ h
  let p := equalityWitness t v c g
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  let A' := A.shift.shift.up p
  have Ht' := TermRealization.up t (TermRealization.shift t (TermRealization.shift t Ht)) p
  have Hv' := TermRealization.up v (TermRealization.shift v (TermRealization.shift v Hv)) p
  have hx' : ND.Proof (p :: shifted (shifted Γ))
      (value (σ t) (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f))
        (Rew.shift (Rew.shift x))) := by simpa only [value_shift] using up (shiftProof (shiftProof hx)) p
  have hy' : ND.Proof (p :: shifted (shifted Γ))
      (value (σ v) (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f))
        (Rew.shift (Rew.shift y))) := by simpa only [value_shift] using up (shiftProof (shiftProof hy)) p
  have hi := realizedTermCompatible t σ A' _ _ _ _ Ht' _ _ hx' (andLeft hp)
  have hj := realizedTermCompatible v σ A' _ _ _ _ Hv' _ _ hy' (andLeft (andRight hp))
  have hd := valueDomain _ _ _ _ hx'
  have outIso := interpretedIsoTransitivity _ _ _ A'.transitivity hd hi
    (interpretedIsoTransitivity _ _ _ A'.transitivity (valueDomain _ _ _ _ (andLeft hp))
      (andRight (andRight hp)) (substitutionIsoSymmetry A' _ _ (valueDomain _ _ _ _ hy') hj))
  have out := equalityValueIntro (σ t) (σ v) _ _ _ _ hx' hy' outIso
  convert out using 1 <;> interpretedWitnessSyntax

#print axioms realizedEqualityForwardAt
#print axioms realizedEqualityBackwardAt
end M6.PA.ForwardRelational
