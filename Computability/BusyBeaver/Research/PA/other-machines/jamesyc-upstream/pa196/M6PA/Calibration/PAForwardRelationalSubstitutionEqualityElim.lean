module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionRealizedTerms
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] value orderIso Ordinal.domain

def equalityWitness {n : Nat} (t v : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) : Form :=
  value t (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1) ⋏
    (value v (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0) ⋏
      orderIso (.fvar 1) (.fvar 0))

def equalityValueElim {Γ : List Form} {n : Nat} (t v : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (q : Form)
    (h : ND.Proof Γ (equal t v b f))
    (k : ND.Proof (equalityWitness t v b f :: shifted (shifted Γ)) q.shift.shift) :
    ND.Proof Γ q := by
  apply exsElim h
  apply exsElim (assumption (List.mem_cons_self))
  have kk := weaken k (Δ := equalityWitness t v b f ::
    shifted (equalityPayload t v (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) :: shifted Γ)) (by
      intro p hp
      simp only [shifted, List.map_cons, List.mem_cons] at hp ⊢
      exact hp.elim Or.inl (fun h => Or.inr (Or.inr h)))
  convert kk using 1 <;>
    (simp only [equalityWitness, equalityPayload]; interpretedWitnessSyntax)
  all_goals first | exact ⟨⟨rfl,rfl⟩,rfl⟩ | rfl

def substitutionIsoSymmetry {Γ : List Form} (A : SubstitutionPremises Γ)
    (x y : Term 0) (hx : ND.Proof Γ (Ordinal.domain x))
    (h : ND.Proof Γ (orderIso x y)) : ND.Proof Γ (orderIso y x) := by
  obtain ⟨x,rfl⟩ := groundName x
  obtain ⟨y,rfl⟩ := groundName y
  exact isoSymmetryClosedAt x y A.symmetry hx h

#print axioms equalityValueElim
#print axioms substitutionIsoSymmetry
end M6.PA.ForwardRelational
