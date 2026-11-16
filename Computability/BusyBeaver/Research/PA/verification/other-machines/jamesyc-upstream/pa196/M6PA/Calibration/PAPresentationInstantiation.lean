module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationND
public import M6PA.Calibration.PAPresentationRewriting
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! Uniform finite quantifier instantiation with arbitrary target terms.
These helpers retain actual LK proof data and do not invoke completeness. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder
abbrev GroundTerm := Semiterm language Nat 0

theorem rewrite_compose {n m k : Nat} (p : Semiproposition language n)
    (ω : Rew language Nat n Nat m) (τ : Rew language Nat m Nat k) :
    Semiformula.rewAux τ (Semiformula.rewAux ω p) = Semiformula.rewAux (τ.comp ω) p :=
  (TransitiveRewriting.comp_app ω τ p).symm

theorem q_bvar_one {n m : Nat} (ω : Rew language Nat (n+1) Nat m) :
    ω.q (.bvar 1) = Rew.bShift (ω (.bvar 0)) := Rew.q_bvar_succ ω 0

theorem q_bvar_two {n m : Nat} (ω : Rew language Nat (n+2) Nat m) :
    ω.q (.bvar 2) = Rew.bShift (ω (.bvar 1)) := Rew.q_bvar_succ ω 1

theorem q_bvar_three {n m : Nat} (ω : Rew language Nat (n+3) Nat m) :
    ω.q (.bvar 3) = Rew.bShift (ω (.bvar 2)) := Rew.q_bvar_succ ω 2

theorem twoSubstitutions (a b : GroundTerm) :
    (Rew.subst ![a]).comp (Rew.subst ![b]).q = Rew.subst ![a,b] := by
  apply Rew.ext
  · intro i; fin_cases i <;> simp [Rew.comp_app,q_bvar_one,q_bvar_two,q_bvar_three]
  · intro i; simp [Rew.comp_app]

theorem threeSubstitutions (a b c : GroundTerm) :
    ((Rew.subst ![a]).comp (Rew.subst ![b]).q).comp (Rew.subst ![c]).q.q =
      Rew.subst ![a,b,c] := by
  apply Rew.ext
  · intro i; fin_cases i <;> simp [Rew.comp_app,q_bvar_one,q_bvar_two,q_bvar_three]
  · intro i; simp [Rew.comp_app]

theorem fourSubstitutions (a b c d : GroundTerm) :
    (((Rew.subst ![a]).comp (Rew.subst ![b]).q).comp (Rew.subst ![c]).q.q).comp
      (Rew.subst ![d]).q.q.q = Rew.subst ![a,b,c,d] := by
  apply Rew.ext
  · intro i; fin_cases i <;> simp [Rew.comp_app,q_bvar_one,q_bvar_two,q_bvar_three]
  · intro i; simp [Rew.comp_app]

def ND.allElim2 {Γ : List ND.Form} (p : Semiproposition language 2) (a b : GroundTerm)
    (d : ND.Proof Γ (.all (.all p))) :
    ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a,b]) p) := by
  have h := ND.allElim _ a (ND.allElim _ b d)
  change ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a])
    (Semiformula.rewAux (Rew.subst ![b]).q p)) at h
  exact h.cast (by rw [rewrite_compose,twoSubstitutions])

def ND.allElim3 {Γ : List ND.Form} (p : Semiproposition language 3) (a b c : GroundTerm)
    (d : ND.Proof Γ (.all (.all (.all p)))) :
    ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a,b,c]) p) := by
  have h := ND.allElim _ a (ND.allElim _ b (ND.allElim _ c d))
  change ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a])
    (Semiformula.rewAux (Rew.subst ![b]).q (Semiformula.rewAux (Rew.subst ![c]).q.q p))) at h
  exact h.cast (by rw [rewrite_compose,rewrite_compose,threeSubstitutions])

def ND.allElim4 {Γ : List ND.Form} (p : Semiproposition language 4) (a b c d : GroundTerm)
    (h₀ : ND.Proof Γ (.all (.all (.all (.all p))))) :
    ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a,b,c,d]) p) := by
  have h := ND.allElim _ a (ND.allElim _ b (ND.allElim _ c (ND.allElim _ d h₀)))
  change ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a])
    (Semiformula.rewAux (Rew.subst ![b]).q (Semiformula.rewAux (Rew.subst ![c]).q.q
      (Semiformula.rewAux (Rew.subst ![d]).q.q.q p)))) at h
  exact h.cast (by rw [rewrite_compose,rewrite_compose,rewrite_compose,fourSubstitutions])

#print axioms ND.allElim4
end M6.PA.Presentation
