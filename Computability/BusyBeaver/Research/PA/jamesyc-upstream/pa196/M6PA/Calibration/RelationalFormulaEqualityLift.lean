module
public import M6PA.Theory
public import M6PA.Calibration.RelationalFormulaEquality
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! Capture-aware eigenvariable lifting of actual equality derivations.
The newly opened binder gets reflexivity; old names get shifted proofs. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder ND

def eigenRewrite {n : Nat} (ω : Rew language Nat n Nat 0) : Rew language Nat (n+1) Nat 0 :=
  Rew.free.comp ω.q

@[simp] theorem eigenRewrite_zero {n : Nat} (ω : Rew language Nat n Nat 0) :
    eigenRewrite ω (.bvar 0) = (.fvar 0 : GroundTerm) := by
  simp [eigenRewrite,Rew.comp_app]

@[simp] theorem eigenRewrite_succ {n : Nat} (ω : Rew language Nat n Nat 0) (i : Fin n) :
    eigenRewrite ω (.bvar i.succ) = Rew.shift (ω (.bvar i)) := by
  simp [eigenRewrite,Rew.comp_app]

@[simp] theorem eigenRewrite_fvar {n : Nat} (ω : Rew language Nat n Nat 0) (i : Nat) :
    eigenRewrite ω (.fvar i) = Rew.shift (ω (.fvar i)) := by
  simp [eigenRewrite,Rew.comp_app]

theorem eq_shift (a b : GroundTerm) : (eq a b).shift = eq (Rew.shift a) (Rew.shift b) :=
by
  change Semiformula.rel Relation.eq (Rew.shift ∘ ![a,b]) =
    Semiformula.rel Relation.eq ![Rew.shift a,Rew.shift b]
  apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 0) Relation.eq)
  funext i; fin_cases i <;> rfl

def ND.shiftEquality {Γ} {a b : GroundTerm} (h : ND.Proof Γ (eq a b)) :
    ND.Proof (ND.shifted Γ) (eq (Rew.shift a) (Rew.shift b)) :=
  (ND.shiftProof h).cast (by rw [eq_shift])

def liftedBoundEquality {Γ} {n : Nat} (E : FormulaEquality Γ)
    (ω τ : Rew language Nat n Nat 0)
    (hb : ∀ i : Fin n, ND.Proof Γ (eq (ω (.bvar i)) (τ (.bvar i)))) :
    ∀ i : Fin (n+1), ND.Proof (ND.shifted Γ)
      (eq (eigenRewrite ω (.bvar i)) (eigenRewrite τ (.bvar i))) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [eigenRewrite_zero] using E.shifted.reflexive (.fvar 0)
  · simpa only [eigenRewrite_succ] using ND.shiftEquality (hb j)

def liftedFreeEquality {Γ} {n : Nat}
    (ω τ : Rew language Nat n Nat 0)
    (hf : ∀ i : Nat, ND.Proof Γ (eq (ω (.fvar i)) (τ (.fvar i)))) :
    ∀ i : Nat, ND.Proof (ND.shifted Γ)
      (eq (eigenRewrite ω (.fvar i)) (eigenRewrite τ (.fvar i))) := by
  intro i
  simpa only [eigenRewrite_fvar] using ND.shiftEquality (hf i)

#print axioms liftedBoundEquality
end M6.PA.RelationalSource

