import FiniteExtrema

/-!
# Uniform transfer for finite continuous formulas

A genuine checked formula-induction theorem in the Lean metatheory.  The
atomic interpretation is a fixed family supplied by the model.  This file
does not claim a primitive-recursive evaluator for arbitrary program codes.

All carrier ranges are `0, ..., last`, hence nonempty.  Values are natural
scores on a common positive denominator.  Complement is truncated; on the
intended score interval `0, ..., B` it is exactly `B - a`.

With max, min, complement, and finite inf/sup, an atomic error bound `e`
remains `e` for the entire formula: quantifier rank does not enlarge it.
-/

namespace QuantitativeIPRA.Continuous

open QuantitativeIPRA

universe u

inductive Formula (Atom : Nat → Type u) : Nat → Type u where
  | atom {n : Nat} (a : Atom n) : Formula Atom n
  | const {n : Nat} (c : Nat) : Formula Atom n
  | minimum {n : Nat} (p q : Formula Atom n) : Formula Atom n
  | maximum {n : Nat} (p q : Formula Atom n) : Formula Atom n
  | complement {n : Nat} (B : Nat) (p : Formula Atom n) : Formula Atom n
  | infimum {n : Nat} (p : Formula Atom (n + 1)) : Formula Atom n
  | supremum {n : Nat} (p : Formula Atom (n + 1)) : Formula Atom n

structure Model (Atom : Nat → Type u) where
  last : Nat
  atomic : {n : Nat} → Atom n → (Fin n → Nat) → Nat

def extend {n : Nat} (x : Nat) (ρ : Fin n → Nat) : Fin (n + 1) → Nat :=
  Fin.cases x ρ

def Valid {n : Nat} (last : Nat) (ρ : Fin n → Nat) : Prop := ∀ i, ρ i ≤ last

theorem valid_extend {n last x : Nat} {ρ : Fin n → Nat}
    (hρ : Valid last ρ) (hx : x ≤ last) : Valid last (extend x ρ) := by
  intro i
  exact Fin.cases hx (fun j => hρ j) i

theorem related_extend {n x y : Nat} {ρ σ : Fin n → Nat}
    (R : Nat → Nat → Prop) (hρ : ∀ i, R (ρ i) (σ i)) (hxy : R x y) :
    ∀ i, R (extend x ρ i) (extend y σ i) := by
  intro i
  exact Fin.cases hxy (fun j => hρ j) i

def eval {Atom : Nat → Type u} (M : Model Atom) :
    {n : Nat} → Formula Atom n → (Fin n → Nat) → Nat
  | _, .atom a, ρ => M.atomic a ρ
  | _, .const c, _ => c
  | _, .minimum p q, ρ => min (eval M p ρ) (eval M q ρ)
  | _, .maximum p q, ρ => max (eval M p ρ) (eval M q ρ)
  | _, .complement B p, ρ => B - eval M p ρ
  | _, .infimum p, ρ => minScore (fun i => eval M p (extend i ρ)) M.last
  | _, .supremum p, ρ => maxScore (fun i => eval M p (extend i ρ)) M.last

/-- Total relatedness of carrier points and uniform atomic distortion. -/
structure Correspondence {Atom : Nat → Type u}
    (A B : Model Atom) (R : Nat → Nat → Prop) (e : Nat) : Prop where
  total : TotalCorrespondence R A.last B.last
  atoms : ∀ {n : Nat} (a : Atom n) (ρ σ : Fin n → Nat),
    Valid A.last ρ → Valid B.last σ → (∀ i, R (ρ i) (σ i)) →
    Close e (A.atomic a ρ) (B.atomic a σ)

/-- Approximate elementarity for the finite continuous fragment.
    The SAME error bound works for every formula and every quantifier rank. -/
theorem formula_transfer {Atom : Nat → Type u} {A B : Model Atom}
    {R : Nat → Nat → Prop} {e n : Nat}
    (H : Correspondence A B R e) (φ : Formula Atom n)
    (ρ σ : Fin n → Nat) (hρ : Valid A.last ρ) (hσ : Valid B.last σ)
    (hR : ∀ i, R (ρ i) (σ i)) : Close e (eval A φ ρ) (eval B φ σ) := by
  induction φ with
  | atom a => exact H.atoms a ρ σ hρ hσ hR
  | const c => exact close_refl e c
  | minimum p q ihp ihq => exact close_min (ihp ρ σ hρ hσ hR) (ihq ρ σ hρ hσ hR)
  | maximum p q ihp ihq => exact close_max (ihp ρ σ hρ hσ hR) (ihq ρ σ hρ hσ hR)
  | complement C p ih => exact close_complement C (ih ρ σ hρ hσ hR)
  | infimum p ih =>
    apply min_correspondence _ _ A.last B.last e R H.total
    intro i hi j hj hij
    exact ih (extend i ρ) (extend j σ) (valid_extend hρ hi) (valid_extend hσ hj)
      (related_extend R hR hij)
  | supremum p ih =>
    apply max_correspondence _ _ A.last B.last e R H.total
    intro i hi j hj hij
    exact ih (extend i ρ) (extend j σ) (valid_extend hρ hi) (valid_extend hσ hj)
      (related_extend R hR hij)

end QuantitativeIPRA.Continuous
