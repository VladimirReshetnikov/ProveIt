import DiophantineConsistency.ParsonsInductionCase
import Foundation.FirstOrder.Hauptsatz
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsInductionCase
variable {L : Language}

def paired_lift (P Q : Proposition L) (d : Derivation [P, Q]) :
    Derivation [∀⁰ (Rew.fix ▹ P), ∃⁰ (Rew.fix ▹ Q)] := by
  have h0 : Derivation [((Rewriting.shift (Rew.fix ▹ Q))/[&0]), P] := by
    simpa using d.contra (Γ := [Q, P]) (by simp)
  have h1 : Derivation [∃⁰ Rewriting.shift (Rew.fix ▹ Q), P] := h0.exs
  have h2 : Derivation ((Rew.fix ▹ P).free :: [∃⁰ (Rew.fix ▹ Q)]⁺) := by
    simpa [Rewriting.shifts] using h1.contra
      (Γ := [P, ∃⁰ Rewriting.shift (Rew.fix ▹ Q)]) (by simp)
  exact h2.all

theorem fix_exsClosure {n : ℕ} (P : Semiformula L ℕ n) :
    (∃⁰ (Rew.fix ▹ (∃⁰* P))) = ∃⁰* (Rew.fix ▹ P) := by
  induction n with
  | zero => simp [exsClosure_succ]
  | succ n ih => simp [exsClosure_succ, ih]

theorem exsClosure_fixitr (P : Proposition L) (m : ℕ) :
    (∃⁰* Rew.fixitr 0 (m + 1) ▹ P) =
      ∃⁰ (Rew.fix ▹ (∃⁰* Rew.fixitr 0 m ▹ P)) := by
  simp [Rew.fixitr_succ, fix_exsClosure, TransitiveRewriting.comp_app]

def paired_closure (P Q : Proposition L) (d : Derivation [P, Q]) :
    (m : ℕ) → Derivation [∀⁰* Rew.fixitr 0 m ▹ P, ∃⁰* Rew.fixitr 0 m ▹ Q]
  | 0 => by simpa using d
  | m + 1 => by
    rw [LawfulSyntacticRewriting.allClosure_fixitr, exsClosure_fixitr]
    exact paired_lift _ _ (paired_closure P Q d m)

variable [L.ORing]

def normalizedCounterexample (φ : Semiproposition L 1) : Proposition L :=
    ∃⁰* Rew.fixitr 0 (succInd φ).fvSup ▹ (∃⁰ matrix φ)

/-- Closed induction axiom entails the normalized counterexample under its
negation. The finite parameter block is kept explicitly. -/
def closed_induction_normalization (φ : Semiproposition L 1) :
    Derivation [(succInd φ).univCl, normalizedCounterexample φ] := by
  simpa [Semiformula.univCl', normalizedCounterexample] using
    paired_closure (succInd φ) (∃⁰ matrix φ) (induction_normalization φ) (succInd φ).fvSup

/-- Replace a negative universally closed induction axiom by its normalized
counterexample before eliminating cuts. -/
def normalize_closed_context (φ : Semiproposition L 1) (Γ : Sequent L)
    (d : Derivation (∼((succInd φ).univCl : Proposition L) :: Γ)) :
    Derivation (normalizedCounterexample φ :: Γ) := by
  simpa using (closed_induction_normalization φ).cut d

/-- Normalize every induction axiom in a finite sequent, retaining the other
context unchanged, including repeated axioms. -/
def normalize_closed_list : (Φ : List (Semiproposition L 1)) →
    (Γ : Sequent L) →
    Derivation (Φ.map (fun φ ↦ ∼((succInd φ).univCl : Proposition L)) ++ Γ) →
    Derivation (Φ.map normalizedCounterexample ++ Γ)
  | [], Γ, d => by simpa using d
  | φ :: Φ, Γ, d => by
    have d₁ : Derivation (normalizedCounterexample φ ::
        (Φ.map (fun ψ ↦ ∼((succInd ψ).univCl : Proposition L)) ++ Γ)) :=
      normalize_closed_context φ _ d
    have d₂ : Derivation (Φ.map (fun ψ ↦ ∼((succInd ψ).univCl : Proposition L)) ++
        normalizedCounterexample φ :: Γ) := d₁.contra (by simp)
    have d₃ := normalize_closed_list Φ (normalizedCounterexample φ :: Γ) d₂
    exact d₃.contra (by simp)

/-- Normalize the finite list first, then cut-eliminate the resulting sequent. -/
noncomputable def normalized_cut_free [L.DecidableEq]
    (Φ : List (Semiproposition L 1)) (Γ : Sequent L)
    (d : Derivation (Φ.map (fun φ ↦ ∼((succInd φ).univCl : Proposition L)) ++ Γ)) :
    {e : Derivation (Φ.map normalizedCounterexample ++ Γ) // Derivation.IsCutFree e} :=
  Derivation.Canonical.hauptsatz (normalize_closed_list Φ Γ d)

end DiophantineConsistency.ParsonsClosure
