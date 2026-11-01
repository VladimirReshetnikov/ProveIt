import DiophantineConsistency.ParsonsGuard
/-! An explicit intermediate first-order calculus with the Σ₁ induction
rule, and Joosten's three-disjunction reduction as a proof transformer.
No conservation theorem or equivalence with PRA is asserted here. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {L : Language} [L.ORing]
def base (φ : Semiproposition L 1) : Proposition L := “!φ 0”
def step (φ : Semiproposition L 1) : Proposition L := “∀ x, !φ x → !φ (x + 1)”
/-- First-order proofs from closed base axioms with the Σ₁ induction rule.
Free variables are parameters; generalization uses Foundation's eigenvariable
shift, and specialization accepts arbitrary terms. -/
inductive Proof (T : Theory L) : Proposition L → Type
  | logical {φ} : Derivation [φ] → Proof T φ
  | axiom {σ : Sentence L} : σ ∈ T → Proof T (Rewriting.emb σ)
  | mp {φ ψ} : Proof T (φ 🡒 ψ) → Proof T φ → Proof T ψ
  | generalize {φ : Semiproposition L 1} : Proof T φ.free → Proof T (∀⁰ φ)
  | specialize {φ : Semiproposition L 1} (t : SyntacticTerm L) :
      Proof T (∀⁰ φ) → Proof T (φ/[t])
  | induction {φ : Semiproposition L 1} : Hierarchy 𝚺 1 φ →
      Proof T (base φ) → Proof T (step φ) → Proof T (∀⁰ φ)
omit [L.ORing] in
def resolution (P E : Proposition L) :
    Derivation [((P ⋎ E) 🡒 ((∼P ⋎ E) 🡒 E))] := by
  have h1 : Derivation [P, ∼P, E] := Derivation.close P (by simp) (by simp)
  have h2 : Derivation [∼E, ∼P, E] := Derivation.close E (by simp) (by simp)
  have h3 : Derivation [P ⋏ ∼E, ∼P, E] := h1.and h2
  have h4 : Derivation [∼P, P ⋏ ∼E, E] := h3.contra (by simp)
  have h5 : Derivation [∼E, P ⋏ ∼E, E] := Derivation.close E (by simp) (by simp)
  have h6 : Derivation [∼P ⋏ ∼E, P ⋏ ∼E, E] := h4.and h5
  have h7 : Derivation [P ⋏ ∼E, E, ∼P ⋏ ∼E] := h6.contra (by simp)
  have h8 : Derivation [(P ⋏ ∼E) ⋎ E, ∼P ⋏ ∼E] := h7.or
  have h9 : Derivation [∼P ⋏ ∼E, (P ⋏ ∼E) ⋎ E] := h8.contra (by simp)
  simpa [Semiformula.imp_eq] using h9.or
omit [L.ORing] in
def prop_step (P Q E : Proposition L) :
    Derivation [∼(P 🡒 Q), (P ⋎ E) 🡒 (Q ⋎ E)] := by
  have h1 : Derivation [∼P, P, Q, E] := Derivation.close P (by simp) (by simp)
  have h2 : Derivation [∼E, P, Q, E] := Derivation.close E (by simp) (by simp)
  have h3 : Derivation [∼P ⋏ ∼E, P, Q, E] := h1.and h2
  have h4 : Derivation [P, ∼P ⋏ ∼E, Q, E] := h3.contra (by simp)
  have h5 : Derivation [∼Q, ∼P ⋏ ∼E, Q, E] := Derivation.close Q (by simp) (by simp)
  have h6 : Derivation [P ⋏ ∼Q, ∼P ⋏ ∼E, Q, E] := h4.and h5
  have h7 : Derivation [Q, E, P ⋏ ∼Q, ∼P ⋏ ∼E] := h6.contra (by simp)
  have h8 : Derivation [∼P ⋏ ∼E, Q ⋎ E, P ⋏ ∼Q] := h7.or.contra (by simp)
  have h9 : Derivation [P ⋏ ∼Q, (∼P ⋏ ∼E) ⋎ (Q ⋎ E)] := h8.or.contra (by simp)
  simpa [Semiformula.imp_eq] using h9

def stepBody (φ : Semiproposition L 1) : Semiproposition L 1 :=
  “x. !φ x → !φ (x+1)”
theorem step_def (φ : Semiproposition L 1) : step φ = ∀⁰ (stepBody φ) := rfl

open ParsonsGuard

def succBody (φ : Semiproposition L 1) : Semiproposition L 1 := “x. !φ (x+1)”
theorem guard_step_free (φ : Semiproposition L 1) (E : Proposition L) :
    (stepBody (guard φ E)).free =
      ((φ.free ⋎ Rewriting.shift E) 🡒 ((succBody φ).free ⋎ Rewriting.shift E)) := by
  have h (v : Fin 1 → Semiterm L ℕ 1) :
      (Rew.subst v).comp Rew.bShift = Rew.bShift := by
    ext i
    · exact Fin.elim0 i
    · simp [Rew.comp_app]
  simp [stepBody, succBody, ParsonsGuard.guard, ← TransitiveRewriting.comp_app, h]

def guard_step_left (φ : Semiproposition L 1) (E : Proposition L) :
    Derivation [∼step φ, step (guard φ E)] := by
  have h : Derivation [∼(stepBody φ).free, (stepBody (guard φ E)).free] := by
    rw [guard_step_free]
    simpa [stepBody, succBody] using
      prop_step φ.free (succBody φ).free (Rewriting.shift E)
  have h0 : Derivation [(∼(Rewriting.shift (stepBody φ)))/[&0],
      (stepBody (guard φ E)).free] := by simpa using h
  have h1 : Derivation [∃⁰ ∼(Rewriting.shift (stepBody φ)),
      (stepBody (guard φ E)).free] := h0.exs
  have h2 : Derivation ((stepBody (guard φ E)).free :: [∼step φ]⁺) := by
    simpa [step_def, Rewriting.shifts] using h1.contra (Γ := [(stepBody (guard φ E)).free,
      ∃⁰ ∼(Rewriting.shift (stepBody φ))]) (by simp)
  have h3 := h2.all
  simpa [step_def] using h3.contra (Γ := [∼step φ, ∀⁰ (stepBody (guard φ E))]) (by simp)

def guard_step_right (φ : Semiproposition L 1) (E : Proposition L) :
    Derivation [∼E, step (guard φ E)] := by
  let P := φ.free
  let Q := (succBody φ).free
  let F := Rewriting.shift E
  have h1 : Derivation [Q, F, ∼P ⋏ ∼F, ∼F] := Derivation.close F (by simp) (by simp)
  have h2 : Derivation [∼P ⋏ ∼F, Q ⋎ F, ∼F] := h1.or.contra (by simp)
  have h3 : Derivation [(P ⋎ F) 🡒 (Q ⋎ F), ∼F] := by
    simpa [Semiformula.imp_eq] using h2.or
  have h4 : Derivation ((stepBody (guard φ E)).free :: [∼E]⁺) := by
    simpa [P, Q, F, guard_step_free, Rewriting.shifts] using h3
  have h5 := h4.all
  simpa [step_def] using h5.contra (Γ := [∼E, ∀⁰ (stepBody (guard φ E))]) (by simp)

/-- A pure LK derivation transports the original disjunctive step to the
guarded induction step. Its universal rule shifts all free parameters. -/
def guard_step_logic (φ : Semiproposition L 1) (E : Proposition L) :
    Derivation [(step φ ⋎ E) 🡒 step (guard φ E)] := by
  have h1 := guard_step_left φ E
  have h2 := guard_step_right φ E
  have h3 : Derivation [∼step φ ⋏ ∼E, step (guard φ E)] := h1.and h2
  simpa [Semiformula.imp_eq] using h3.or

def guard_result {T : Theory L} (φ : Semiproposition L 1) (E : Proposition L)
    (t : SyntacticTerm L) (hφ : Hierarchy 𝚺 1 φ) (hE : Hierarchy 𝚺 1 E)
    (hb : Proof T (base φ ⋎ E)) (hs : Proof T (step (guard φ E)))
    (hn : Proof T (∼(φ/[t]) ⋎ E)) : Proof T E := by
  have hb' : Proof T (base (guard φ E)) := by simpa [base] using hb
  have ha : Proof T (∀⁰ (guard φ E)) := .induction (guard_sigma φ E hφ hE) hb' hs
  have ht : Proof T (φ/[t] ⋎ E) := by simpa using (Proof.specialize t ha)
  exact .mp (.mp (.logical (resolution (φ/[t]) E)) ht) hn

/-- Joosten's guarded induction case, with arbitrary free parameters. -/
def three_disjunctions {T : Theory L} (φ : Semiproposition L 1) (E : Proposition L)
    (t : SyntacticTerm L) (hφ : Hierarchy 𝚺 1 φ) (hE : Hierarchy 𝚺 1 E)
    (hb : Proof T (base φ ⋎ E)) (hs : Proof T (step φ ⋎ E))
    (hn : Proof T (∼(φ/[t]) ⋎ E)) : Proof T E :=
  guard_result φ E t hφ hE hb (.mp (.logical (guard_step_logic φ E)) hs) hn

end DiophantineConsistency.ParsonsRule
