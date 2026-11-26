import IPRADerivations.Core.Order
import IPRADerivations.Core.Header

/-! Imported from the packet `foundations/finite_observations_ipra_2026-11-20`, `lean/MetricKernel.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/- Actual derivations in the object theory. Row shapes are fixed by the proof
generator. All entries and the error may be arbitrary open object terms. -/
namespace LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel
open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Minimum, with positive common denominators cleared. -/
def meet (a b : PTm n) := monus a (monus a b)

theorem meet_left {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] meet a b ≐ a :=
  (congrMonus (.eqRefl a) h).eqTrans (monus_zero a)

theorem meet_right {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] meet a b ≐ b :=
  (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (add_monus _ _)

theorem meet_le_left (a b : PTm n) : Γ ⊢[PRAAx] le (meet a b) a :=
  .orE (le_total a b)
    (le_congr (meet_left Prf.hyp0).eqSymm (.eqRefl _) (le_refl a))
    (le_congr (meet_right Prf.hyp0).eqSymm (.eqRefl _) Prf.hyp0)

theorem meet_le_right (a b : PTm n) : Γ ⊢[PRAAx] le (meet a b) b :=
  .orE (le_total a b)
    (le_congr (meet_left Prf.hyp0).eqSymm (.eqRefl _) Prf.hyp0)
    (le_congr (meet_right Prf.hyp0).eqSymm (.eqRefl _) (le_refl b))

inductive Row (α : Type)
  | one (x : α)
  | cons (x : α) (tail : Row α)

namespace Row
def entries : Row α → List α
  | .one x => [x]
  | .cons x xs => x :: xs.entries

def value : Row (PTm n) → PTm n
  | .one x => x
  | .cons x xs => meet x xs.value

def someF (P : α → Fm PTm n) : Row α → Fm PTm n
  | .one x => P x
  | .cons x xs => P x ⋎ xs.someF P

def everyF (P : α → Fm PTm n) : Row α → Fm PTm n
  | .one x => P x
  | .cons x xs => P x ⋏ xs.everyF P

theorem some_elim {r : Row α} {P : α → Fm PTm n} {Q : Fm PTm n}
    (h : Γ ⊢[PRAAx] r.someF P)
    (f : ∀ x ∈ r.entries, P x :: Γ ⊢[PRAAx] Q) : Γ ⊢[PRAAx] Q := by
  induction r generalizing Γ with
  | one x => exact (f x (by simp [entries])).trans (fun _ hm => by
      rcases List.mem_cons.mp hm with e | e
      · subst_vars; exact h
      · exact .hyp e)
  | cons x xs ih =>
    refine .orE h (f x (by simp [entries])) (ih Prf.hyp0 ?_)
    intro y hy
    exact (f y (List.mem_cons_of_mem _ hy)).weaken (by
      intro φ hm
      rcases List.mem_cons.mp hm with e | e
      · subst_vars; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e))

theorem every_at {r : Row α} {P : α → Fm PTm n}
    (h : Γ ⊢[PRAAx] r.everyF P) {x : α} (hx : x ∈ r.entries) :
    Γ ⊢[PRAAx] P x := by
  induction r with
  | one y =>
    have e : x = y := by simpa [entries] using hx
    subst_vars; exact h
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with e | e
    · subst_vars; exact .andE₁ h
    · exact ih (.andE₂ h) e

theorem value_le {r : Row (PTm n)} {x : PTm n} (hx : x ∈ r.entries) :
    Γ ⊢[PRAAx] le r.value x := by
  induction r with
  | one y =>
    have e : x = y := by simpa [entries] using hx
    subst_vars; exact le_refl _
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with e | e
    · subst_vars; exact meet_le_left _ _
    · exact le_trans (meet_le_right _ _) (ih e)

/-- Lower bounds with a uniform rational error pass through a finite minimum. -/
theorem lower_shift {r : Row (PTm n)} {z e : PTm n}
    (h : ∀ x ∈ r.entries, Γ ⊢[PRAAx] le z (x + e)) :
    Γ ⊢[PRAAx] le z (r.value + e) := by
  induction r with
  | one x => exact h x (by simp [entries])
  | cons x xs ih =>
    have h₁ := h x (by simp [entries])
    have h₂ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact .orE (le_total x xs.value)
      (le_congr (.eqRefl _) (congrAdd (meet_left Prf.hyp0).eqSymm (.eqRefl e)) h₁.wk)
      (le_congr (.eqRefl _) (congrAdd (meet_right Prf.hyp0).eqSymm (.eqRefl e)) h₂.wk)

/-- A pointwise cover can choose its match by an object-level disjunction. -/
def cover (s r : Row (PTm n)) (e : PTm n) : Fm PTm n :=
  r.everyF (fun x => s.someF (fun y => le y (x + e)))

theorem cover_transfer (s r : Row (PTm n)) (e : PTm n) :
    Γ ⊢[PRAAx] cover s r e ⟶ le s.value (r.value + e) := by
  apply Prf.impI
  apply lower_shift
  intro x hx
  have h := every_at (r := r) (P := fun u => s.someF (fun y => le y (u + e)))
    (Γ := cover s r e :: Γ) Prf.hyp0 hx
  apply some_elim h
  intro y hy
  exact le_trans (value_le hy) Prf.hyp0

/-- The Yoneda probe row contains its diagonal and every alternative costs
at least that much. Its value is exactly the represented kernel entry. -/
theorem diagonal_exact (r : Row (PTm n)) (z : PTm n)
    (lower : ∀ x ∈ r.entries, Γ ⊢[PRAAx] le z x)
    (i : PTm n) (hi : i ∈ r.entries) (diag : Γ ⊢[PRAAx] i ≐ z) :
    Γ ⊢[PRAAx] r.value ≐ z := by
  apply LeanProofs.IPRA.le_antisymm
  · exact le_congr (.eqRefl _) diag (value_le hi)
  · have h := lower_shift (r := r) (e := zero) (fun x hx =>
        le_congr (.eqRefl _) (add_zero x).eqSymm (lower x hx))
    exact le_congr (.eqRefl _) (add_zero _) h

end Row
end LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel
