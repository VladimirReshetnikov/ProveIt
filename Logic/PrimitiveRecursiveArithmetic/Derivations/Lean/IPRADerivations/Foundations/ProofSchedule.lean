import IPRADerivations.Core.Basic

/-!
# Kernel proof schedules

Packets (`docs/proofs/foundations`):

* `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`, `ipra_kifcr_framework_2026-11-16`:
  the definition "Kernel proof schedule" and Theorem `thm:schedule` ("Schedule compilation": every kernel
  proof schedule compiles to a derivation `Γ ⊢ φ`), "the object-proof core of the graph compiler";
* `darc_ipra_framework_2026-11-16`: Theorem `thm:acyclic-compile` ("Acyclic graph compilation": for every
  retained node `v_i`, `B ⊢ φ_{v_i}`).

A schedule for `φ` under a context `Γ` is a terminal derivation `Γ ⊢ φ`, or a derivation `Γ ⊢ ψ` followed
by a schedule for `φ` under `ψ :: Γ`.

* `Schedule Γ φ`: the inductive definition;
* `compile` (`thm:schedule`): `Schedule Γ φ` gives `Γ ⊢ φ`;
* `Steps Γ L`: the formulas of the list `L`, in topological order, each have a local derivation from `Γ`
  and the earlier members of `L`;
* `schedule_of_steps`: such a list followed by a terminal derivation from all of it is a schedule;
* `all_derivable` (`thm:acyclic-compile`): every member of such a list is derivable from `Γ` alone.

The elaboration of graphs into schedules (arity checking, topological sorting, register allocation) is a
metalevel task of the packets' compilers and is not formalized.
-/

namespace LeanProofs.IPRA.Foundations.ProofSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm

variable {n : ℕ}

/-- A kernel proof schedule for `φ` under `Γ`. -/
inductive Schedule : List (Fm PTm n) → Fm PTm n → Prop
  | done {Γ : List (Fm PTm n)} {φ : Fm PTm n} (h : Γ ⊢[PRAAx] φ) : Schedule Γ φ
  | step {Γ : List (Fm PTm n)} {ψ φ : Fm PTm n} (h : Γ ⊢[PRAAx] ψ) (rest : Schedule (ψ :: Γ) φ) :
      Schedule Γ φ

/-- `thm:schedule`: every kernel proof schedule compiles to a derivation. -/
theorem compile {Γ : List (Fm PTm n)} {φ : Fm PTm n} (s : Schedule Γ φ) : Γ ⊢[PRAAx] φ := by
  induction s with
  | done h => exact h
  | step h _ ih => exact .impE (.impI ih) h

/-- The members of `L`, in order, are each derivable from `Γ` and the earlier members. -/
def Steps : List (Fm PTm n) → List (Fm PTm n) → Prop
  | _, [] => True
  | Γ, ψ :: L => (Γ ⊢[PRAAx] ψ) ∧ Steps (ψ :: Γ) L

/-- A topologically ordered list of local rules followed by a terminal derivation is a schedule. -/
theorem schedule_of_steps : ∀ (L : List (Fm PTm n)) {Γ : List (Fm PTm n)} {φ : Fm PTm n},
    Steps Γ L → ((L.reverse ++ Γ) ⊢[PRAAx] φ) → Schedule Γ φ
  | [], _, _, _, h => .done (by simpa using h)
  | ψ :: L, Γ, φ, hs, h =>
    .step hs.1 (schedule_of_steps L hs.2 (by simpa [List.reverse_cons, List.append_assoc] using h))

/-- `thm:acyclic-compile`: every node formula of the list is derivable from the boundary context. -/
theorem all_derivable : ∀ (L : List (Fm PTm n)) {Γ : List (Fm PTm n)},
    Steps Γ L → ∀ χ ∈ L, Γ ⊢[PRAAx] χ
  | [], _, _, _, hχ => nomatch hχ
  | ψ :: L, Γ, hs, χ, hχ => by
    rcases List.mem_cons.mp hχ with rfl | h'
    · exact hs.1
    · exact .impE (.impI (all_derivable L hs.2 χ h')) hs.1

/-- The terminal formula of a list of local rules is derivable: the composite of the two statements. -/
theorem compile_steps (L : List (Fm PTm n)) {Γ : List (Fm PTm n)} {φ : Fm PTm n} (hs : Steps Γ L)
    (h : (L.reverse ++ Γ) ⊢[PRAAx] φ) : Γ ⊢[PRAAx] φ :=
  compile (schedule_of_steps L hs h)

end LeanProofs.IPRA.Foundations.ProofSchedule
