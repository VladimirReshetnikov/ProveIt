import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Order

/-!
# Invariants indexed by control labels

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15` and its later editions, Theorem
`thm:one-loop` ("One-loop normal form"), the invariant of the combined machine: "The combined invariant is
a finite conjunction indexed by control labels: `⋀_{ℓ<L} (pc = ℓ → I_ℓ(live registers))` … Since `L` is
fixed and every `I_ℓ` is QF, the conjunction is QF. … The step proof performs a finite case split on the
reflected value of `pc`, invokes the local preservation derivation for that command, and establishes the
invariant at the successor label."

The number `L` of labels is a metalevel number, as in the packet (the program is fixed), and the local
invariants are a family `I : ℕ → Fm`.

* `num_cases`: finite case analysis on a value below a numeral. From `p < L` and derivations of `φ` under
  each hypothesis `p = ℓ`, `ℓ < L`, a derivation of `φ`;
* `Labelled I pc L`: the formula `⋀_{ℓ<L} (pc = ℓ → I_ℓ)`; `labelled_QF`: it is quantifier-free when
  every `I_ℓ` is;
* `labelled_intro`, `labelled_at`: its introduction and elimination;
* `labelled_step`: the step rule. From `pc < L`, the labelled invariant, and for each label `ℓ` a local
  preservation derivation of `ψ` from `pc = ℓ` and `I_ℓ`, a derivation of `ψ` (in the application `ψ` is
  the labelled invariant of the successor state).

With `Foundations/TraceReflection` or `Foundations/GuardedTrace` this gives the base and step derivations
of the combined machine. The transformation of a structured program into one transition, its fuel and the
output projections are metalevel constructions and are not formalized here.
-/

namespace LeanProofs.IPRA.Foundations.LabelledInvariant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ}

/-- Finite case analysis on a value below the numeral `L`. -/
theorem num_cases {p : PTm n} {φ : Fm PTm n} (L : ℕ) :
    ∀ {Γ : List (Fm PTm n)}, (Γ ⊢[PRAAx] lt p (num L)) →
      (∀ ℓ, ℓ < L → (((p ≐ num ℓ) :: Γ) ⊢[PRAAx] φ)) → (Γ ⊢[PRAAx] φ) := by
  induction L with
  | zero =>
    intro Γ h _
    exact lt_zero_absurd φ h
  | succ L ih =>
    intro Γ h c
    have h' : Γ ⊢[PRAAx] lt p (succ (num L)) := h
    refine .orE (lt_succ_cases h') ?_ (c L (Nat.lt_succ_self L))
    exact ih Prf.hyp0 (fun ℓ hℓ =>
      (c ℓ (Nat.lt_succ_of_lt hℓ)).weaken (List.cons_subset_cons _ (List.subset_cons_self _ _)))

/-- `⋀_{ℓ<L} (pc = ℓ → I_ℓ)`. -/
def Labelled (I : ℕ → Fm PTm n) (pc : PTm n) : ℕ → Fm PTm n
  | 0 => (zero : PTm n) ≐ zero
  | L + 1 => Labelled I pc L ⋏ ((pc ≐ num L) ⟶ I L)

theorem labelled_QF {I : ℕ → Fm PTm n} {pc : PTm n} (hI : ∀ ℓ, (I ℓ).QF) :
    ∀ L, (Labelled I pc L).QF
  | 0 => trivial
  | L + 1 => ⟨labelled_QF hI L, trivial, hI L⟩

variable {Γ : List (Fm PTm n)} {I : ℕ → Fm PTm n} {pc : PTm n}

theorem labelled_intro :
    ∀ L, (∀ ℓ, ℓ < L → (((pc ≐ num ℓ) :: Γ) ⊢[PRAAx] I ℓ)) → (Γ ⊢[PRAAx] Labelled I pc L)
  | 0, _ => Prf.eqRefl zero
  | L + 1, c =>
    Prf.andI (labelled_intro L (fun ℓ hℓ => c ℓ (Nat.lt_succ_of_lt hℓ)))
      (Prf.impI (c L (Nat.lt_succ_self L)))

theorem labelled_at :
    ∀ (L ℓ : ℕ), ℓ < L → (Γ ⊢[PRAAx] Labelled I pc L) → (Γ ⊢[PRAAx] pc ≐ num ℓ) → (Γ ⊢[PRAAx] I ℓ)
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | L + 1, ℓ, h, hI, hp => by
    have hI' : Γ ⊢[PRAAx] Labelled I pc L ⋏ ((pc ≐ num L) ⟶ I L) := hI
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact labelled_at L ℓ h' (Prf.andE₁ hI') hp
    · exact Prf.impE (Prf.andE₂ hI') hp

/-- The step rule of the combined machine: case split on the program counter and invoke the local
preservation derivation of that label. -/
theorem labelled_step {ψ : Fm PTm n} (L : ℕ) (hpc : Γ ⊢[PRAAx] lt pc (num L))
    (hinv : Γ ⊢[PRAAx] Labelled I pc L)
    (hloc : ∀ ℓ, ℓ < L → ((I ℓ :: (pc ≐ num ℓ) :: Γ) ⊢[PRAAx] ψ)) : Γ ⊢[PRAAx] ψ :=
  num_cases L hpc (fun ℓ hℓ =>
    Prf.impE (Prf.impI (hloc ℓ hℓ)) (labelled_at L ℓ hℓ hinv.wk Prf.hyp0))

end LeanProofs.IPRA.Foundations.LabelledInvariant
