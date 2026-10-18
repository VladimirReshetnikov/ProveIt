import BusyBeaver.Core
import Lean.Elab.Tactic.Omega

/-!
Positive-segment simulation into the existing deterministic binary semantics.

This generic composition layer is intended for the permutation252 machine.
It is independent of the concrete instruction certificates and their frame
adapters. Every simulation obligation is an explicit premise. In particular,
an abstract failed step is not silently identified with a halt instruction:
the `stopped` obligation must establish the designated terminal predicate.

Positive segment lengths and Core's absorbing halted configurations prove
halting reflection without an unproved fairness or uniform clock assumption.
The finite abstract prefix lemma also bounds the accumulated binary clock
below by the number of abstract steps. No concrete252 runtime or consistency
claim is made until the obligations are instantiated with checked coverage.
-/

namespace SetTheory.BusyBeaver.ZFC.RuntimePerm252

universe u

def partialRun {A : Type u} (next : A → Option A) : Nat → A → Option A
  | 0, a => some a
  | k + 1, a => match next a with
    | none => none
    | some b => partialRun next k b

def AbstractHalts {A : Type u} (next : A → Option A) (terminal : A → Prop) (a : A) : Prop :=
  ∃ k b, partialRun next k a = some b ∧ terminal b

def BinaryHalts {states : Nat} (M : Machine states) (c : Config states) : Prop :=
  ∃ t, (M.runFrom c t).state = none

/-- All obligations needed for the eventual concrete runtime instance.
`next` returns the logical successor, while R includes the whole-tape frame
and any explicit decoder invariant needed by the instruction certificates. -/
structure PositiveSimulation {A : Type u} {states : Nat}
    (M : Machine states) (next : A → Option A) (terminal : A → Prop)
    (R : A → Config states → Prop) : Prop where
  active : ∀ a c, R a c → c.state ≠ none
  step : ∀ a b c, R a c → next a = some b →
    ∃ k, 0 < k ∧ R b (M.runFrom c k)
  stopped : ∀ a c, R a c → next a = none → terminal a
  halt : ∀ a c, R a c → terminal a → BinaryHalts M c

/-- Finite logical prefixes have actual binary endpoints, with at least one
binary step per logical operation. This is a finite induction, not Choice. -/
theorem prefix_run {A : Type u} {states : Nat} {M : Machine states}
    {next : A → Option A} {terminal : A → Prop} {R : A → Config states → Prop}
    (sim : PositiveSimulation M next terminal R)
    (N : Nat) (a b : A) (c : Config states) (hc : R a c)
    (hr : partialRun next N a = some b) :
    ∃ k, N ≤ k ∧ R b (M.runFrom c k) := by
  induction N generalizing a c with
  | zero =>
    simp only [partialRun, Option.some.injEq] at hr
    subst b
    exact ⟨0, Nat.le_refl 0, hc⟩
  | succ N ih =>
    cases hs : next a with
    | none => simp [partialRun, hs] at hr
    | some a' =>
      have hr' : partialRun next N a' = some b := by
        simpa only [partialRun, hs] using hr
      obtain ⟨k, hk, hnext⟩ := sim.step a a' c hc hs
      obtain ⟨j, hj, hend⟩ := ih a' (M.runFrom c k) hnext hr'
      refine ⟨k + j, by omega, ?_⟩
      simpa only [Machine.runFrom_add] using hend

theorem abstract_to_binary {A : Type u} {states : Nat} {M : Machine states}
    {next : A → Option A} {terminal : A → Prop} {R : A → Config states → Prop}
    (sim : PositiveSimulation M next terminal R)
    (a : A) (c : Config states) (hc : R a c)
    (hh : AbstractHalts next terminal a) : BinaryHalts M c := by
  obtain ⟨N, b, hr, ht⟩ := hh
  obtain ⟨k, _, hk⟩ := prefix_run sim N a b c hc hr
  obtain ⟨j, hj⟩ := sim.halt b (M.runFrom c k) hk ht
  exact ⟨k + j, by simpa only [Machine.runFrom_add] using hj⟩

/-- An active endpoint cannot lie at or beyond an earlier halting time.
This is the exact point where the existing Core absorbing-halt semantics is
used to rule out unobserved intermediate halting. -/
theorem active_before_halt {states : Nat} (M : Machine states) (c : Config states)
    (k t : Nat) (ha : (M.runFrom c k).state ≠ none)
    (hh : (M.runFrom c t).state = none) : k < t := by
  rcases Nat.lt_or_ge k t with hk | hle
  · exact hk
  · have he : t + (k - t) = k := by omega
    have hf := M.runFrom_of_halted (M.runFrom c t) hh (k - t)
    have hx : (M.runFrom c k).state = none := by
      rw [← he, Machine.runFrom_add, hf]
      exact hh
    exact False.elim (ha hx)

theorem binary_to_abstract {A : Type u} {states : Nat} {M : Machine states}
    {next : A → Option A} {terminal : A → Prop} {R : A → Config states → Prop}
    (sim : PositiveSimulation M next terminal R)
    (a : A) (c : Config states) (hc : R a c)
    (hh : BinaryHalts M c) : AbstractHalts next terminal a := by
  obtain ⟨t, ht⟩ := hh
  induction t using Nat.strongRecOn generalizing a c with
  | ind t ih =>
    cases hs : next a with
    | none => exact ⟨0, a, rfl, sim.stopped a c hc hs⟩
    | some a' =>
      obtain ⟨k, hk, hnext⟩ := sim.step a a' c hc hs
      have hkt : k < t := active_before_halt M c k t (sim.active a' _ hnext) ht
      have hsum : k + (t - k) = t := by omega
      have hremaining : (M.runFrom (M.runFrom c k) (t - k)).state = none := by
        rw [← Machine.runFrom_add, hsum]
        exact ht
      obtain ⟨N, b, hr, hb⟩ := ih (t - k) (by omega) a' (M.runFrom c k) hnext hremaining
      exact ⟨N + 1, b, by simpa only [partialRun, hs] using hr, hb⟩

theorem halts_iff {A : Type u} {states : Nat} {M : Machine states}
    {next : A → Option A} {terminal : A → Prop} {R : A → Config states → Prop}
    (sim : PositiveSimulation M next terminal R)
    (a : A) (c : Config states) (hc : R a c) :
    AbstractHalts next terminal a ↔ BinaryHalts M c :=
  ⟨abstract_to_binary sim a c hc, binary_to_abstract sim a c hc⟩

/-- Any fixed actual binary prefix can be added or removed when asking
whether the run eventually halts, even if it halts inside that prefix. -/
theorem binary_prefix_iff {states : Nat} (M : Machine states) (c : Config states) (N : Nat) :
    BinaryHalts M (M.runFrom c N) ↔ BinaryHalts M c := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨N + t, by simpa only [Machine.runFrom_add] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← Machine.runFrom_add, Nat.add_comm N t, Machine.runFrom_add,
      M.runFrom_of_halted (M.runFrom c t) ht N]
    exact ht

#print axioms prefix_run
#print axioms abstract_to_binary
#print axioms active_before_halt
#print axioms binary_to_abstract
#print axioms halts_iff
#print axioms binary_prefix_iff

end SetTheory.BusyBeaver.ZFC.RuntimePerm252

