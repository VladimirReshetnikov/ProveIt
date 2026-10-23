import Init

/-!
A clock-free proof of termination transport for deterministic partial machines.

The finite-run API is deliberately the same elementary API used by KZip.  The
new reusable ingredient is induction on every reachable suffix of a terminating
run.  Neither the induction theorem nor simulation reflection uses subtraction,
inequalities, a global choice of blocks, or classical reasoning.

This is an implementation of the reachable-suffix idea proposed in ProveIt's
`simplification/proposals/further-interface/report.tex`, applied to the existing
positive-simulation interface.  It is not a new halting-equivalence principle.
-/

namespace TerminationTransport

universe u v
variable {A : Type u} {B : Type v}

def run (f : A → Option A) : Nat → A → Option A
  | 0, a => some a
  | n + 1, a => (f a).bind (run f n)

def Reach (f : A → Option A) (a b : A) : Prop := ∃ n, run f n a = some b
def Reach1 (f : A → Option A) (a b : A) : Prop := ∃ n, run f (n + 1) a = some b
def Halts (f : A → Option A) (a : A) : Prop :=
  ∃ n b, run f n a = some b ∧ f b = none

theorem Reach.refl (f : A → Option A) (a : A) : Reach f a a := ⟨0, rfl⟩

theorem Reach1.tail {f : A → Option A} {a b c : A}
    (h : f a = some b) (hr : Reach1 f a c) : Reach f b c := by
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, by simpa only [run, h, Option.bind_some] using hn⟩

theorem Reach1.not_stop {f : A → Option A} {a b : A}
    (h : f a = none) (hr : Reach1 f a b) : False := by
  obtain ⟨n, hn⟩ := hr
  simp only [run, h, Option.bind_none] at hn
  cases hn

theorem Halts.stop {f : A → Option A} {a : A} (h : f a = none) : Halts f a :=
  ⟨0, a, rfl, h⟩

theorem Halts.step {f : A → Option A} {a b : A}
    (h : f a = some b) (hh : Halts f b) : Halts f a := by
  obtain ⟨n, c, hr, hc⟩ := hh
  exact ⟨n + 1, c, by simp only [run, h, Option.bind_some]; exact hr, hc⟩

/-- Induct over the terminating run, exposing the induction hypothesis at all
reachable suffixes of the successor.  Determinism is provided by the function
`f`; `none` has no outgoing step. -/
theorem Halts.suffix_induction_all {f : A → Option A} {P : A → Prop}
    (stop : ∀ a, f a = none → P a)
    (step : ∀ a b, f a = some b → (∀ c, Reach f b c → P c) → P a)
    {a : A} (hh : Halts f a) : ∀ c, Reach f a c → P c := by
  obtain ⟨n, z, hr, hz⟩ := hh
  induction n generalizing a with
  | zero =>
      cases hr
      intro c hreach
      obtain ⟨m, hm⟩ := hreach
      cases m with
      | zero => cases hm; exact stop _ hz
      | succ m => simp only [run, hz, Option.bind_none] at hm; cases hm
  | succ n ih =>
      cases ha : f a with
      | none => simp only [run, ha, Option.bind_none] at hr; cases hr
      | some b =>
          have hr' : run f n b = some z := by
            simpa only [run, ha, Option.bind_some] using hr
          have hb := ih hr'
          intro c hreach
          obtain ⟨m, hm⟩ := hreach
          cases m with
          | zero => cases hm; exact step _ _ ha hb
          | succ m =>
              exact hb _ ⟨m, by simpa only [run, ha, Option.bind_some] using hm⟩

/-- The initial state is the reflexive suffix. -/
theorem Halts.suffix_induction {f : A → Option A} {P : A → Prop}
    (stop : ∀ a, f a = none → P a)
    (step : ∀ a b, f a = some b → (∀ c, Reach f b c → P c) → P a)
    {a : A} (hh : Halts f a) : P a :=
  suffix_induction_all stop step hh a (.refl f a)

/-- A terminating run remains terminating at every reachable configuration. -/
theorem Halts.at_reach {f : A → Option A} {a b : A}
    (hh : Halts f a) (hr : Reach f a b) : Halts f b :=
  suffix_induction_all (fun _ h => .stop h)
    (fun _ a' h ih => .step h (ih a' (.refl f a'))) hh b hr

theorem Halts.of_reach {f : A → Option A} {a b : A}
    (hr : Reach f a b) (hh : Halts f b) : Halts f a := by
  obtain ⟨n, hn⟩ := hr
  induction n generalizing a with
  | zero => cases hn; exact hh
  | succ n ih =>
      cases ha : f a with
      | none => simp only [run, ha, Option.bind_none] at hn; cases hn
      | some a' => exact .step ha (ih (by simpa only [run, ha, Option.bind_some] using hn))

/-- Positive forward simulation reflects termination.  No reverse simulation,
terminal compatibility, functional representation, or injectivity is needed
for this direction. -/
theorem reflects {f : A → Option A} {g : B → Option B} {R : A → B → Prop}
    (sim : ∀ {a a' b}, R a b → f a = some a' →
      ∃ b', R a' b' ∧ Reach1 g b b')
    {a : A} {b : B} (hab : R a b) (hh : Halts g b) : Halts f a := by
  apply Halts.suffix_induction (P := fun b => ∀ a, R a b → Halts f a) ?_ ?_ hh a hab
  · intro b hb a hab
    cases ha : f a with
    | none => exact .stop ha
    | some a' =>
        obtain ⟨b', _, hrun⟩ := sim hab ha
        exact False.elim (hrun.not_stop hb)
  · intro b b1 hb ih a hab
    cases ha : f a with
    | none => exact .stop ha
    | some a' =>
        obtain ⟨b', hab', hrun⟩ := sim hab ha
        exact .step ha (ih b' (hrun.tail hb) a' hab')

/-- Source terminals may drain through finitely many target transitions. -/
theorem halts_iff {f : A → Option A} {g : B → Option B} {R : A → B → Prop}
    (sim : ∀ {a a' b}, R a b → f a = some a' →
      ∃ b', R a' b' ∧ Reach1 g b b')
    (stop : ∀ {a b}, R a b → f a = none → Halts g b)
    {a : A} {b : B} (hab : R a b) : Halts f a ↔ Halts g b := by
  constructor
  · intro hh
    apply Halts.suffix_induction (P := fun a => ∀ b, R a b → Halts g b) ?_ ?_ hh b hab
    · intro a ha b hab; exact stop hab ha
    · intro a a' ha ih b hab
      obtain ⟨b', hab', n, hr⟩ := sim hab ha
      exact .of_reach ⟨n + 1, hr⟩ (ih a' (.refl f a') b' hab')
  · exact reflects sim hab

#print axioms Halts.suffix_induction
#print axioms reflects
#print axioms halts_iff

end TerminationTransport
