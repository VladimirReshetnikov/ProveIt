/-!
Reusable positive-stuttering simulation for deterministic transition systems.

This extracts the final argument of ProveIt's KSim.halts_iff from its
register-machine/tape-specific setting.  The only imported boundary is Init.
No theorem about K215 or its consistency calibration is assumed here.

Status: a proof script until the accompanying compiler receipt says PASS.
-/

namespace PositiveSimulation

universe u v
variable {A : Type u} {B : Type v}

def run (f : A → Option A) : Nat → A → Option A
  | 0, x => some x
  | n + 1, x => match f x with
    | none => none
    | some y => run f n y

@[simp] theorem run_one (f : A → Option A) (x : A) : run f 1 x = f x := by
  simp only [run]
  cases f x <;> rfl

def Reach (f : A → Option A) (x y : A) : Prop :=
  ∃ n, run f n x = some y

def Reach1 (f : A → Option A) (x y : A) : Prop :=
  ∃ n, run f (n + 1) x = some y

def Halts (f : A → Option A) (x : A) : Prop :=
  ∃ n y, run f n x = some y ∧ f y = none

theorem run_add (f : A → Option A) (a b : Nat) (x : A) :
    run f (a + b) x =
      match run f a x with | none => none | some y => run f b y := by
  induction a generalizing x with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [run]
      cases f x with
      | none => rfl
      | some y => exact ih y

theorem Halts.of_reach {f : A → Option A} {x y : A}
    (hr : Reach f x y) (hh : Halts f y) : Halts f x := by
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, z, hj, hz⟩ := hh
  exact ⟨i + j, z, by rw [run_add, hi]; exact hj, hz⟩

/-- A single forward simulation is enough for halting equivalence when
every source step takes a strictly positive number of target steps.
Reachability invariants can be conjoined into R; R need not be functional
or injective. A terminal source may take finitely many final target steps. -/
theorem halts_iff
    {f : A → Option A} {g : B → Option B} {R : A → B → Prop}
    (sim : ∀ {x x' y}, R x y → f x = some x' →
      ∃ y', R x' y' ∧ Reach1 g y y')
    (stop : ∀ {x y}, R x y → f x = none → Halts g y)
    {x : A} {y : B} (hR : R x y) : Halts f x ↔ Halts g y := by
  constructor
  · rintro ⟨n, xf, hr, hs⟩
    induction n generalizing x y with
    | zero =>
        simp only [run, Option.some.injEq] at hr
        subst hr
        exact stop hR hs
    | succ n ih =>
        simp only [run] at hr
        cases hx : f x with
        | none => rw [hx] at hr; cases hr
        | some x1 =>
            rw [hx] at hr
            obtain ⟨y1, h1, j, hj⟩ := sim hR hx
            exact Halts.of_reach ⟨j + 1, hj⟩ (ih h1 hr)
  · rintro ⟨t, yf, ht, hstop⟩
    induction t using Nat.strongRecOn generalizing x y with
    | ind t ih =>
        cases hx : f x with
        | none => exact ⟨0, x, rfl, hx⟩
        | some x1 =>
            obtain ⟨y1, h1, j, hj⟩ := sim hR hx
            have hle : j + 1 ≤ t := by
              refine Nat.not_lt.mp fun hlt => ?_
              have e1 : j + 1 = t + (j + 1 - t) := by omega
              rw [e1, run_add, ht] at hj
              obtain ⟨m, hm⟩ : ∃ m, j + 1 - t = m + 1 := ⟨j - t, by omega⟩
              rw [hm] at hj
              simp [run, hstop] at hj
            have e2 : t = (j + 1) + (t - (j + 1)) := by omega
            rw [e2, run_add, hj] at ht
            obtain ⟨n, xf, hr, hs⟩ := ih (t - (j + 1)) (by omega) h1 ht
            exact ⟨n + 1, xf, by simp only [run, hx]; exact hr, hs⟩

#print axioms halts_iff

end PositiveSimulation
