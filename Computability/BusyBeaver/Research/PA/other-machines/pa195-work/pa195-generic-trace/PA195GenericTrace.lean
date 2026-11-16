import Mathlib.Data.Int.Basic

/-! Generic standard-natural-number trace comparison for deterministic partial
machines. Positive-length forward simulation and source totality suffice for
halting equivalence. This is not an internal arithmetic theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 0
universe u v
namespace PA195GenericTrace

def run {A : Type u} (step : A → Option A) : Nat → A → Option A
  | 0, x => some x
  | n + 1, x => (step x).bind (run step n)

theorem run_add {A : Type u} (step : A → Option A) (m n : Nat) (x : A) :
    run step (m + n) x = (run step m x).bind (run step n) := by
  induction m generalizing x with
  | zero => simp [run]
  | succ m ih =>
    cases h : step x with
    | none => simp [Nat.succ_add, run, h]
    | some y => simpa [run, h, Nat.succ_add] using ih y

theorem run_stopped {A : Type u} (step : A → Option A) (x : A)
    (h : step x = none) (n : Nat) : run step (n + 1) x = none := by
  simp [run, h]

section Simulation
variable {A : Type u} {B : Type v}
variable (parent : A → Option A) (child : B → Option B)
variable (project : A → B) (inv : A → Prop)
variable (preserve : ∀ x y, inv x → parent x = some y → inv y)
variable (simulate : ∀ x y, inv x → parent x = some y →
  ∃ k, 0 < k ∧ run child k (project x) = some (project y))

include preserve simulate

/-- A parent run of length n is simulated by at least n child steps. -/
theorem simulate_run (n : Nat) (x y : A) (hi : inv x)
    (hp : run parent n x = some y) :
    ∃ k, n ≤ k ∧ run child k (project x) = some (project y) ∧ inv y := by
  induction n generalizing x with
  | zero =>
    simp only [run, Option.some.injEq] at hp
    subst y
    exact ⟨0, Nat.le_refl _, rfl, hi⟩
  | succ n ih =>
    cases hs : parent x with
    | none => simp [run, hs] at hp
    | some z =>
      have hrest : run parent n z = some y := by simpa [run, hs] using hp
      have hz : inv z := preserve x z hi hs
      obtain ⟨k, hk, hr⟩ := simulate x z hi hs
      obtain ⟨l, hl, ht, hy⟩ := ih z hz hrest
      refine ⟨k + l, ?_, ?_, hy⟩
      · omega
      · rw [run_add, hr]
        exact ht

end Simulation

theorem no_extension_past_halt {A : Type u} (step : A → Option A)
    (halt : A → Prop) (stuck : ∀ x, halt x → step x = none)
    (x z : A) (m n : Nat) (hm : run step m x = some z) (hz : halt z)
    (hn : m < n) : run step n x = none := by
  have hsub : n = m + (n - m) := by omega
  rw [hsub, run_add, hm]
  cases hdiff : n - m with
  | zero => omega
  | succ k =>
    simp [run_stopped step z (stuck z hz) k]

section Halting
variable {A : Type u} {B : Type v}
variable (parent : A → Option A) (child : B → Option B)
variable (project : A → B) (inv : A → Prop)
variable (pHalt : A → Prop) (cHalt : B → Prop)
variable (preserve : ∀ x y, inv x → parent x = some y → inv y)
variable (simulate : ∀ x y, inv x → parent x = some y →
  ∃ k, 0 < k ∧ run child k (project x) = some (project y))
variable (parentTotal : ∀ x, inv x → ¬pHalt x → ∃ y, parent x = some y)
variable (haltMaps : ∀ x, pHalt x → cHalt (project x))
variable (childStuck : ∀ y, cHalt y → child y = none)

def Halts {X : Type*} (step : X → Option X) (halt : X → Prop) (x : X) : Prop :=
  ∃ n y, run step n x = some y ∧ halt y

include preserve simulate parentTotal haltMaps childStuck

/-- Standard-Nat halting equivalence, conditional on the stated local
simulation, invariant, target-stuck, and source-totality hypotheses. -/
theorem halts_iff (x : A) (hi : inv x) :
    Halts parent pHalt x ↔ Halts child cHalt (project x) := by
  constructor
  · rintro ⟨n, y, hp, hy⟩
    obtain ⟨k, _, hc, _⟩ := simulate_run parent child project inv preserve simulate n x y hi hp
    exact ⟨k, project y, hc, haltMaps y hy⟩
  · intro hc
    by_contra hn
    have never : ∀ n y, run parent n x = some y → ¬pHalt y := by
      intro n y hr hy
      exact hn ⟨n, y, hr, hy⟩
    have extend (n : Nat) : ∃ y, run parent n x = some y ∧ inv y := by
      induction n with
      | zero => exact ⟨x, rfl, hi⟩
      | succ n ih =>
        obtain ⟨y, hr, hyv⟩ := ih
        obtain ⟨z, hz⟩ := parentTotal y hyv (never n y hr)
        refine ⟨z, ?_, preserve y z hyv hz⟩
        rw [run_add, hr]
        simp [run, hz]
    obtain ⟨m, z, hm, hz⟩ := hc
    obtain ⟨y, hy, hyi⟩ := extend (m + 1)
    obtain ⟨k, hk, hchild, _⟩ := simulate_run parent child project inv preserve simulate (m + 1) x y hi hy
    have hnone : run child k (project x) = none :=
      no_extension_past_halt child cHalt childStuck (project x) z m k hm hz (by omega)
    rw [hchild] at hnone
    contradiction
end Halting

#print axioms halts_iff
end PA195GenericTrace
