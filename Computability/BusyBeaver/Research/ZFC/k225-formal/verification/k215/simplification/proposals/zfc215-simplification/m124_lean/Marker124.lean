import Marker124Data

namespace Marker124

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

@[simp] theorem old124_false : oldTable 124 false = ⟨false, true, 62⟩ := rfl
@[simp] theorem old124_true : oldTable 124 true = ⟨true, true, 138⟩ := rfl
@[simp] theorem old127_false : oldTable 127 false = ⟨false, true, 14⟩ := rfl
@[simp] theorem old127_true : oldTable 127 true = ⟨true, true, 138⟩ := rfl
@[simp] theorem new124_false : newTable 124 false = ⟨false, false, 127⟩ := rfl
@[simp] theorem new124_true : newTable 124 true = ⟨true, true, 138⟩ := rfl
@[simp] theorem new127_false : newTable 127 false = ⟨false, true, 8⟩ := rfl
@[simp] theorem new127_true : newTable 127 true = ⟨true, true, 59⟩ := rfl
@[simp] theorem new8_false : newTable 8 false = ⟨false, true, 14⟩ := rfl
@[simp] theorem new59_false : newTable 59 false = ⟨false, true, 62⟩ := rfl

abbrev Tape := Int → Bool

def wrR (b : Bool) (t : Tape) : Tape :=
  fun i => if i + 1 = 0 then b else t (i + 1)

def wrL (b : Bool) (t : Tape) : Tape :=
  fun i => if i - 1 = 0 then b else t (i - 1)

@[simp] theorem wrL_here (b : Bool) (t : Tape) : wrL b t 0 = t (-1) := rfl
@[simp] theorem wrR_wrL_here (a b : Bool) (t : Tape) : wrR a (wrL b t) 0 = b := rfl

structure Config where
  q : Nat
  tape : Tape

def applyAct (a : Act) (t : Tape) : Config :=
  ⟨a.dest, if a.right then wrR a.write t else wrL a.write t⟩

def step (table : Nat → Bool → Act) (c : Config) : Config :=
  if c.q = 254 then c else applyAct (table c.q (c.tape 0)) c.tape

def embed (c : Config) : Config := ⟨phi c.q, c.tape⟩

def Inv (c : Config) : Prop := c.q < 303 ∧
  (c.q = 124 → c.tape (-1) = true) ∧
  (c.q = 127 → c.tape (-1) = false)

def Halt (c : Config) : Prop := c.q = 254

def run {C : Type} (f : C → C) : Nat → C → C
  | 0, c => c
  | n + 1, c => run f n (f c)

def Halts (table : Nat → Bool → Act) (c : Config) : Prop :=
  ∃ n, Halt (run (step table) n c)

/-- The total extension on unused native labels is never reached from start. -/
def Active (c : Config) : Prop := c.q ∈ workingLabels ∨ c.q = 254

theorem working_bound {q : Nat} (hq : q ∈ workingLabels) : q < 303 := by
  have h : workingLabels.all (fun q => decide (q < 303)) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp h) q hq)

theorem active_step (table : Nat → Bool → Act)
    (closure : ∀ (q : Fin 303) (b : Bool), q.val ∈ workingLabels →
      (table q.val b).dest ∈ workingLabels ∨ (table q.val b).dest = 254)
    (c : Config) (hc : Active c) : Active (step table c) := by
  by_cases hh : c.q = 254
  · simpa [step, hh] using hc
  · have hq : c.q ∈ workingLabels := hc.resolve_right hh
    have h := closure ⟨c.q, working_bound hq⟩ (c.tape 0) hq
    simpa only [Active, step, hh, if_false, applyAct] using h

theorem active_run (table : Nat → Bool → Act)
    (closure : ∀ (q : Fin 303) (b : Bool), q.val ∈ workingLabels →
      (table q.val b).dest ∈ workingLabels ∨ (table q.val b).dest = 254)
    (n : Nat) (c : Config) (hc : Active c) : Active (run (step table) n c) := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih => exact ih _ (active_step table closure c hc)

theorem old_reachable_states (n : Nat) (t : Tape) :
    Active (run (step oldTable) n ⟨0, t⟩) :=
  active_run oldTable old_label_closure n _ (Or.inl start_is_working)

theorem new_reachable_states (n : Nat) (t : Tape) :
    Active (run (step newTable) n ⟨0, t⟩) :=
  active_run newTable new_label_closure n _ (Or.inl start_is_working)

theorem run_add {C : Type} (f : C → C) (n m : Nat) (c : C) :
    run f (n + m) c = run f m (run f n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simpa only [Nat.succ_add, run] using ih (f c)

theorem halt_stable (table : Nat → Bool → Act) (c : Config) (h : Halt c) :
    Halt (step table c) := by
  change c.q = 254 at h
  simp [Halt, step, h]

theorem halt_run (table : Nat → Bool → Act) (c : Config) (h : Halt c) (n : Nat) :
    Halt (run (step table) n c) := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih => exact ih _ (halt_stable table c h)

theorem embed_halt (c : Config) : Halt (embed c) ↔ Halt c := by
  simp only [Halt, embed, phi]
  split <;> omega

theorem excursion (t : Tape) (m b : Bool) (hm : t (-1) = m) :
    wrR b (wrR m (wrL b t)) = wrR b t := by
  funext i
  by_cases h1 : i + 1 = 0
  · simp [wrR, h1]
  · by_cases h2 : i + 1 + 1 = 0
    · have hi : i + 1 = -1 := by omega
      simp [wrR, hi, hm]
    · have e : i + 1 + 1 - 1 = i + 1 := by omega
      simp [wrR, wrL, h1, h2, e]

theorem inv_step (c : Config) (hi : Inv c) : Inv (step oldTable c) := by
  by_cases hh : c.q = 254
  · simpa [step, hh] using hi
  · have hb := old_bounds ⟨c.q, hi.1⟩ (c.tape 0)
    refine ⟨by simpa [step, hh, applyAct] using hb, ?_, ?_⟩
    · intro hq
      have hdest : (oldTable c.q (c.tape 0)).dest = 124 := by
        simpa [step, hh, applyAct] using hq
      obtain ⟨hw, hr⟩ := incoming124 ⟨c.q, hi.1⟩ (c.tape 0) hdest
      simp [step, hh, applyAct, hw, hr, wrR]
    · intro hq
      have hdest : (oldTable c.q (c.tape 0)).dest = 127 := by
        simpa [step, hh, applyAct] using hq
      obtain ⟨hw, hr⟩ := incoming127 ⟨c.q, hi.1⟩ (c.tape 0) hdest
      simp [step, hh, applyAct, hw, hr, wrR]

theorem regular_step (c : Config) (hi : Inv c) (h124 : c.q ≠ 124)
    (h127 : c.q ≠ 127) : step newTable (embed c) = embed (step oldTable c) := by
  have hr := regular_rows ⟨c.q, hi.1⟩ (c.tape 0) h124 h127
  by_cases hh : c.q = 254
  · simp [step, embed, phi, hh]
  · have hphi : phi c.q = c.q := by simp [phi, h127]
    have hr' : newTable c.q (c.tape 0) = mapAct (oldTable c.q (c.tape 0)) := by
      simpa only [hphi] using hr
    simp only [step, embed, hphi, hh, if_false]
    rw [hr']
    rfl

theorem marker124_step (t : Tape) (hm : t (-1) = true) :
    ∃ d, (d = 1 ∨ d = 3) ∧
      run (step newTable) d (embed ⟨124, t⟩) = embed (step oldTable ⟨124, t⟩) := by
  cases hb : t 0 with
  | false =>
    refine ⟨3, Or.inr rfl, ?_⟩
    simp [run, step, embed, phi, applyAct, hb, hm, excursion t true false hm]
  | true =>
    refine ⟨1, Or.inl rfl, ?_⟩
    simp [run, step, embed, phi, hb, applyAct]

theorem marker127_step (t : Tape) (hm : t (-1) = false) :
    ∃ d, (d = 1 ∨ d = 3) ∧
      run (step newTable) d (embed ⟨127, t⟩) = embed (step oldTable ⟨127, t⟩) := by
  cases hb : t 0 with
  | false =>
    refine ⟨3, Or.inr rfl, ?_⟩
    simp [run, step, embed, phi, applyAct, hb, hm, excursion t false false hm]
  | true =>
    refine ⟨1, Or.inl rfl, ?_⟩
    simp [run, step, embed, phi, hb, applyAct]

theorem one_step (c : Config) (hi : Inv c) :
    ∃ d, (d = 1 ∨ d = 3) ∧
      run (step newTable) d (embed c) = embed (step oldTable c) := by
  by_cases h124 : c.q = 124
  · cases c with
    | mk q t =>
      dsimp at h124
      subst q
      exact marker124_step t (hi.2.1 rfl)
  · by_cases h127 : c.q = 127
    · cases c with
      | mk q t =>
        dsimp at h127
        subst q
        exact marker127_step t (hi.2.2 rfl)
    · exact ⟨1, Or.inl rfl, regular_step c hi h124 h127⟩

theorem simulate (n : Nat) (c : Config) (hi : Inv c) :
    ∃ k, n ≤ k ∧ k ≤ 3*n ∧
      run (step newTable) k (embed c) = embed (run (step oldTable) n c) := by
  induction n generalizing c with
  | zero => exact ⟨0, by omega, by omega, rfl⟩
  | succ n ih =>
    obtain ⟨d, hd, he⟩ := one_step c hi
    obtain ⟨k, hnk, hkn, hk⟩ := ih (step oldTable c) (inv_step c hi)
    refine ⟨d+k, by rcases hd with hd|hd <;> omega,
      by rcases hd with hd|hd <;> omega, ?_⟩
    rw [run_add, he, hk]
    rfl

theorem halts_iff (c : Config) (hi : Inv c) :
    Halts newTable (embed c) ↔ Halts oldTable c := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, hnk, _, he⟩ := simulate n c hi
    have hh := halt_run newTable (run (step newTable) n (embed c)) hn (k-n)
    rw [← run_add, Nat.add_sub_of_le hnk, he] at hh
    exact ⟨n, (embed_halt _).mp hh⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, _, _, he⟩ := simulate n c hi
    exact ⟨k, he ▸ (embed_halt _).mpr hn⟩

theorem all_tapes (t : Tape) :
    Halts newTable ⟨0, t⟩ ↔ Halts oldTable ⟨0, t⟩ := by
  exact halts_iff ⟨0, t⟩ ⟨by change 0 < 303; decide, by simp, by simp⟩

theorem blank_nonhalting :
    (¬ Halts newTable ⟨0, fun _ => false⟩) ↔
      (¬ Halts oldTable ⟨0, fun _ => false⟩) := not_congr (all_tapes _)

#print axioms all_tapes
#print axioms blank_nonhalting

end Marker124
