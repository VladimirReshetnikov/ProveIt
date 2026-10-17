import ParityCandidates254

/-!
The full original proof language with a stride-two candidate scheduler.

Attributed adaptation of Enum254.lean and EnumSafeStart254.lean at ProveIt
85633fd2f57b5dca16f87667699134d1b500ebc0.  The original published program is
attributed to Mira-Cult, Jeff Ketchersid and Andrew James Wade.  The supplied
source retains all original command semantics; only the outer scheduler's
increment changes from one to two.

The new parity-completeness theorem supplies a universally halting command
word in each candidate progression.  The resulting source endpoint is
HaltsFrom s iff Code254.C254 F for every s satisfying the original invariant.
There is no binary-machine transition table or physical-loader claim here.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumParity254

open Code254 Enum254

attribute [local irreducible] Code254.P

/-- New candidates advance by two; internal list fetches are unchanged. -/
def fetch (s : St) : Nat × Nat :=
  if s.pl = 0 then (s.np, s.np + 2) else (s.pl - 1, s.np)

def enumStep (s : St) : Option St := execAt (fetch s).1 (fetch s).2 s

def run : Nat → St → Option St
  | 0, s => some s
  | n + 1, s => match enumStep s with
    | some s' => run n s'
    | none => none

def HaltsFrom (s : St) : Prop :=
  ∃ n t, run n s = some t ∧ enumStep t = none

theorem step_inv {s s' : St} (hs : Inv s) (h : enumStep s = some s') : Inv s' := by
  obtain ⟨ht, hh, hw⟩ := hs
  unfold enumStep execAt at h
  generalize (fetch s).1 = pl1 at h
  generalize (fetch s).2 = np1 at h
  split at h
  · split at h
    · rename_i heq
      cases h
      refine ⟨?_, C254.truth, good_cons C254.truth hw⟩
      exact C254.mp ht (heq ▸ hh)
    · cases h
      exact ⟨C254.truth, C254.truth, hw⟩
  · cases h
    exact ⟨hh, hh, good_cons ht hw⟩
  · split at h
    · cases h
    · cases h
      exact ⟨ht, good_head hw, good_tail hw⟩
  · cases h
    exact ⟨gate_good _ _ _, C254.truth, axStack_good _ _ _ _ _ _ _ hh ht hw⟩

theorem halt_step {s : St} (hs : Inv s) (h : enumStep s = none) : C254 F := by
  obtain ⟨_, hh, _⟩ := hs
  unfold enumStep execAt at h
  generalize (fetch s).1 = pl1 at h
  generalize (fetch s).2 = np1 at h
  split at h
  · split at h <;> cases h
  · cases h
  · split at h
    · rename_i h1
      rw [h1] at hh
      exact hh
    · cases h
  · cases h

theorem run_inv : ∀ (n : Nat) {s s' : St}, Inv s → run n s = some s' → Inv s'
  | 0, s, s', hs, h => by cases h; exact hs
  | n + 1, s, s', hs, h => by
      unfold run at h
      split at h
      · rename_i s1 h1
        exact run_inv n (step_inv hs h1) h
      · cases h

theorem sound_from {s : St} (hs : Inv s) : HaltsFrom s → C254 F := by
  rintro ⟨n, t, hr, hh⟩
  exact halt_step (run_inv n hs hr) hh

theorem run_succ (n : Nat) (s s1 : St) (h : enumStep s = some s1) : run (n + 1) s = run n s1 := by
  simp only [run, h]

theorem run_add : ∀ (n m : Nat) (s s1 : St), run n s = some s1 → run (n + m) s = run m s1
  | 0, m, s, s1, h => by
      simp only [run] at h; cases h; simp
  | n + 1, m, s, s1, h => by
      simp only [run] at h
      split at h
      · rename_i s2 h2
        have := run_add n m s2 s1 h
        rw [show n + 1 + m = (n + m) + 1 by omega]
        simp only [run, h2]
        exact this
      · cases h

theorem halts_from_run {s t : St} (n : Nat) (hr : run n s = some t)
    (hh : HaltsFrom t) : HaltsFrom s := by
  obtain ⟨k, u, hrun, hhalt⟩ := hh
  exact ⟨n + k, u, by rw [run_add n k s t hr]; exact hrun, hhalt⟩

/-- List execution is independent of the stride between candidates. -/
theorem exec_list : ∀ (cs : List Cmd) (c : Cmd) (s : St), (fetch s).1 = encL c cs →
    cexec (c :: cs) (toW s) = none → HaltsFrom s
  | [], c, s, hf, hx => by
      refine ⟨0, s, rfl, ?_⟩
      unfold enumStep
      rw [hf, encL, execAt_pack]
      simp only [cexec] at hx
      cases hw : cstep c (toW s) with
      | none => rfl
      | some w => rw [hw] at hx; simp at hx
  | c' :: cs', c, s, hf, hx => by
      simp only [cexec] at hx
      split at hx
      · rename_i w hw
        let s1 : St := ⟨encL c' cs' + 1, (fetch s).2, w.tw, w.ws, w.d, w.h⟩
        have hstep : enumStep s = some s1 := by
          unfold enumStep
          rw [hf, encL, execAt_pack, hw]
        have hf1 : (fetch s1).1 = encL c' cs' := by
          simp [fetch, s1]
        obtain ⟨n, s', hr, hs'⟩ := exec_list cs' c' s1 hf1 hx
        exact ⟨n + 1, s', by rw [run_succ n s s1 hstep]; exact hr, hs'⟩
      · rename_i hw
        refine ⟨0, s, rfl, ?_⟩
        unfold enumStep
        rw [hf, encL, execAt_pack, hw]

theorem step_pl {s s1 : St} (hpl : s.pl ≠ 0) (h : enumStep s = some s1) :
    s1.pl < s.pl ∧ s1.np = s.np := by
  unfold enumStep fetch execAt at h
  simp only [hpl, if_false] at h
  have h1 := unP_le (s.pl - 1)
  have h2 := unP_le (unP (s.pl - 1)).2
  have h3 := unP_le (unP (unP (s.pl - 1)).2).2
  have h4 := unP_le (unP (unP (unP (s.pl - 1)).2).2).2
  split at h
  · split at h <;> (cases h; exact ⟨by simp only; omega, rfl⟩)
  · cases h; exact ⟨by simp only; omega, rfl⟩
  · split at h
    · cases h
    · cases h; exact ⟨by simp only; omega, rfl⟩
  · cases h; exact ⟨by simp only; omega, rfl⟩

theorem step_start {s s1 : St} (hpl : s.pl = 0) (h : enumStep s = some s1) :
    s1.np = s.np + 2 := by
  unfold enumStep fetch execAt at h
  simp only [hpl, if_true] at h
  split at h
  · split at h <;> (cases h; rfl)
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- A candidate in progress terminates or exhausts its finite list pointer. -/
theorem drain : ∀ (m : Nat) (s : St), s.pl ≤ m →
    (∃ n t, run n s = some t ∧ t.pl = 0 ∧ t.np = s.np) ∨ HaltsFrom s
  | m, s, hm => by
      by_cases hpl : s.pl = 0
      · exact Or.inl ⟨0, s, rfl, hpl, rfl⟩
      · match hs : enumStep s with
        | none => exact Or.inr ⟨0, s, rfl, hs⟩
        | some s1 =>
          obtain ⟨hlt, hnp⟩ := step_pl hpl hs
          cases m with
          | zero => omega
          | succ m =>
            rcases drain m s1 (by omega) with ⟨n, t, hr, h1, h2⟩ | ⟨n, t, hr, h1⟩
            · exact Or.inl ⟨n + 1, t, by rw [run_succ n s s1 hs]; exact hr, h1, h2.trans hnp⟩
            · exact Or.inr ⟨n + 1, t, by rw [run_succ n s s1 hs]; exact hr, h1⟩

/-- Every later member of the current parity progression is reached or the
enumerator has already halted. -/
theorem reach_from (s : St) (hpl : s.pl = 0) : ∀ k : Nat,
    (∃ n t, run n s = some t ∧ t.pl = 0 ∧ t.np = s.np + 2 * k) ∨ HaltsFrom s
  | 0 => Or.inl ⟨0, s, rfl, hpl, by omega⟩
  | k + 1 => by
      rcases reach_from s hpl k with ⟨n, t, hr, ht, hn⟩ | hh
      · match hs : enumStep t with
        | none => exact Or.inr ⟨n, t, hr, hs⟩
        | some t1 =>
          have hn1 : t1.np = s.np + 2 * (k + 1) := by
            rw [step_start ht hs, hn]
            omega
          have hr1 : run (n + 1) s = some t1 := by
            rw [run_add n 1 s t hr]
            simp only [run, hs]
          rcases drain t1.pl t1 (Nat.le_refl _) with ⟨j, u, hru, hu, hnu⟩ | hh
          · exact Or.inl ⟨n + 1 + j, u,
              by rw [run_add (n + 1) j s t1 hr1]; exact hru,
              hu, hnu.trans hn1⟩
          · exact Or.inr (halts_from_run (n + 1) hr1 hh)
      · exact Or.inr hh

/-- Initial internal list pointers and numerical accumulators are arbitrary. -/
theorem reach_progression (s : St) (k : Nat) :
    (∃ n t, run n s = some t ∧ t.pl = 0 ∧ t.np = s.np + 2 * k) ∨ HaltsFrom s := by
  rcases drain s.pl s (Nat.le_refl _) with ⟨n, t, hr, ht, hn⟩ | hh
  · rcases reach_from t ht k with ⟨j, u, hru, hu, hnu⟩ | hh
    · exact Or.inl ⟨n + j, u, by rw [run_add n j s t hr]; exact hru,
        hu, by rw [hn] at hnu; exact hnu⟩
    · exact Or.inr (halts_from_run n hr hh)
  · exact Or.inr hh

/-- A refutation forces this stride-two enumerator to halt from every state,
including states whose formula fields fail the soundness invariant. -/
theorem complete_from (s : St) (h : C254 F) : HaltsFrom s := by
  obtain ⟨c, cs, k, _, hk, hw⟩ :=
    ParityCandidates254.Original.cofinal_uniform_parity h s.np 0
  rcases reach_progression s k with ⟨n, t, hr, ht, hn⟩ | hh
  · have hf : (fetch t).1 = encL c cs := by simp [fetch, ht, hn, hk]
    exact halts_from_run n hr (exec_list cs c t hf (hw (toW t)))
  · exact hh

/-- Closed source endpoint for every sound starting state and either parity. -/
theorem safe_start_iff (s : St) (hs : Inv s) : HaltsFrom s ↔ C254 F :=
  ⟨sound_from hs, complete_from s⟩

theorem zero_formula_start_iff (pl np d : Nat) :
    HaltsFrom ⟨pl, np, 0, 0, d, 0⟩ ↔ C254 F :=
  safe_start_iff _ ⟨C254.truth, C254.truth, good_zero⟩

theorem halts_iff_original : HaltsFrom s0 ↔ Enum254.Halts :=
  (zero_formula_start_iff 0 0 0).trans Enum254.enum_halts_iff.symm

#print axioms safe_start_iff
#print axioms complete_from
#print axioms halts_iff_original

end SetTheory.BusyBeaver.ZFC.EnumParity254
