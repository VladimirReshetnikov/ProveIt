import BusyBeaver.ZFC.Enum254

/-!
Attributed port from intake 153, source 35, “Small Turing Machines for the
Consistency of ZFC: Source audit, formal scratch absorption, and certified
transition synthesis” (2026-10-16), supplied under MIT No Attribution.

Arrival: 4e720ccbbfaa836b95be3b2f3f268a737b48c6d1.
Preserved-source placement: 6135ffef4b.
Original ProveIt input: 426592ce97e52d309bfb8f0132411556650b7ac1.
Upstream literal program: jeff87654/busy-beaver,
297ab8df7e5de329605c3875b4934643b371a5e3, ZF/m254/coq/prog/Dag254.v.
Preserved source: SetTheory/Cardinals/docs/reports/set-theory/
zfc-closure-kernels/code/35-dirty-formal-src-BusyBeaver-ZFC-EnumSafeStart254.lean.
The published program is attributed to Mira-Cult, Jeff Ketchersid and
Andrew James Wade. The port retains the delivered theorem statements and
proofs; DirtyProgram254 supplies the separate current-tree composition.
-/

/-!
Tail universality for the exact six-register enumerator.

The ordinary argument was already recorded in ProveIt intake 144, source 09.
This file supplies a new Lean proof extending the zero-state endpoint of
`Enum254.lean`. It makes no binary-machine simulation or ZFC-calibration claim.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumSafeStart254

open Code254 Enum254

attribute [local irreducible] Code254.P

def HaltsFrom (s : St) : Prop :=
  ∃ n t, run n s = some t ∧ enumStep t = none

theorem sound_from {s : St} (hs : Inv s) : HaltsFrom s → C254 F := by
  rintro ⟨n, t, hr, hh⟩
  exact halt_step (run_inv n hs hr) hh

theorem halts_from_run {s t : St} (n : Nat) (hr : run n s = some t)
    (hh : HaltsFrom t) : HaltsFrom s := by
  obtain ⟨k, u, hrun, hhalt⟩ := hh
  exact ⟨n + k, u, by rw [run_add n k s t hr]; exact hrun, hhalt⟩

/-- Every later candidate is reached, unless an earlier command halts. -/
theorem reach_from (s : St) (hpl : s.pl = 0) : ∀ k : Nat,
    (∃ n t, run n s = some t ∧ t.pl = 0 ∧ t.np = s.np + k) ∨ HaltsFrom s
  | 0 => Or.inl ⟨0, s, rfl, hpl, by omega⟩
  | k + 1 => by
      rcases reach_from s hpl k with ⟨n, t, hr, ht, hn⟩ | hh
      · match hs : enumStep t with
        | none => exact Or.inr ⟨n, t, hr, hs⟩
        | some t1 =>
          have hn1 : t1.np = s.np + (k + 1) := by
            rw [step_start ht hs, hn]
            omega
          have hr1 : run (n + 1) s = some t1 := by
            rw [run_add n 1 s t hr]
            simp only [run, hs]
          rcases drain t1.pl t1 (Nat.le_refl _) with
              ⟨j, u, hru, hu, hnu⟩ | hh
          · exact Or.inl ⟨n + 1 + j, u,
              by rw [run_add (n + 1) j s t1 hr1]; exact hru,
              hu, hnu.trans hn1⟩
          · exact Or.inr (halts_from_run (n + 1) hr1 hh)
      · exact Or.inr hh

/-- The proof-list pointer itself need not initially be zero. -/
theorem reach_ge (s : St) (N : Nat) (hN : s.np ≤ N) :
    (∃ n t, run n s = some t ∧ t.pl = 0 ∧ t.np = N) ∨ HaltsFrom s := by
  rcases drain s.pl s (Nat.le_refl _) with ⟨n, t, hr, ht, hn⟩ | hh
  · rcases reach_from t ht (N - s.np) with ⟨j, u, hru, hu, hnu⟩ | hh
    · exact Or.inl ⟨n + j, u, by rw [run_add n j s t hr]; exact hru,
        hu, by rw [hn] at hnu; omega⟩
    · exact Or.inr (halts_from_run n hr hh)
  · exact Or.inr hh

theorem pad_code_ge (u : Nat) (cs : List Cmd) :
    u ≤ encL (.ax 0 1 1 u) cs := by
  cases cs with
  | nil =>
      change u ≤ P 3 (P 1 (P 1 (P u 0)))
      exact Nat.le_trans (le_P_left _ _) (Nat.le_trans (le_P_right _ _)
        (Nat.le_trans (le_P_right _ _) (le_P_right _ _)))
  | cons c cs =>
      change u ≤ P 3 (P 1 (P 1 (P u (encL c cs + 1))))
      exact Nat.le_trans (le_P_left _ _) (Nat.le_trans (le_P_right _ _)
        (Nat.le_trans (le_P_right _ _) (le_P_right _ _)))

/-- Padding the fourth AX field changes no reset guarantee. -/
theorem padded_program_halts {p : List Cmd} (hp : Contract p F) (u : Nat) (w : W) :
    cexec (.ax 0 1 1 u :: (p ++ [.drop 0, .nip 0, .nip 0])) w = none := by
  obtain ⟨t, S, d, hh⟩ := w
  rw [cexec_cons_some (cstep_ax 0 1 1 u t S d hh), cexec_append]
  rcases hp (gate (d + 1) (hh + 1) 0)
      (axStack (d + 1) hh (hh + 1) 0 u t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 F _ 0 0)]
    simp only [Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 0 _ 0 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    exact cexec_cons_none (cstep_nip_one 0 0 _ 0)

/-- A contradiction forces halting from every six-register state,
including states without the soundness invariant. -/
theorem complete_from (s : St) (h : C254 F) : HaltsFrom s := by
  obtain ⟨p, hp⟩ := build h
  let cs := p ++ [.drop 0, .nip 0, .nip 0]
  let N := encL (.ax 0 1 1 s.np) cs
  rcases reach_ge s N (pad_code_ge s.np cs) with ⟨n, t, hr, ht, hn⟩ | hh
  · have hf : (fetch t).1 = N := by simp [fetch, ht, hn]
    have hx : cexec (.ax 0 1 1 s.np :: cs) (toW t) = none :=
      padded_program_halts hp s.np (toW t)
    exact halts_from_run n hr (exec_list cs (.ax 0 1 1 s.np) t hf hx)
  · exact hh

/-- Exact tail universality, with all six starting fields quantified. -/
theorem safe_start_iff (s : St) (hs : Inv s) : HaltsFrom s ↔ C254 F :=
  ⟨sound_from hs, complete_from s⟩

/-- The three numerical control fields are completely unrestricted. -/
theorem zero_formula_start_iff (pl np d : Nat) :
    HaltsFrom ⟨pl, np, 0, 0, d, 0⟩ ↔ C254 F :=
  safe_start_iff _ ⟨C254.truth, C254.truth, good_zero⟩

#print axioms safe_start_iff
#print axioms complete_from
#print axioms pad_code_ge

end SetTheory.BusyBeaver.ZFC.EnumSafeStart254
