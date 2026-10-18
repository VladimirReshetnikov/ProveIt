import BusyBeaver.ZFC.RuntimePerm252

/-!
Two deterministic binary machines may use different positive block clocks.
Matching checkpoint endpoints must agree on halting. These hypotheses alone
preserve halting: absorbing halt handles a run that halts inside a block.
No bound on either clock and no global choice of successive blocks is needed.
This generic lemma does not assert a concrete 244-state simulation.
-/
namespace SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation

open RuntimePerm252

/-- A whole-configuration relation at selected comparison boundaries. -/
structure Simulation {m n : Nat} (M : Machine m) (N : Machine n)
    (R : Config m → Config n → Prop) : Prop where
  halted : ∀ c d, R c d → (c.state = none ↔ d.state = none)
  block : ∀ c d, R c d → c.state ≠ none →
    ∃ i j, 0 < i ∧ 0 < j ∧ R (M.runFrom c i) (N.runFrom d j)

/-- Swapping the machines preserves the positive-block obligations. -/
theorem Simulation.symm {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (sim : Simulation M N R) :
    Simulation N M (fun d c => R c d) := by
  constructor
  · intro d c h
    exact (sim.halted c d h).symm
  · intro d c h hd
    have hc : c.state ≠ none := fun hn => hd ((sim.halted c d h).mp hn)
    obtain ⟨i, j, hi, hj, hr⟩ := sim.block c d h hc
    exact ⟨j, i, hj, hi, hr⟩

/-- Induction on an actual halting time transfers termination across blocks. -/
theorem forward {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (sim : Simulation M N R)
    (c : Config m) (d : Config n) (hr : R c d)
    (hh : BinaryHalts M c) : BinaryHalts N d := by
  obtain ⟨t, ht⟩ := hh
  induction t using Nat.strongRecOn generalizing c d with
  | ind t ih =>
    by_cases hc : c.state = none
    · exact ⟨0, (sim.halted c d hr).mp hc⟩
    · obtain ⟨i, j, hi, _hj, hnext⟩ := sim.block c d hr hc
      by_cases hend : (M.runFrom c i).state = none
      · exact ⟨j, (sim.halted _ _ hnext).mp hend⟩
      · have hit : i < t := active_before_halt M c i t hend ht
        have he : i + (t - i) = t := by omega
        have remaining : (M.runFrom (M.runFrom c i) (t - i)).state = none := by
          rw [← Machine.runFrom_add, he]
          exact ht
        obtain ⟨k, hk⟩ := ih (t - i) (by omega)
          (M.runFrom c i) (N.runFrom d j) hnext remaining
        exact ⟨j + k, by simpa only [Machine.runFrom_add] using hk⟩

/-- Positive clocks on both machines give both directions of halting equivalence. -/
theorem halts_iff {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (sim : Simulation M N R)
    (c : Config m) (d : Config n) (hr : R c d) :
    BinaryHalts M c ↔ BinaryHalts N d :=
  ⟨forward sim c d hr, forward sim.symm d c hr⟩

/-- Blank-tape specialization, with the initial checkpoint premise explicit. -/
theorem blank_halts_iff {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (sim : Simulation M N R)
    (hinit : R (initial m) (initial n)) :
    (∃ t, (M.run t).state = none) ↔ ∃ t, (N.run t).state = none := by
  have h := halts_iff sim (initial m) (initial n) hinit
  have hm (t : Nat) : M.runFrom (initial m) t = M.run t :=
    by simpa only [Nat.zero_add, Machine.run] using (M.run_add_eq_runFrom 0 t).symm
  have hn (t : Nat) : N.runFrom (initial n) t = N.run t :=
    by simpa only [Nat.zero_add, Machine.run] using (N.run_add_eq_runFrom 0 t).symm
  simpa only [BinaryHalts, hm, hn] using h

end SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation
