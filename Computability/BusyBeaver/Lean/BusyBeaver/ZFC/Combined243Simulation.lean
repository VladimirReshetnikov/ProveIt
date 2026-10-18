import BusyBeaver.ZFC.PositiveBlockBisimulation
import BusyBeaver.ZFC.Rotation244Invariant
import BusyBeaver.ZFC.Combined243Blocks

/-!
Concrete positive-block simulation of Combined243 against Rotation244.
Source-only mechanical port of the checked compensated244 simulation.
The relation retains the old-side local tape invariant and excludes old92
from paired endpoints; old122 is absent from the new state set.
The imported generic PositiveBlockBisimulation remains unchanged.
Results concern arbitrary finite-support Core tapes, including blank.
No calibration of Rotation244, completed kernel proof, or PA endpoint is claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.Combined243Simulation

open Combined243Blocks Rotation244Invariant RuntimePerm252

/-- Full configuration equality after state embedding, with the checkpoint facts. -/
def Related (c : Config 244) (d : Config 243) : Prop :=
  c = embedConfig243 d ∧ Holds c ∧ d.state ≠ some (oldStateCombined243 92)

private theorem endpoint_distinct :
    oldStateCombined243 25 ≠ oldStateCombined243 92 ∧
    oldStateCombined243 66 ≠ oldStateCombined243 92 ∧
    oldStateCombined243 24 ≠ oldStateCombined243 92 ∧
    oldStateCombined243 107 ≠ oldStateCombined243 92 ∧
    oldStateCombined243 2 ≠ oldStateCombined243 92 := by decide +kernel

private theorem ordinary_step (q : Fin 243) (h : Int) (t : Tape)
    (hq : q ≠ oldStateCombined243 92)
    (he : ¬ exceptionalRow243 q (Tape.read t h)) :
    embedConfig243 (machineCombined243.step ⟨some q, h, t⟩) =
      machineRotation244.step (embedConfig243 ⟨some q, h, t⟩) := by
  simp only [Machine.step, embedConfig243, Option.map_some]
  rw [← combined243_common_action q (Tape.read t h) hq he]
  rfl

private theorem pair_of_block {c : Config 244} {d : Config 243} {i j : Nat}
    (hi : Holds c)
    (he : embedConfig243 (machineCombined243.runFrom d j) = machineRotation244.runFrom c i)
    (hn : (machineCombined243.runFrom d j).state ≠ some (oldStateCombined243 92)) :
    Related (machineRotation244.runFrom c i) (machineCombined243.runFrom d j) :=
  ⟨he.symm, runFrom_holds c hi i, hn⟩

private theorem checkpoint_of_endpoint {d : Config 243} {j q : Nat} {h : Int} {t : Tape}
    (he : machineCombined243.runFrom d j = cfgNew q h t)
    (hq : oldStateCombined243 q ≠ oldStateCombined243 92) :
    (machineCombined243.runFrom d j).state ≠ some (oldStateCombined243 92) := by
  rw [he]
  exact fun hs => hq (Option.some.inj hs)

private theorem matched_block (c : Config 244) (d : Config 243)
    (hr : Related c d) (hn : c.state ≠ none) :
    ∃ i j, 0 < i ∧ 0 < j ∧
      Related (machineRotation244.runFrom c i) (machineCombined243.runFrom d j) := by
  rcases hr with ⟨rfl, hi, hcheckpoint⟩
  rcases d with ⟨state, h, t⟩
  cases state with
  | none => exact False.elim (hn rfl)
  | some q =>
    have hq : q ≠ oldStateCombined243 92 :=
      fun he => hcheckpoint (congrArg some he)
    by_cases he : exceptionalRow243 q (Tape.read t h)
    · rcases he with ⟨hb, hcases⟩
      rcases hcases with rfl | rfl | rfl | rfl
      · cases hnext : Tape.read t (h + 1) with
        | false =>
          refine ⟨2, 4, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old104] using
              (enter122_from104_read0 h t hb hnext)
          · exact checkpoint_of_endpoint (enter122_from104_read0_new_endpoint h t hb hnext) endpoint_distinct.1
        | true =>
          refine ⟨2, 2, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old104] using
              (enter122_from104_read1 h t hb hnext)
          · exact checkpoint_of_endpoint (enter122_from104_read1_new_endpoint h t hb hnext) endpoint_distinct.2.1
      · cases hnext : Tape.read t (h + 1) with
        | false =>
          refine ⟨2, 4, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old106] using
              (enter122_from106_read0 h t hb hnext)
          · exact checkpoint_of_endpoint (enter122_from106_read0_new_endpoint h t hb hnext) endpoint_distinct.1
        | true =>
          refine ⟨2, 2, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old106] using
              (enter122_from106_read1 h t hb hnext)
          · exact checkpoint_of_endpoint (enter122_from106_read1_new_endpoint h t hb hnext) endpoint_distinct.2.1
      · have hleft : Tape.read t (h - 1) = true := hi.2.2 rfl
        refine ⟨2, 2, by decide, by decide, pair_of_block hi ?_ ?_⟩
        · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old167] using
            (repair167 h t hleft hb)
        · exact checkpoint_of_endpoint (repair167_new_endpoint h t hleft hb) endpoint_distinct.2.2.1
      · cases hleft : Tape.read t (h - 1) with
        | false =>
          refine ⟨2, 2, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old81] using
              (enter92_from81_zero h t hleft hb)
          · exact checkpoint_of_endpoint (enter92_from81_zero_new_endpoint h t hleft hb) endpoint_distinct.2.2.2.1
        | true =>
          have htwo : Tape.read t (h - 2) = true := hi.2.1 rfl hleft
          refine ⟨6, 4, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig243, Option.map_some, embedState243_old81] using
              (enter92_from81_one h t htwo hleft hb)
          · exact checkpoint_of_endpoint (enter92_from81_one_new_endpoint h t htwo hleft hb) endpoint_distinct.2.2.2.2
    · refine ⟨1, 1, by decide, by decide, ?_⟩
      change Related (machineRotation244.step (embedConfig243 ⟨some q, h, t⟩))
        (machineCombined243.step ⟨some q, h, t⟩)
      exact ⟨(ordinary_step q h t hq he).symm,
        step_holds _ hi, combined243_common_next q (Tape.read t h) hq he⟩

/-- Both block clocks are positive; matching endpoints agree on halt. -/
theorem simulation :
    PositiveBlockBisimulation.Simulation machineRotation244 machineCombined243 Related where
  halted c d hr := by
    rcases hr with ⟨rfl, _, _⟩
    cases hs : d.state <;> simp [embedConfig243, hs]
  block := matched_block

/-- This source only claims arbitrary finite-support Core tapes. -/
theorem start_halts_iff (h : Int) (t : Tape) :
    BinaryHalts machineRotation244 (cfgOld 95 h t) ↔
      BinaryHalts machineCombined243 (cfgNew 95 h t) := by
  apply PositiveBlockBisimulation.halts_iff simulation
  refine ⟨?_, start_holds h t, ?_⟩
  · rfl
  · exact fun hs => (by decide : oldStateCombined243 95 ≠ oldStateCombined243 92)
      (Option.some.inj hs)

theorem blank_halts_iff :
    (∃ t, (machineRotation244.run t).state = none) ↔
      ∃ t, (machineCombined243.run t).state = none := by
  apply PositiveBlockBisimulation.blank_halts_iff simulation
  exact ⟨embedConfig243_initial.symm, initial_holds, by decide⟩

theorem blank_nonhalts_iff :
    (¬ ∃ t, (machineRotation244.run t).state = none) ↔
      ¬ ∃ t, (machineCombined243.run t).state = none :=
  not_congr blank_halts_iff

end SetTheory.BusyBeaver.ZFC.Combined243Simulation
