from pathlib import Path
import hashlib,json
H=Path(__file__).parent
s='''import BusyBeaver.ZFC.PositiveBlockBisimulation
import BusyBeaver.ZFC.Routing245Invariant
import BusyBeaver.ZFC.Compensated244Blocks

/-!
Concrete positive-block simulation of the exact compensated244 table against
Routing245. The relation preserves the original local tape invariant and
excludes old92 from paired endpoints; old122 is absent from the new state set.
All results concern Core finite-support tapes, including the blank tape.
No functional infinite-support tape semantics or PA internalization is claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.Compensated244Simulation

open Compensated244Blocks Routing245Invariant RuntimePerm252

/-- Full configuration equality after state embedding, with the checkpoint facts. -/
def Related (c : Config 245) (d : Config 244) : Prop :=
  c = embedConfig244 d ∧ Holds c ∧ d.state ≠ some (oldStateCompensated244 92)

private theorem endpoint_distinct :
    oldStateCompensated244 25 ≠ oldStateCompensated244 92 ∧
    oldStateCompensated244 66 ≠ oldStateCompensated244 92 ∧
    oldStateCompensated244 24 ≠ oldStateCompensated244 92 ∧
    oldStateCompensated244 107 ≠ oldStateCompensated244 92 ∧
    oldStateCompensated244 2 ≠ oldStateCompensated244 92 := by decide +kernel

private theorem ordinary_step (q : Fin 244) (h : Int) (t : Tape)
    (hq : q ≠ oldStateCompensated244 92)
    (he : ¬ exceptionalRow244 q (Tape.read t h)) :
    embedConfig244 (machineCompensated244.step ⟨some q, h, t⟩) =
      machineRouting245.step (embedConfig244 ⟨some q, h, t⟩) := by
  simp only [Machine.step, embedConfig244, Option.map_some]
  rw [← compensated244_common_action q (Tape.read t h) hq he]
  rfl

private theorem pair_of_block {c : Config 245} {d : Config 244} {i j : Nat}
    (hi : Holds c)
    (he : embedConfig244 (machineCompensated244.runFrom d j) = machineRouting245.runFrom c i)
    (hn : (machineCompensated244.runFrom d j).state ≠ some (oldStateCompensated244 92)) :
    Related (machineRouting245.runFrom c i) (machineCompensated244.runFrom d j) :=
  ⟨he.symm, runFrom_holds c hi i, hn⟩

private theorem checkpoint_of_endpoint {d : Config 244} {j q : Nat} {h : Int} {t : Tape}
    (he : machineCompensated244.runFrom d j = cfgNew q h t)
    (hq : oldStateCompensated244 q ≠ oldStateCompensated244 92) :
    (machineCompensated244.runFrom d j).state ≠ some (oldStateCompensated244 92) := by
  rw [he]
  exact fun hs => hq (Option.some.inj hs)

private theorem matched_block (c : Config 245) (d : Config 244)
    (hr : Related c d) (hn : c.state ≠ none) :
    ∃ i j, 0 < i ∧ 0 < j ∧
      Related (machineRouting245.runFrom c i) (machineCompensated244.runFrom d j) := by
  rcases hr with ⟨rfl, hi, hcheckpoint⟩
  rcases d with ⟨state, h, t⟩
  cases state with
  | none => exact False.elim (hn rfl)
  | some q =>
    have hq : q ≠ oldStateCompensated244 92 :=
      fun he => hcheckpoint (congrArg some he)
    by_cases he : exceptionalRow244 q (Tape.read t h)
    · rcases he with ⟨hb, hcases⟩
      rcases hcases with rfl | rfl | rfl | rfl
'''
# Four entry rows; next-bit branches instantiate the seven fixed identities.
for q in [104,106]:
 s+='''      · cases hnext : Tape.read t (h + 1) with
'''
 for b in [0,1]:
  name=f'enter122_from{q}_read{b}';j=4 if b==0 else2;dist='endpoint_distinct.1'if b==0 else'endpoint_distinct.2.1'
  s+=f'''        | {'false'if b==0 else'true'} =>
          refine ⟨2, {j}, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig244, Option.map_some, embedState244_old{q}] using
              ({name} h t hb hnext)
          · exact checkpoint_of_endpoint ({name}_new_endpoint h t hb hnext) {dist}
'''
s+='''      · have hleft : Tape.read t (h - 1) = true := hi.2.2 rfl
        refine ⟨2, 2, by decide, by decide, pair_of_block hi ?_ ?_⟩
        · simpa only [cfgOld, cfgNew, embedConfig244, Option.map_some, embedState244_old167] using
            (repair167 h t hleft hb)
        · exact checkpoint_of_endpoint (repair167_new_endpoint h t hleft hb) endpoint_distinct.2.2.1
      · cases hleft : Tape.read t (h - 1) with
        | false =>
          refine ⟨2, 2, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig244, Option.map_some, embedState244_old81] using
              (enter92_from81_zero h t hleft hb)
          · exact checkpoint_of_endpoint (enter92_from81_zero_new_endpoint h t hleft hb) endpoint_distinct.2.2.2.1
        | true =>
          have htwo : Tape.read t (h - 2) = true := hi.2.1 rfl hleft
          refine ⟨6, 4, by decide, by decide, pair_of_block hi ?_ ?_⟩
          · simpa only [cfgOld, cfgNew, embedConfig244, Option.map_some, embedState244_old81] using
              (enter92_from81_one h t htwo hleft hb)
          · exact checkpoint_of_endpoint (enter92_from81_one_new_endpoint h t htwo hleft hb) endpoint_distinct.2.2.2.2
    · refine ⟨1, 1, by decide, by decide, ?_⟩
      change Related (machineRouting245.step (embedConfig244 ⟨some q, h, t⟩))
        (machineCompensated244.step ⟨some q, h, t⟩)
      exact ⟨(ordinary_step q h t hq he).symm,
        step_holds _ hi, compensated244_common_next q (Tape.read t h) hq he⟩

/-- Both block clocks are positive; matching endpoints agree on halt. -/
theorem simulation :
    PositiveBlockBisimulation.Simulation machineRouting245 machineCompensated244 Related where
  halted c d hr := by
    rcases hr with ⟨rfl, _, _⟩
    cases hs : d.state <;> simp [embedConfig244, hs]
  block := matched_block

/-- This source only claims arbitrary finite-support Core tapes. -/
theorem start_halts_iff (h : Int) (t : Tape) :
    BinaryHalts machineRouting245 (cfgOld 95 h t) ↔
      BinaryHalts machineCompensated244 (cfgNew 95 h t) := by
  apply PositiveBlockBisimulation.halts_iff simulation
  refine ⟨?_, start_holds h t, ?_⟩
  · rfl
  · exact fun hs => (by decide : oldStateCompensated244 95 ≠ oldStateCompensated244 92)
      (Option.some.inj hs)

theorem blank_halts_iff :
    (∃ t, (machineRouting245.run t).state = none) ↔
      ∃ t, (machineCompensated244.run t).state = none := by
  apply PositiveBlockBisimulation.blank_halts_iff simulation
  exact ⟨embedConfig244_initial.symm, initial_holds, by decide⟩

theorem blank_nonhalts_iff :
    (¬ ∃ t, (machineRouting245.run t).state = none) ↔
      ¬ ∃ t, (machineCompensated244.run t).state = none :=
  not_congr blank_halts_iff

end SetTheory.BusyBeaver.ZFC.Compensated244Simulation
'''
(H/'Compensated244Simulation.lean').write_text(s)
a='''import BusyBeaver.ZFC.Compensated244Simulation

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.Compensated244Simulation
open SetTheory.BusyBeaver.ZFC.Compensated244Blocks
open SetTheory.BusyBeaver.ZFC.RuntimePerm252

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.simulation
#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.start_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.blank_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.blank_nonhalts_iff

example : PositiveBlockBisimulation.Simulation machineRouting245 machineCompensated244 Related := simulation
example (h : Int) (t : Tape) :
    BinaryHalts machineRouting245 (cfgOld 95 h t) ↔ BinaryHalts machineCompensated244 (cfgNew 95 h t) :=
  start_halts_iff h t
example : (∃ t, (machineRouting245.run t).state = none) ↔ ∃ t, (machineCompensated244.run t).state = none :=
  blank_halts_iff
example : (¬ ∃ t, (machineRouting245.run t).state = none) ↔ ¬ ∃ t, (machineCompensated244.run t).state = none :=
  blank_nonhalts_iff
'''
(H/'Audit.lean').write_text(a)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();print(json.dumps({p.name:sha(p)for p in [H/'Compensated244Simulation.lean',H/'Audit.lean']}))
