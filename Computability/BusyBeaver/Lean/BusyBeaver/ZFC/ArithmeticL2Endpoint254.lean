import BusyBeaver.ZFC.ArithmeticL2Scheduler254
import BusyBeaver.ZFC.ControlBisimRotation240

set_option autoImplicit false

/-!
# Internal L2, part 7: the scheduler and the dag254 interpreter halt together

In every model of `IΣ₁`:

* `root_occ`: the root of the 219-node program occupies controls
  `1, …, 6460` of the packed dag254 catalogue, its normal exit restarting at
  control `1` (one kernel check of `occB` on literal data; the Python model is
  `Research/ZFC/rotation240_pa/check_root_occ.py`);
* `Related`: a live scheduler configuration `liveValue pl np (stateValue t s d h)`
  is related to the interpreter state `liveValue 1 (enc (toAS pl np t s d h))`
  (a `Σ₁` relation, given by an explicit formula);
* `halts_iff`: by positive-clock transport (`ArithmeticPositiveSimulation254`),
  the scheduler halts from a configuration iff the represented dag254
  interpreter halts from its record. Positivity of each clock holds because one
  root run changes the record (`root_step`: the pointer decreases or the
  candidate increases);
* `accepted_iff_dag_halts`, `accepted_iff_rotation_halts`: at the logical seed
  (`np = 3`, `p1 = 3`, all other registers zero) the represented validator
  accepts a proof of falsity iff the dag254 interpreter halts, iff the
  Rotation240 interpreter `controlRun ControlBisimRotation240.tableR` halts
  (with `ControlBisimRotation240.halts_iff`). The latter is the W6 interface of
  `Research/ZFC/pa_internalization.md`.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticCommandStep254 (stateValue)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The root occurrence, checked by the kernel on the packed table. -/
theorem root_occB :
    occB Dag254.dag254 DagControl254.rowsLit 220 (.node 0) 1 (fun _ => 1) = true := by
  decide +kernel

theorem root_occ : Occ Dag254.dag254 DagControl254.rowsLit 220 (.node 0) 1 (fun _ => 1) :=
  occ_of_occB _ _ 220 _ 1 _ root_occB

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The relation -/

/-- The interpreter state of a scheduler configuration. -/
noncomputable def binOf (pl np t s d h : V) : V :=
  ArithmeticControlFile.liveValue 1 (enc (toAS pl np t s d h))

/-- Scheduler configurations and the interpreter states at their records. -/
def Related (l b : V) : Prop :=
  ∃ pl np t s d h : V, l = ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h) ∧
    b = binOf pl np t s d h

/-- The record of a configuration as nested pairs (the order of `enc`). -/
theorem enc_toAS (pl np t s d h : V) : enc (toAS pl np t s d h) =
    cantor s (cantor pl (cantor t (cantor d (cantor 0 (cantor 0 (cantor np (cantor h 0))))))) := by
  rfl

def relatedDef : 𝚺₁.Semisentence 2 := .mkSigma
  “l b. ∃ pl, ∃ np, ∃ t, ∃ s, ∃ d, ∃ h, ∃ w, ∃ z,
    z = 0 ∧
    !ArithmeticCommandStep254.stateDef w t s d h ∧
    !ArithmeticEnumeratorStep254.liveDef l pl np w ∧
    ∃ p7, !ArithmeticCantor.pairDef p7 h z ∧
    ∃ p6, !ArithmeticCantor.pairDef p6 np p7 ∧
    ∃ p5, !ArithmeticCantor.pairDef p5 z p6 ∧
    ∃ p4, !ArithmeticCantor.pairDef p4 z p5 ∧
    ∃ p3, !ArithmeticCantor.pairDef p3 d p4 ∧
    ∃ p2, !ArithmeticCantor.pairDef p2 t p3 ∧
    ∃ p1, !ArithmeticCantor.pairDef p1 pl p2 ∧
    ∃ f, !ArithmeticCantor.pairDef f s p1 ∧
    ∃ q, !ArithmeticCantor.pairDef q 1 f ∧ b = q + 1”

instance related_defined : 𝚺₁-Relation[V] Related via relatedDef := .mk fun e => by
  simp [relatedDef, Related, binOf, enc_toAS, ArithmeticControlFile.liveValue]

instance related_definable : 𝚺₁-Relation[V] Related :=
  HierarchySymbol.Defined.to_definable relatedDef related_defined

/-! ## The simulation obligations -/

theorem liveFile_ne (c x : V) : ArithmeticControlFile.liveValue c x ≠ 0 := by
  simp [ArithmeticControlFile.liveValue]

theorem liveFile_inj {c x y : V} (h : ArithmeticControlFile.liveValue c x =
    ArithmeticControlFile.liveValue c y) : x = y := by
  simp only [ArithmeticControlFile.liveValue, add_left_inj] at h
  exact (cantor_injective h).2

/-- The normal exit of a root run, read at the root occurrence. -/
theorem root_reach {st st' : AS V} (h : Rn (.node 0) st st') :
    ∃ k, DagControl254.run k (ArithmeticControlFile.liveValue 1 (enc st)) =
      ArithmeticControlFile.liveValue 1 (enc st') := by
  have := h 220 1 (fun _ => 1) root_occ
  simpa [Reach] using this

theorem root_reach_halt {st : AS V} {y : V} (h : IR (.node 0) (enc st) .halt y) :
    ∃ k, DagControl254.run k (ArithmeticControlFile.liveValue 1 (enc st)) = 0 := by
  have := h 220 1 (fun _ => 1) root_occ
  simpa [Reach] using this

theorem toAS_ne {pl np t s d h pl' np' t' s' d' h' : V} (hd : pl' < pl ∨ np' = np + 1) :
    enc (toAS pl np t s d h) ≠ enc (toAS pl' np' t' s' d' h') := by
  intro he
  have h8 := congrArg (fun x => lreg x 8) he
  have h0 := congrArg (fun x => lreg x 0) he
  simp only [lreg_enc _ 8 (by norm_num), lreg_enc _ 0 (by norm_num), field, toAS] at h8 h0
  rcases hd with hlt | heq
  · exact (_root_.lt_irrefl pl) (h8 ▸ hlt)
  · rw [heq] at h0
    exact (_root_.lt_irrefl np) (lt_of_lt_of_eq (lt_add_one np) h0.symm)

theorem related_step (l b : V) (hr : Related l b)
    (hn : ArithmeticEnumeratorStep254.step l ≠ 0) :
    ∃ k, 0 < k ∧ Related (ArithmeticEnumeratorStep254.step l) (DagControl254.run k b) := by
  obtain ⟨pl, np, t, s, d, h, rfl, rfl⟩ := hr
  rcases root_step pl np t s d h with ⟨hz, _⟩ | ⟨pl', np', t', s', d', h', hv, hrn, hd⟩
  · exact absurd hz hn
  · obtain ⟨k, hk⟩ := root_reach hrn
    refine ⟨k, ?_, pl', np', t', s', d', h', hv, hk⟩
    rcases (Arithmetic.zero_le k).lt_or_eq with hpos | h0
    · exact hpos
    · exfalso
      rw [← h0, R.run_zero] at hk
      exact toAS_ne hd (liveFile_inj hk)

theorem related_halt (l b : V) (hr : Related l b)
    (hz : ArithmeticEnumeratorStep254.step l = 0) :
    ∃ k, DagControl254.run k b = 0 := by
  obtain ⟨pl, np, t, s, d, h, rfl, rfl⟩ := hr
  rcases root_step pl np t s d h with ⟨_, y, hy⟩ | ⟨pl', np', t', s', d', h', hv, _, _⟩
  · exact root_reach_halt hy
  · rw [hv] at hz
    exact absurd hz (ArithmeticEnumeratorStep254.live_ne_zero _ _ _)

/-- The scheduler halts from a configuration iff the dag254 interpreter halts
from its record. -/
theorem halts_iff (pl np t s d h : V) :
    (∃ n, ArithmeticEnumeratorRun254.run n
        (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h)) = 0) ↔
      (∃ k, DagControl254.run k (binOf pl np t s d h) = 0) := by
  haveI : 𝚺₁-Function₁[V] (fun n => ArithmeticEnumeratorRun254.run n
      (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h))) := by
    definability
  apply ArithmeticPositiveSimulation254.halts_iff
    ArithmeticEnumeratorStep254.step
    (fun n => ArithmeticEnumeratorRun254.run n
      (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h)))
    DagControl254.run Related (fun b => b = 0)
    (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h)) (binOf pl np t s d h)
  · exact ArithmeticEnumeratorRun254.run_zero _
  · intro n; exact ArithmeticEnumeratorRun254.run_succ n _
  · exact R.run_zero
  · exact R.run_add
  · exact ⟨pl, np, t, s, d, h, rfl, rfl⟩
  · rintro l b ⟨_, _, _, _, _, _, rfl, _⟩
    exact ArithmeticEnumeratorStep254.live_ne_zero _ _ _
  · rintro l b ⟨_, _, _, _, _, _, _, rfl⟩
    exact liveFile_ne _ _
  · exact related_step
  · exact related_halt
  · rintro b rfl k
    exact ArithmeticControlTable.controlRun_halted _ k

/-! ## The seed -/

/-- The logical seed record: `np = 3`, `p1 = 3`, all else zero. -/
theorem seed_record : toAS (0 : V) 3 0 0 3 0 = ⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ := rfl

/-- The validator accepts a proof of falsity iff the dag254 interpreter halts
from the seed record. -/
theorem accepted_iff_dag_halts :
    (∃ code : V, ArithmeticHistory254.value code = 2) ↔
      (∃ k, DagControl254.run k
        (ArithmeticControlFile.liveValue 1 (enc (⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ : AS V))) = 0) :=
  ArithmeticEnumeratorSeed246.accepted_iff_seed_halts.trans (halts_iff 0 3 0 0 3 0)

/-- The W6 interface: the validator accepts a proof of falsity iff the
represented Rotation240 interpreter halts from the seed record. -/
theorem accepted_iff_rotation_halts :
    (∃ code : V, ArithmeticHistory254.value code = 2) ↔
      (∃ k, ArithmeticControlTable.controlRun ControlBisimRotation240.tableR k
        (ArithmeticControlFile.liveValue 1 (enc (⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ : AS V))) = 0) :=
  accepted_iff_dag_halts.trans (ControlBisimRotation240.halts_iff _)

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
