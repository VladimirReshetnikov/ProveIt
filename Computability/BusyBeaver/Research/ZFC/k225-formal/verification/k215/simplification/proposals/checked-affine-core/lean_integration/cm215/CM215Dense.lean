import CM215CoreBridge
import CM215Transfer

set_option maxRecDepth 100000

/-! The literal conditional-marker table as a ProveIt `Machine 215`.
The final equivalence uses the already checked local positive simulation,
without recompiling the original K215 semantic calibration. -/

namespace CM215.CoreBridge

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC

def unlabel (q : CM215.State) : Option (Fin 215) :=
  if h : q.val < 215 then some ⟨q.val, h⟩ else none

theorem label_unlabel (q : CM215.State) : label (unlabel q) = q := by
  unfold unlabel
  split
  · apply Fin.ext
    rfl
  · apply Fin.ext
    simp only [label]
    have hq := q.isLt
    omega

def coreAction (a : CM215.Action) : SetTheory.BusyBeaver.Action 215 :=
  ⟨a.write, if a.right then .right else .left, unlabel a.next⟩

theorem action_coreAction (a : CM215.Action) : action (coreAction a) = a := by
  rcases a with ⟨w, r, q⟩
  cases r <;> simp [action, coreAction, label_unlabel]

theorem newRows_length : CM215.newRows.length = 430 := rfl

theorem new_index_bound (q : Fin 215) (b : Bool) :
    q.val * 2 + b.toNat < CM215.newRows.length := by
  rw [newRows_length]
  have hq := q.isLt
  cases b with
  | false => change q.val * 2 + 0 < 430; omega
  | true => change q.val * 2 + 1 < 430; omega

/-- Exactly 215 operational states, binary tape, L/R moves, and a separate halt. -/
def machineCM215 : Machine 215 where
  transition q b :=
    coreAction (CM215.newRows[q.val * 2 + b.toNat]'(new_index_bound q b))

theorem new_commutes : Commutes machineCM215 CM215.new := by
  constructor
  · intro q b
    change CM215.newRows[q.val * 2 + b.toNat]? =
      some (action (coreAction (CM215.newRows[q.val * 2 + b.toNat]'(new_index_bound q b))))
    rw [action_coreAction]
    exact List.getElem?_eq_some_iff.mpr ⟨new_index_bound q b, rfl⟩
  · intro b
    cases b <;> decide +kernel

theorem new_blank_iff : KDenseBridge.BlankHalts machineCM215 ↔
    PositiveStutter.Halts (CM215.step CM215.new) ⟨0, 0, fun _ => false⟩ :=
  blank_iff new_commutes

/-- Halting equivalence of the two actual `Machine 215` values. -/
theorem core_blank_halts_iff :
    KDenseBridge.BlankHalts KDense215.machine215 ↔ KDenseBridge.BlankHalts machineCM215 :=
  old_blank_iff.trans (CM215.blank_halts_iff.trans new_blank_iff.symm)

theorem core_nonhalting_iff :
    (¬ KDenseBridge.BlankHalts KDense215.machine215) ↔
      (¬ KDenseBridge.BlankHalts machineCM215) :=
  not_congr core_blank_halts_iff

/-- A compiled endpoint interface: instantiate `P` with the existing refutation
predicate and `base` with the repository's checked K215 endpoint. -/
theorem calibration_transfer {P : Prop}
    (base : KDenseBridge.BlankHalts KDense215.machine215 ↔ P) :
    KDenseBridge.BlankHalts machineCM215 ↔ P :=
  core_blank_halts_iff.symm.trans base

#print axioms core_blank_halts_iff
#print axioms core_nonhalting_iff
#print axioms calibration_transfer

end CM215.CoreBridge
