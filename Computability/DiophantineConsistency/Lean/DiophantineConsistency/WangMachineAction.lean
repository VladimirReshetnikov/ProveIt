import DiophantineConsistency.WangMachineEncoding
import DiophantineConsistency.WangTiles942Language

/-!
# Actual decimal transitions and literal Wang-table actions

The input index is `2*q+b`. The existing complete decoder/cache theorem
binds its literal action to the actual machine transition. Target bounds
come from the already proved actual direction-specific target sets, so
the target215 is exactly the optional halt state and not an out-of-range
operating state. No decimal numeral or full table is reevaluated here.
-/

namespace DiophantineConsistency.WangMachineAction

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC WangMachineEncoding

set_option Elab.async false
set_option maxRecDepth 10000

/-- The literal 430-action index of an operating state and read bit. -/
def inputIndex (q : Fin 215) (b : Bool) : Fin 430 :=
  ⟨2 * q.val + b.toNat, by
    have hq := q.isLt
    have hb := bit_le_one b
    omega⟩

@[simp] theorem inputIndex_val (q : Fin 215) (b : Bool) :
    (inputIndex q b).val = 2 * q.val + b.toNat := rfl

theorem inputIndex_div_two (q : Fin 215) (b : Bool) :
    (inputIndex q b).val / 2 = q.val := by
  have hb := bit_le_one b
  rw [inputIndex_val]
  omega

theorem inputIndex_mod_two (q : Fin 215) (b : Bool) :
    (inputIndex q b).val % 2 = b.toNat := by
  have hb := bit_le_one b
  rw [inputIndex_val]
  omega

/-- The transition tile's north color is the encoded operating head. -/
theorem inputIndex_north (q : Fin 215) (b : Bool) :
    (inputIndex q b).val + 2 = WangTiles942.headColor q.val b.toNat := rfl

theorem action_target_lt (j : Fin 430) : (WangTiles942.action j).2.2 < 216 := by
  apply WangTiles942.target_bounds (WangTiles942.action j).2.1
  exact List.mem_toFinset.mp (WangTiles942Language.action_target_mem j)

/-- Valid numeric targets preserve their number under the actual optional
state convention, including exactly the halting target215. -/
theorem act_stateNumber (a : Bool × Bool × ℕ) (ha : a.2.2 < 216) :
    stateNumber (KDense215.act a).next = a.2.2 := by
  by_cases h : a.2.2 < 215
  · simp [KDense215.act, h, stateNumber]
  · have he : a.2.2 = 215 := by omega
    simp [KDense215.act, stateNumber, he]

theorem act_next_none_iff (a : Bool × Bool × ℕ) (ha : a.2.2 < 216) :
    (KDense215.act a).next = none ↔ a.2.2 = 215 := by
  rw [← stateNumber_injective.eq_iff, act_stateNumber a ha, stateNumber_none]

/-- This binds the literal cached action to the actual decimal machine. -/
theorem transition_eq_cached (q : Fin 215) (b : Bool) :
    DecimalMachine215.machine.transition q b =
      KDense215.act (WangTiles942.action (inputIndex q b)) := by
  change KDense215.act (DecimalMachine215.action (2 * q.val + if b then 1 else 0)) = _
  have hi : 2 * q.val + (if b then 1 else 0) = (inputIndex q b).val := by
    cases b <;> rfl
  rw [hi]
  exact congrArg KDense215.act (WangTiles942.action_eq_decoder (inputIndex q b)).symm

theorem transition_write (q : Fin 215) (b : Bool) :
    (DecimalMachine215.machine.transition q b).write =
      (WangTiles942.action (inputIndex q b)).1 := by
  rw [transition_eq_cached]
  rfl

theorem transition_move (q : Fin 215) (b : Bool) :
    (DecimalMachine215.machine.transition q b).move =
      if (WangTiles942.action (inputIndex q b)).2.1 then Move.right else Move.left := by
  rw [transition_eq_cached]
  rfl

theorem transition_moved_head (q : Fin 215) (b : Bool) (p : ℤ) :
    (DecimalMachine215.machine.transition q b).move.apply p =
      if (WangTiles942.action (inputIndex q b)).2.1 then p + 1 else p - 1 := by
  rw [transition_move]
  cases (WangTiles942.action (inputIndex q b)).2.1 <;> rfl

theorem transition_stateNumber (q : Fin 215) (b : Bool) :
    stateNumber (DecimalMachine215.machine.transition q b).next =
      (WangTiles942.action (inputIndex q b)).2.2 := by
  rw [transition_eq_cached]
  exact act_stateNumber _ (action_target_lt _)

theorem transition_next_none_iff (q : Fin 215) (b : Bool) :
    (DecimalMachine215.machine.transition q b).next = none ↔
      (WangTiles942.action (inputIndex q b)).2.2 = 215 := by
  rw [transition_eq_cached]
  exact act_next_none_iff _ (action_target_lt _)

/-- The receiving tile's numeric target gives precisely the encoded actual
next head, including halting heads432/433. Its read bit is unrestricted. -/
theorem transition_headColor (q : Fin 215) (b c : Bool) :
    headColor (DecimalMachine215.machine.transition q b).next c =
      WangTiles942.headColor (WangTiles942.action (inputIndex q b)).2.2 c.toNat := by
  unfold headColor
  rw [transition_stateNumber]

end DiophantineConsistency.WangMachineAction
