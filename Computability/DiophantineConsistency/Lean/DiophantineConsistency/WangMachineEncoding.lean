import DiophantineConsistency.DecimalMachineInitialization

/-!
# Literal vertical colors of an actual machine configuration

Plain tape cells carry 0 or 1. The unique head carries `2*q+b+2`,
where operating states have q < 215 and the halted state has q = 215.
An action entering halt still writes and moves before this encoding is
applied; its final head has color 432 or 433 at the moved position.
This module defines no tiling or machine-run correspondence premise.
-/

namespace DiophantineConsistency.WangMachineEncoding

open SetTheory.BusyBeaver

set_option Elab.async false
set_option maxRecDepth 10000

/-- The literal table's state number, including its separate halt state. -/
def stateNumber : Option (Fin 215) → ℕ
  | none => 215
  | some q => q.val

@[simp] theorem stateNumber_none : stateNumber none = 215 := rfl

@[simp] theorem stateNumber_some (q : Fin 215) : stateNumber (some q) = q.val := rfl

theorem stateNumber_le (s : Option (Fin 215)) : stateNumber s ≤ 215 := by
  cases s with
  | none => exact Nat.le_refl _
  | some q => exact Nat.le_of_lt q.isLt

theorem stateNumber_injective : Function.Injective stateNumber := by
  intro s t h
  cases s <;> cases t <;> simp_all [stateNumber, Fin.ext_iff] <;> omega

theorem bit_le_one (b : Bool) : b.toNat ≤ 1 := Bool.toNat_le b

/-- Head colors use precisely the same constructor as the literal table. -/
def headColor (s : Option (Fin 215)) (b : Bool) : ℕ :=
  WangTiles942.headColor (stateNumber s) b.toNat

theorem operating_head_color (q : Fin 215) (b : Bool) :
    headColor (some q) b = WangTiles942.headColor q.val b.toNat := rfl

theorem halted_head_color (b : Bool) : headColor none b = 432 + b.toNat := by
  simp [headColor, stateNumber, WangTiles942.headColor]
  omega

theorem headColor_bounds (s : Option (Fin 215)) (b : Bool) :
    2 ≤ headColor s b ∧ headColor s b ≤ 433 := by
  have hs := stateNumber_le s
  have hb := bit_le_one b
  unfold headColor WangTiles942.headColor
  omega

theorem headColor_injective {s t : Option (Fin 215)} {b c : Bool} :
    headColor s b = headColor t c ↔ s = t ∧ b = c := by
  constructor
  · intro h
    have hb := bit_le_one b
    have hc := bit_le_one c
    unfold headColor WangTiles942.headColor at h
    have hs : stateNumber s = stateNumber t := by omega
    have he : b.toNat = c.toNat := by omega
    refine ⟨stateNumber_injective hs, ?_⟩
    cases b <;> cases c <;> simp_all
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Encode the actual tape, state and head of a configuration. -/
def color (cfg : Config 215) (x : ℤ) : ℕ :=
  if x = cfg.head then headColor cfg.state (Tape.read cfg.tape x)
  else (Tape.read cfg.tape x).toNat

theorem color_at_head (cfg : Config 215) :
    color cfg cfg.head = headColor cfg.state (Tape.read cfg.tape cfg.head) := by
  simp [color]

theorem color_of_ne_head (cfg : Config 215) (x : ℤ) (h : x ≠ cfg.head) :
    color cfg x = (Tape.read cfg.tape x).toNat := by
  simp only [color, if_neg h]

theorem plain_color_le_one (cfg : Config 215) (x : ℤ) (h : x ≠ cfg.head) :
    color cfg x ≤ 1 := by
  rw [color_of_ne_head cfg x h]
  exact bit_le_one _

theorem color_le_433 (cfg : Config 215) (x : ℤ) : color cfg x ≤ 433 := by
  by_cases h : x = cfg.head
  · subst x
    rw [color_at_head]
    exact (headColor_bounds _ _).2
  · have hp := plain_color_le_one cfg x h
    omega

/-- The color itself singles out the configuration's unique head. -/
theorem head_iff (cfg : Config 215) (x : ℤ) : 2 ≤ color cfg x ↔ x = cfg.head := by
  constructor
  · intro h
    by_contra hn
    have hp := plain_color_le_one cfg x hn
    omega
  · rintro rfl
    rw [color_at_head]
    exact (headColor_bounds _ _).1

/-- Even an action whose next state is `none` first writes and moves.
This records the underlying operational convention, without a color shortcut. -/
theorem step_enter_halt (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q)
    (hh : (M.transition q (Tape.read cfg.tape cfg.head)).next = none) :
    M.step cfg =
      { state := none,
        head := (M.transition q (Tape.read cfg.tape cfg.head)).move.apply cfg.head,
        tape := Tape.write cfg.tape cfg.head
          (M.transition q (Tape.read cfg.tape cfg.head)).write } := by
  simp only [Machine.step, hq, hh]

theorem step_enter_halt_color (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q)
    (hh : (M.transition q (Tape.read cfg.tape cfg.head)).next = none) :
    color (M.step cfg)
        ((M.transition q (Tape.read cfg.tape cfg.head)).move.apply cfg.head) =
      432 + (Tape.read
        (Tape.write cfg.tape cfg.head (M.transition q (Tape.read cfg.tape cfg.head)).write)
        ((M.transition q (Tape.read cfg.tape cfg.head)).move.apply cfg.head)).toNat := by
  rw [step_enter_halt M cfg q hq hh]
  exact (color_at_head _).trans (halted_head_color _)

theorem initialized_color_zero : color DecimalMachineInitialization.initialized 0 = 1 := rfl

theorem initialized_color_one : color DecimalMachineInitialization.initialized 1 = 4 := rfl

theorem initialized_color_other (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    color DecimalMachineInitialization.initialized x = 0 := by
  rw [color_of_ne_head _ x h1,
    (DecimalMachineInitialization.initialized_read_false_iff x).mpr h0]
  rfl

/-- The actual boundary configuration is exactly a written origin and an
adjacent operating state1 reading0, with plain blank cells elsewhere. -/
theorem initialized_color (x : ℤ) :
    color DecimalMachineInitialization.initialized x =
      if x = 0 then 1 else if x = 1 then 4 else 0 := by
  split_ifs with h0 h1
  · subst x; exact initialized_color_zero
  · subst x; exact initialized_color_one
  · exact initialized_color_other x h0 h1

end DiophantineConsistency.WangMachineEncoding
