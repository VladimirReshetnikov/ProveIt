import BusyBeaver.Core
import CM215Transfer

/-! Connect the functional-tape transfer theorem to the repository's concrete
`Machine 215` and finite-support tape representation. -/
namespace CM215
open SetTheory.BusyBeaver PositiveStuttering
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def fromCoreState : Option (Fin 215) → State
  | none => s254
  | some q => ⟨q.val, by omega⟩

def toCoreState (q : State) : Option (Fin 215) :=
  if h : q.val < 215 then some ⟨q.val, h⟩ else none

theorem from_to (q : State) : fromCoreState (toCoreState q) = q := by
  by_cases h : q.val < 215
  · simp [toCoreState, h, fromCoreState]
  · have hq : q = s254 := by apply Fin.ext; simp only [s254]; omega
    subst q
    rfl

theorem fromCore_halt (q : Option (Fin 215)) : fromCoreState q = s254 ↔ q = none := by
  cases q with
  | none => simp [fromCoreState]
  | some q =>
    simp only [fromCoreState, Option.some_ne_none, iff_false]
    intro h
    have he := congrArg Fin.val h
    simp only [s254] at he
    omega

def machineFrom (T : State → Bool → Row) : Machine 215 where
  transition q b :=
    let r := T (fromCoreState (some q)) b
    { write := r.w, move := if r.d = 1 then .right else .left,
      next := toCoreState r.next }

def embed (c : Config 215) : Cfg := ⟨fromCoreState c.state, c.head, Tape.read c.tape⟩

def TableWF (T : State → Bool → Row) : Prop :=
  (∀ q : Fin 215, ∀ b, (T (fromCoreState (some q)) b).d = 1 ∨
    (T (fromCoreState (some q)) b).d = -1) ∧
  (∀ b, T s254 b = ⟨b, 0, s254⟩)

theorem K_wf : TableWF K := by unfold TableWF; decide +kernel
theorem M_wf : TableWF M := by unfold TableWF; decide +kernel

private theorem read_write (t : Tape) (h : Int) (b : Bool) :
    Tape.read (Tape.write t h b) = put (Tape.read t) h b := by
  funext x
  by_cases hx : x = h
  · subst x; simp [put]
  · simp [Tape.read_write_of_ne t hx, put, hx]

private theorem put_read (t : Int → Bool) (h : Int) : put t h (t h) = t := by
  funext x
  by_cases hx : x = h
  · subst x; simp [put]
  · simp [put, hx]

theorem embed_step (T : State → Bool → Row) (hw : TableWF T) (c : Config 215) :
    embed ((machineFrom T).step c) = step T (embed c) := by
  cases c with
  | mk q h t =>
    cases q with
    | none =>
      simp only [Machine.step, embed, step, fromCoreState, hw.2, act, Int.add_zero, put_read]
    | some q =>
      have hd := hw.1 q (Tape.read t h)
      rcases hd with hd | hd
      · simp [Machine.step, embed, machineFrom, step, act, hd, Move.apply, from_to, read_write]
      · have he : h + (-1) = h-1 := by omega
        simp [Machine.step, embed, machineFrom, step, act, hd, Move.apply, from_to, read_write, he]

theorem embed_run (T : State → Bool → Row) (hw : TableWF T) (n : Nat) :
    embed ((machineFrom T).run n) = run (step T) n ⟨s0, 0, fun _ => false⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Machine.run, embed_step T hw, ih]
    rfl

def CoreBlankHalts (D : Machine 215) : Prop := ∃ n, (D.run n).state = none

theorem core_iff (T : State → Bool → Row) (hw : TableWF T) :
    CoreBlankHalts (machineFrom T) ↔
    ∃ n, Halt (run (step T) n ⟨s0, 0, fun _ => false⟩) := by
  unfold CoreBlankHalts
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← embed_run T hw]
    exact (fromCore_halt _).mpr hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← embed_run T hw] at hn
    exact (fromCore_halt _).mp hn

/-- Concrete Machine215-to-Machine215 blank equivalence. -/
theorem core_blank_halts_iff :
    CoreBlankHalts (machineFrom K) ↔ CoreBlankHalts (machineFrom M) :=
  (core_iff K K_wf).trans ((halts_iff (fun _ => false) 0).trans (core_iff M M_wf).symm)

#print axioms core_blank_halts_iff
end CM215
