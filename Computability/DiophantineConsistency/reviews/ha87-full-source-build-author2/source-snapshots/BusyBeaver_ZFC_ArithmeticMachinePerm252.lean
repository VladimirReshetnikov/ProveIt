import BusyBeaver.ZFC.FiniteZipper
import BusyBeaver.ZFC.TablePerm252

/-!
Exact arithmetic tape halves for the frozen register-permutation252 machine.
The initial checkpoint is a generic Nat simulation of the actual Core step.
Zero state means halt; invalid state codes are explicit absorbing active sinks.
Both tape halves and the absolute head witness are retained through the whole
FiniteZipper representation. A halting transition still writes and moves.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252
open FiniteZipper
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem read_cons (b : Bool) (bs : List Bool) :
    (b :: bs)[0]?.getD false = b := rfl

/-- Least significant bit is the nearest cell. Trailing zero cells are the
blank exterior already quantified by ZipRep. -/
def bitsCode : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsCode bs

@[simp] theorem bitsCode_head (bs : List Bool) :
    bitsCode bs % 2 = (bs.getD 0 false).toNat := by
  cases bs with
  | nil => rfl
  | cons b bs => cases b <;> simp [bitsCode]

@[simp] theorem bitsCode_tail (bs : List Bool) :
    bitsCode bs / 2 = bitsCode bs.tail := by
  cases bs with
  | nil => rfl
  | cons b bs =>
      cases b
      · simp [bitsCode]
      · simp only [bitsCode, Bool.toNat_true, List.tail_cons]
        omega

@[simp] theorem bitsCode_head_bit (bs : List Bool) :
    decide (bitsCode bs % 2 = 1) = bs.getD 0 false := by
  rw [bitsCode_head]
  cases bs.getD 0 false <;> rfl

def stateCode {n : Nat} : Option (Fin n) → Nat
  | none => 0
  | some q => q.val + 1

@[simp] theorem stateCode_zero_iff {n : Nat} (q : Option (Fin n)) :
    stateCode q = 0 ↔ q = none := by
  cases q <;> simp [stateCode]

structure NumericConfig where
  state : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def encodeZip {n : Nat} (z : ZipConfig n) : NumericConfig :=
  ⟨stateCode z.state, bitsCode z.left, bitsCode z.right⟩

/-- Exactly the indexed action of M. Zero and indices outside 1..n have no
action; their configurations remain unchanged rather than becoming a halt. -/
def actionAt {n : Nat} (M : Machine n) (u : NumericConfig) : Option (Action n) :=
  if u.state = 0 then none else
    if h : u.state - 1 < n then
      some (M.transition ⟨u.state - 1, h⟩ (decide (u.right % 2 = 1)))
    else none

def applyAction {n : Nat} (a : Action n) (u : NumericConfig) : NumericConfig :=
  match a.move with
  | .right => ⟨stateCode a.next, 2 * u.left + a.write.toNat, u.right / 2⟩
  | .left => ⟨stateCode a.next, u.left / 2,
      u.left % 2 + 2 * (a.write.toNat + 2 * (u.right / 2))⟩

def numericStep {n : Nat} (M : Machine n) (u : NumericConfig) : NumericConfig :=
  match actionAt M u with
  | none => u
  | some a => applyAction a u

def nextHead {n : Nat} (M : Machine n) (u : NumericConfig) (h : Int) : Int :=
  match actionAt M u with
  | none => h
  | some a => a.move.apply h

theorem actionAt_encodeZip {n : Nat} (M : Machine n) (z : ZipConfig n) :
    actionAt M (encodeZip z) = z.state.map
      (fun q => M.transition q (z.right.getD 0 false)) := by
  cases hs : z.state with
  | none => simp [actionAt, encodeZip, stateCode, hs]
  | some q =>
      have hq : q.val + 1 - 1 < n := by omega
      have he : (⟨q.val + 1 - 1, hq⟩ : Fin n) = q := Fin.ext (by simp)
      simp only [actionAt, encodeZip, hs, stateCode, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, if_false, hq, dif_pos, he, bitsCode_head_bit,
        Option.map_some]

/-- Numeric tape updates include the final write and move even when next=none. -/
theorem encodeZip_step {n : Nat} (M : Machine n) (z : ZipConfig n) :
    encodeZip (zipStep M z) = numericStep M (encodeZip z) := by
  rw [numericStep, actionAt_encodeZip]
  cases hs : z.state with
  | none => simp [zipStep, hs]
  | some q =>
      simp only [zipStep, hs, Option.map_some]
      generalize M.transition q (z.right.getD 0 false) = a
      cases hm : a.move <;>
        simp [hm, encodeZip, zipWrite, zipLeft, zipRight, applyAction,
          bitsCode, Nat.add_comm, read_cons]

theorem zipStep_head {n : Nat} (M : Machine n) (z : ZipConfig n) :
    (zipStep M z).head = nextHead M (encodeZip z) z.head := by
  rw [nextHead, actionAt_encodeZip]
  cases hs : z.state with
  | none => simp [zipStep, hs]
  | some q =>
      simp only [zipStep, hs, Option.map_some]
      generalize M.transition q (z.right.getD 0 false) = a
      cases hm : a.move <;>
        simp [zipWrite, zipLeft, zipRight, Move.apply]

/-- A whole-tape relation: every Core cell is constrained by the zipper
witness, and its absolute head is explicit. No bounded window is used. -/
def Represents {n : Nat} (c : Config n) (u : NumericConfig) (h : Int) : Prop :=
  ∃ z, ZipRep c z ∧ encodeZip z = u ∧ z.head = h

theorem step_sound {n : Nat} (M : Machine n) (c : Config n)
    (u : NumericConfig) (h : Int) (hc : Represents c u h) :
    Represents (M.step c) (numericStep M u) (nextHead M u h) := by
  obtain ⟨z, hz, rfl, rfl⟩ := hc
  exact ⟨zipStep M z, zipStep_sound M hz, encodeZip_step M z, zipStep_head M z⟩

theorem represents_state {n : Nat} (c : Config n) (u : NumericConfig) (h : Int)
    (hc : Represents c u h) : u.state = 0 ↔ c.state = none := by
  obtain ⟨z, hz, rfl, _⟩ := hc
  simpa only [encodeZip, stateCode_zero_iff] using Iff.of_eq (congrArg (fun q => q = none) hz.1.symm)

@[simp] theorem numericStep_halted {n : Nat} (M : Machine n) (u : NumericConfig)
    (hu : u.state = 0) : numericStep M u = u := by
  simp [numericStep, actionAt, hu]

theorem numericStep_invalid {n : Nat} (M : Machine n) (u : NumericConfig)
    (hu : n < u.state) : numericStep M u = u := by
  by_cases h0 : u.state = 0
  · exact numericStep_halted M u h0
  · have hi : ¬ u.state - 1 < n := by omega
    simp [numericStep, actionAt, h0, hi]

def numericInitial (n : Nat) : NumericConfig := ⟨stateCode (startState n), 0, 0⟩

def blankZip (n : Nat) : ZipConfig n :=
  { state := startState n, head := 0, left := [], right := [] }

theorem initial_represents (n : Nat) :
    Represents (initial n) (numericInitial n) 0 := by
  refine ⟨blankZip n, ?_, rfl, rfl⟩
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

def numericRun {n : Nat} (M : Machine n) : Nat → NumericConfig
  | 0 => numericInitial n
  | t + 1 => numericStep M (numericRun M t)

def numericRunHead {n : Nat} (M : Machine n) : Nat → Int
  | 0 => 0
  | t + 1 => nextHead M (numericRun M t) (numericRunHead M t)

/-- Every finite arithmetic prefix represents ALL actual Core tape cells and
its absolute head. This is a universal Nat theorem, not a bounded experiment. -/
theorem numericRun_sound {n : Nat} (M : Machine n) (t : Nat) :
    Represents (M.run t) (numericRun M t) (numericRunHead M t) := by
  induction t with
  | zero => exact initial_represents n
  | succ t ih => exact step_sound M _ _ _ ih

theorem numericRun_state_bounded {n : Nat} (M : Machine n) (t : Nat) :
    (numericRun M t).state ≤ n := by
  obtain ⟨z, _, hz, _⟩ := numericRun_sound M t
  rw [← hz]
  change stateCode z.state ≤ n
  cases z.state with
  | none => simp [stateCode]
  | some q => simp only [stateCode]; omega

theorem numericRun_state_zero_iff {n : Nat} (M : Machine n) (t : Nat) :
    (numericRun M t).state = 0 ↔ (M.run t).state = none :=
  represents_state _ _ _ (numericRun_sound M t)

/-- Exact actual frozen table binding, no instruction-oracle premise. -/
theorem perm252_halts_iff :
    (∃ t, (numericRun machinePerm252 t).state = 0) ↔
      ∃ t, (machinePerm252.run t).state = none :=
  exists_congr fun t => numericRun_state_zero_iff machinePerm252 t

theorem perm252_initial : numericInitial 252 = ⟨1, 0, 0⟩ := by decide

theorem perm252_first_step :
    numericStep machinePerm252 ⟨1, 0, 0⟩ = ⟨28, 0, 0⟩ := by decide

/-- The actual sole halting edge writes1 and moves right. Neither operation
is suppressed when the returned state becomes zero. -/
theorem perm252_halt_edge (l r : Nat) :
    numericStep machinePerm252 ⟨76, l, 2 * r + 1⟩ = ⟨0, 2 * l + 1, r⟩ := by
  have ht : machinePerm252.transition (75 : Fin 252) true =
      { write := true, move := .right, next := none } := by decide
  simp [numericStep, actionAt, ht, applyAction, stateCode]
  omega

end SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252
