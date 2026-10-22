import CM215Tables

namespace CM215

abbrev Tape := Int → Bool

structure Config where
  state : State
  head : Int
  tape : Tape

def write (t : Tape) (h : Int) (v : Bool) : Tape :=
  fun x => if x = h then v else t x

def move (right : Bool) : Int := if right then 1 else -1

def act (a : Action) (c : Config) : Config :=
  ⟨a.next, c.head + move a.right, write c.tape c.head a.write⟩

def step (d : State → Bool → Option Action) (c : Config) : Option Config :=
  (d c.state (c.tape c.head)).map (fun a => act a c)

def mapped (c : Config) : Config := {c with state := phi c.state}

def Invariant (c : Config) : Prop :=
  (c.state = 52 → c.tape (c.head - 1) = true) ∧
  (c.state = 170 → c.tape c.head = true ∨ c.tape (c.head - 1) = false) ∧
  (c.state = 151 → c.tape (c.head + 1) = true)

@[simp] theorem write_at (t : Tape) (h : Int) (v : Bool) : write t h v h = v := by
  simp [write]

@[simp] theorem write_else (t : Tape) (h x : Int) (v : Bool) (hx : x ≠ h) :
    write t h v x = t x := by simp [write, hx]

theorem write_same (t : Tape) (h : Int) : write t h (t h) = t := by
  funext x
  by_cases hx : x = h <;> simp [write, hx]

theorem write_of_read (t : Tape) (h : Int) (b : Bool) (hb : t h = b) :
    write t h b = t := by rw [← hb]; exact write_same t h

theorem mapped_act (a : Action) (c : Config) :
    act (phiAction a) (mapped c) = mapped (act a c) := rfl

theorem invariant_act (c : Config) (a : Action)
    (hc : Invariant c) (ha : incomingCondition c.state (c.tape c.head) a) :
    Invariant (act a c) := by
  rcases ha with ⟨h52, h170, h151⟩
  constructor
  · intro h
    obtain ⟨hw, hd⟩ := h52 h
    simp [act, move, hw, hd]
  constructor
  · intro h
    rcases h170 h with ⟨hw, hd⟩ | ⟨hq, hb, hd⟩
    · right
      simp [act, move, hw, hd]
    · left
      have hx : c.head + 1 ≠ c.head := by omega
      simpa [act, move, hd, write, hx] using hc.2.2 hq
  · intro h
    obtain ⟨hw, hd⟩ := h151 h
    have hx : c.head + -1 + 1 = c.head := by omega
    simp [act, move, hw, hd, hx]

theorem invariant_step (c c' : Config) (hc : Invariant c)
    (hs : step old c = some c') : Invariant c' := by
  unfold step at hs
  cases he : old c.state (c.tape c.head) with
  | none => simp [he] at hs
  | some a =>
    have hi := incoming c.state (c.tape c.head)
    simp only [he] at hi hs
    cases Option.some.inj hs
    exact invariant_act c a hc hi

theorem initial_invariant (t : Tape) (h : Int) : Invariant ⟨0,h,t⟩ := by
  simp [Invariant]

theorem ordinary_step (c c' : Config)
    (hq : c.state ≠ 52) (hr : c.state ≠ 170)
    (hs : step old c = some c') :
    step new (mapped c) = some (mapped c') := by
  unfold step at hs ⊢
  simp only [mapped]
  rw [commute c.state (c.tape c.head) hq hr]
  cases he : old c.state (c.tape c.head) with
  | none => simp [he] at hs
  | some a =>
    simp only [he, Option.map_some] at hs ⊢
    cases Option.some.inj hs
    exact congrArg some (mapped_act a c)

theorem halt_step_agrees (c : Config) :
    (step old c = none) ↔ (step new (mapped c) = none) := by
  simp only [step, Option.map_eq_none_iff, mapped]
  exact halt_agrees c.state (c.tape c.head)

end CM215
