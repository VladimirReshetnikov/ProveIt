import Init

/-! A finite, checked execution window refines arbitrary integer-indexed tapes.
The checker cannot read an unspecified cell. Only ordinary Lean kernel
computation is used by clients. -/
namespace SetTheory.BusyBeaver.ZFC.FramedWindow
abbrev Cells := List (Int × Bool)
abbrev Tape := Int → Bool

def lookup : Cells → Int → Option Bool
  | [], _ => none
  | (j,b)::xs, i => if i = j then some b else lookup xs i

def put : Cells → Int → Bool → Cells
  | [], _, _ => []
  | (j,b)::xs, i, v => if i = j then (j,v)::xs else (j,b)::put xs i v

def overlay (xs : Cells) (t : Tape) (i : Int) : Bool :=
  (lookup xs i).getD (t i)

def write (t : Tape) (i : Int) (b : Bool) : Tape :=
  fun j => if j = i then b else t j

theorem overlay_put (xs : Cells) (t : Tape) (i : Int) (b v : Bool)
    (hi : lookup xs i = some b) :
    overlay (put xs i v) t = write (overlay xs t) i v := by
  funext j
  induction xs with
  | nil => simp [lookup] at hi
  | cons x xs ih =>
    rcases x with ⟨k,c⟩
    by_cases hik : i = k
    · subst k
      by_cases hji : j = i
      · subst j; simp [overlay, put, lookup, write]
      · simp [overlay, put, lookup, write, hji]
    · have ht : lookup xs i = some b := by simpa [lookup, hik] using hi
      have hs := ih ht
      by_cases hjk : j = k
      · subst j
        have hki : k ≠ i := Ne.symm hik
        simp [overlay, put, lookup, write, hik, hki]
      · simpa [overlay, put, lookup, write, hik, hjk] using hs

structure Action where
  write : Bool
  move : Int
  next : Nat
  deriving DecidableEq, Repr
abbrev Table := Nat → Bool → Option Action

structure Local where
  state : Nat
  head : Int
  cells : Cells
  deriving DecidableEq, Repr
structure Full where
  state : Nat
  head : Int
  tape : Tape

def embed (c : Local) (t : Tape) : Full := ⟨c.state, c.head, overlay c.cells t⟩

def localStep (M : Table) (c : Local) : Option Local := do
  let b ← lookup c.cells c.head
  let a ← M c.state b
  return ⟨a.next, c.head + a.move, put c.cells c.head a.write⟩

def fullStep (M : Table) (c : Full) : Option Full := do
  let a ← M c.state (c.tape c.head)
  return ⟨a.next, c.head + a.move, write c.tape c.head a.write⟩

theorem localStep_sound (M : Table) (c d : Local) (t : Tape)
    (h : localStep M c = some d) :
    fullStep M (embed c t) = some (embed d t) := by
  cases hb : lookup c.cells c.head with
  | none => simp [localStep, hb] at h
  | some b =>
    cases ha : M c.state b with
    | none => simp [localStep, hb, ha] at h
    | some a =>
      have hd : d = ⟨a.next, c.head + a.move, put c.cells c.head a.write⟩ := by
        simpa [localStep, hb, ha] using h.symm
      subst d
      have hw := overlay_put c.cells t c.head b a.write hb
      simp [fullStep, embed, overlay, hb, ha, ← hw]

def run {α : Type} (step : α → Option α) : Nat → α → Option α
  | 0, c => some c
  | n+1, c => (step c).bind (run step n)

theorem run_add {α : Type} (step : α → Option α) (m n : Nat) (c : α) :
    run step (m+n) c = (run step m c).bind (run step n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add, run]
    cases h : step c with
    | none => simp [h, run]
    | some d => simpa [h, run] using ih d

theorem run_sound (M : Table) (n : Nat) (c d : Local) (t : Tape)
    (h : run (localStep M) n c = some d) :
    run (fullStep M) n (embed c t) = some (embed d t) := by
  induction n generalizing c with
  | zero => simpa [run] using congrArg (Option.map (fun x => embed x t)) h
  | succ n ih =>
    cases hs : localStep M c with
    | none => simp [run, hs] at h
    | some e =>
      have he : run (localStep M) n e = some d := by simpa [run, hs] using h
      simpa [run, localStep_sound M c e t hs] using ih e he

def check (M : Table) (n : Nat) (q : Nat) (h : Int) (xs : Cells)
    (q' : Nat) (h' : Int) : Bool :=
  match run (localStep M) n ⟨q,h,xs⟩ with
  | none => false
  | some d => decide (d = ⟨q',h',xs⟩)

theorem check_sound (M : Table) (n q : Nat) (h : Int) (xs : Cells)
    (q' : Nat) (h' : Int) (hc : check M n q h xs q' h' = true)
    (t : Tape) :
    run (fullStep M) n ⟨q,h,overlay xs t⟩ =
      some ⟨q',h',overlay xs t⟩ := by
  cases hr : run (localStep M) n ⟨q,h,xs⟩ with
  | none => simp [check, hr] at hc
  | some d =>
    have hd : d = ⟨q',h',xs⟩ := by simpa [check, hr] using hc
    subst d
    exact run_sound M n ⟨q,h,xs⟩ ⟨q',h',xs⟩ t hr

/-- The arbitrary exterior tape is restored, not merely its observed window. -/
theorem arbitrary_tape (M : Table) (n q : Nat) (h : Int) (xs : Cells)
    (q' : Nat) (h' : Int) (hc : check M n q h xs q' h' = true)
    (t : Tape) (hmatch : overlay xs t = t) :
    run (fullStep M) n ⟨q,h,t⟩ = some ⟨q',h',t⟩ := by
  simpa [hmatch] using check_sound M n q h xs q' h' hc t


/-- Translate every absolute coordinate by the same integer. -/
def translate (a : Int) (c : Full) : Full :=
  ⟨c.state, c.head + a, fun i => c.tape (i-a)⟩

theorem fullStep_translate (M : Table) (a : Int) (c : Full) :
    fullStep M (translate a c) = (fullStep M c).map (translate a) := by
  cases ha : M c.state (c.tape c.head) with
  | none => simp [fullStep, translate, ha]
  | some v =>
    have hp : c.head + a + v.move = c.head + v.move + a := by omega
    have hw : write (fun i => c.tape (i-a)) (c.head+a) v.write =
        (fun i => write c.tape c.head v.write (i-a)) := by
      funext j
      have he : j = c.head + a ↔ j-a = c.head := by omega
      simp only [write, he]
    simp [fullStep, translate, ha, hp, hw]

theorem run_translate (M : Table) (a : Int) (n : Nat) (c : Full) :
    run (fullStep M) n (translate a c) =
      (run (fullStep M) n c).map (translate a) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run, fullStep_translate]
    cases hs : fullStep M c with
    | none => rfl
    | some d => simpa using ih d

/-- The certified restored window may occur at every integer head position. -/
theorem arbitrary_tape_at (M : Table) (n q : Nat) (xs : Cells)
    (q' : Nat) (hc : check M n q 0 xs q' 1 = true)
    (a : Int) (t : Tape)
    (hmatch : overlay xs (fun i => t (i+a)) = (fun i => t (i+a))) :
    run (fullStep M) n ⟨q,a,t⟩ = some ⟨q',a+1,t⟩ := by
  have hh := arbitrary_tape M n q 0 xs q' 1 hc (fun i => t (i+a)) hmatch
  have ht := run_translate M a n ⟨q,0,fun i => t (i+a)⟩
  rw [hh] at ht
  have hf : (fun i => t (i-a+a)) = t := by funext i; simp
  simp only [translate, Int.zero_add, hf, Option.map_some] at ht
  simpa [Int.add_comm 1 a] using ht

#print axioms arbitrary_tape_at
end SetTheory.BusyBeaver.ZFC.FramedWindow

