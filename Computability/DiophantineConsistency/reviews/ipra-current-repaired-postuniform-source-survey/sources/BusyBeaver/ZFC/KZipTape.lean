import BusyBeaver.ZFC.KZip
import BusyBeaver.ZFC.FramedWindow

/-! Exact step/run transport from integer tapes to finite zipper configurations.
Only related tapes are transported; no representation of every infinite tape
by a finite zipper is assumed. Decoder restoration keeps the exact step count. -/
namespace SetTheory.BusyBeaver.ZFC.KZipTape
open KZip

/-- Interpret the zipper table's Boolean direction as the integer displacement ±1. -/
def table (M : TMN) : FramedWindow.Table := fun q b =>
  (M q b).map fun (w, right, q') => ⟨w, if right then 1 else -1, q'⟩

/-- Both complete half-tapes agree, starting at the integer head. -/
def Rel (c : FramedWindow.Full) (z : Conf) : Prop :=
  z.q = c.state ∧ ∀ i : Nat,
    c.tape (c.head + (i : Int)) = z.r.getD i false ∧
    c.tape (c.head - ((i + 1 : Nat) : Int)) = z.l.getD i false

private theorem getD_trim : ∀ (l : List Bool) (i : Nat),
    (trim l).getD i false = l.getD i false
  | [], _ => rfl
  | b :: l, i => by
      rw [trim_cons]
      split
      · rename_i h
        obtain ⟨rfl, ht⟩ := h
        cases i with
        | zero => rfl
        | succ i => simpa [ht] using (getD_trim l i).symm
      · cases i with
        | zero => rfl
        | succ i => simpa using getD_trim l i

private theorem getD_tail (l : List Bool) (i : Nat) :
    l.tail.getD i false = l.getD (i + 1) false := by cases l <;> simp

/-- One full-tape step has the same zipper step, including its write and direction. -/
theorem rel_step {M : TMN} {c d : FramedWindow.Full} {z : Conf}
    (hr : Rel c z) (hs : FramedWindow.fullStep (table M) c = some d) :
    ∃ z', KZip.step M z = some z' ∧ Rel d z' := by
  obtain ⟨hzq, ht⟩ := hr
  have hread : c.tape c.head = z.r.headD false := by
    have := (ht 0).1
    simp only [Int.natCast_zero, Int.add_zero] at this
    rw [this]; cases z.r <;> rfl
  cases hrow : M z.q (z.r.headD false) with
  | none =>
    simp only [FramedWindow.fullStep, table, ← hzq, hread, hrow, Option.map_none] at hs
    cases hs
  | some a =>
    obtain ⟨w, right, q'⟩ := a
    have hd : d = ⟨q', c.head + (if right then 1 else -1),
        FramedWindow.write c.tape c.head w⟩ := by
      apply Option.some.inj
      simpa only [FramedWindow.fullStep, table, ← hzq, hread, hrow, Option.map_some, bind, pure, Option.bind_some] using hs.symm
    subst d
    cases right with
    | true =>
      change ∃ z', KZip.step M z = some z' ∧
        Rel ⟨q', c.head + 1, FramedWindow.write c.tape c.head w⟩ z'
      refine ⟨zc q' (w :: z.l) z.r.tail, ?_, rfl, fun i => ⟨?_, ?_⟩⟩
      · simp only [KZip.step, hrow]
      · simp only [zc, getD_trim, getD_tail]
        simp only [FramedWindow.write, if_neg (show c.head + 1 + (i : Int) ≠ c.head by omega)]
        rw [show c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) by omega]
        exact (ht (i + 1)).1
      · simp only [zc, getD_trim]
        cases i with
        | zero => simp [FramedWindow.write]
        | succ j =>
          simp only [FramedWindow.write, if_neg (show c.head + 1 - ((j + 1 + 1 : Nat) : Int) ≠ c.head by omega)]
          rw [show c.head + 1 - ((j + 1 + 1 : Nat) : Int) = c.head - ((j + 1 : Nat) : Int) by omega]
          simpa using (ht j).2
    | false =>
      change ∃ z', KZip.step M z = some z' ∧
        Rel ⟨q', c.head - 1, FramedWindow.write c.tape c.head w⟩ z'
      refine ⟨zl q' z.l (w :: z.r.tail), ?_, rfl, fun i => ⟨?_, ?_⟩⟩
      · simp only [KZip.step, hrow]
      · simp only [zl, zc, getD_trim]
        match i with
        | 0 =>
          simp only [FramedWindow.write, if_neg (show c.head - 1 + ((0 : Nat) : Int) ≠ c.head by omega)]
          rw [show c.head - 1 + ((0 : Nat) : Int) = c.head - ((0 + 1 : Nat) : Int) by omega,
            (ht 0).2]
          cases z.l <;> rfl
        | 1 =>
          rw [show c.head - 1 + ((1 : Nat) : Int) = c.head by omega]
          simp [FramedWindow.write]
        | j + 2 =>
          simp only [FramedWindow.write, if_neg (show c.head - 1 + ((j + 2 : Nat) : Int) ≠ c.head by omega)]
          rw [show c.head - 1 + ((j + 2 : Nat) : Int) = c.head + ((j + 1 : Nat) : Int) by omega,
            (ht (j + 1)).1]
          simp
      · simp only [zl, zc, getD_trim, getD_tail]
        simp only [FramedWindow.write, if_neg (show c.head - 1 - ((i + 1 : Nat) : Int) ≠ c.head by omega)]
        rw [show c.head - 1 - ((i + 1 : Nat) : Int) = c.head - ((i + 1 + 1 : Nat) : Int) by omega]
        exact (ht (i + 1)).2

/-- Full-tape runs lift to zipper runs without changing their length. -/
theorem rel_run {M : TMN} {c d : FramedWindow.Full} {z : Conf} (hr : Rel c z)
    {n : Nat} (hs : FramedWindow.run (FramedWindow.fullStep (table M)) n c = some d) :
    ∃ z', KZip.run M n z = some z' ∧ Rel d z' := by
  induction n generalizing c z with
  | zero =>
    simp only [FramedWindow.run, Option.some.injEq] at hs
    subst d
    exact ⟨z, rfl, hr⟩
  | succ n ih =>
    cases he : FramedWindow.fullStep (table M) c with
    | none => simp [FramedWindow.run, he] at hs
    | some e =>
      obtain ⟨z', hz', hr'⟩ := rel_step hr he
      obtain ⟨z'', hz'', hr''⟩ := ih hr' (by simpa [FramedWindow.run, he] using hs)
      exact ⟨z'', by simp [KZip.run, hz', hz''], hr''⟩

private theorem trim_nil_of_false (l : List Bool) (h : ∀ i, l.getD i false = false) :
    trim l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b = false := h 0
    have ht : trim l = [] := ih (fun i => by simpa using h (i+1))
    simp [trim_cons, hb, ht]

private theorem trim_eq_of_getD (l r : List Bool)
    (h : ∀ i, l.getD i false = r.getD i false) : trim l = trim r := by
  induction l generalizing r with
  | nil =>
    exact (trim_nil_of_false r (fun i => (h i).symm)).symm
  | cons b l ih =>
    cases r with
    | nil => exact trim_nil_of_false (b :: l) h
    | cons c r =>
      obtain rfl : b = c := h 0
      exact trim_cons_congr _ (ih r (fun i => by simpa using h (i+1)))

/-- Normalized zipper configurations representing the same full tape are equal. -/
theorem rel_unique {c : FramedWindow.Full} {z z' : Conf} (h : Rel c z) (h' : Rel c z')
    (hz : trim z.l = z.l ∧ trim z.r = z.r)
    (hz' : trim z'.l = z'.l ∧ trim z'.r = z'.r) : z = z' := by
  have hl : z.l = z'.l := by
    rw [← hz.1, ← hz'.1]
    exact trim_eq_of_getD _ _ fun i => (h.2 i).2.symm.trans (h'.2 i).2
  have hr : z.r = z'.r := by
    rw [← hz.2, ← hz'.2]
    exact trim_eq_of_getD _ _ fun i => (h.2 i).1.symm.trans (h'.2 i).1
  cases z; cases z'; simp_all [Rel]

private theorem run_normal {M : TMN} {n : Nat} {z z' : Conf}
    (hz : trim z.l = z.l ∧ trim z.r = z.r) (hs : KZip.run M n z = some z') :
    trim z'.l = z'.l ∧ trim z'.r = z'.r := by
  induction n generalizing z with
  | zero =>
    simp only [KZip.run, Option.some.injEq] at hs
    subst z'
    exact hz
  | succ n ih =>
    cases he : KZip.step M z with
    | none => simp [KZip.run, he] at hs
    | some e =>
      apply ih (z := e) ?_ (by simpa [KZip.run, he] using hs)
      unfold KZip.step at he
      split at he
      · simp at he
      all_goals (cases he; exact ⟨trim_trim _, trim_trim _⟩)

/-- Reflect a full-tape endpoint when its two zipper representations are normalized. -/
theorem run_reflect {M : TMN} {c d : FramedWindow.Full} {z z' : Conf}
    (hr : Rel c z) (hr' : Rel d z')
    (hz : trim z.l = z.l ∧ trim z.r = z.r)
    (hz' : trim z'.l = z'.l ∧ trim z'.r = z'.r)
    {n : Nat} (hs : FramedWindow.run (FramedWindow.fullStep (table M)) n c = some d) :
    KZip.run M n z = some z' := by
  obtain ⟨e, he, hre⟩ := rel_run hr hs
  exact (rel_unique hre hr' (run_normal hz he) hz') ▸ he

/-- The complete integer tape shown by a finite zipper; the head is at zero. -/
def tape (z : Conf) : FramedWindow.Tape
  | .ofNat i => z.r.getD i false
  | .negSucc i => z.l.getD i false

def full (z : Conf) : FramedWindow.Full := ⟨z.q, 0, tape z⟩

theorem rel_full (z : Conf) : Rel (full z) z := by
  refine ⟨rfl, fun i => ⟨?_, ?_⟩⟩
  · change tape z (0 + (i : Int)) = z.r.getD i false
    rw [Int.zero_add]; rfl
  · change tape z (0 - ((i + 1 : Nat) : Int)) = z.l.getD i false
    rw [show (0 : Int) - ((i + 1 : Nat) : Int) = Int.negSucc i by omega]
    rfl

/-- Moving the head right on a restored tape is one zipper shift. -/
theorem rel_right {c : FramedWindow.Full} {z : Conf} (hr : Rel c z) (q : Nat) :
    Rel ⟨q, c.head + 1, c.tape⟩ (zc q (z.r.headD false :: z.l) z.r.tail) := by
  refine ⟨rfl, fun i => ⟨?_, ?_⟩⟩
  · simp only [zc, getD_trim, getD_tail]
    rw [show c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) by omega]
    exact (hr.2 (i + 1)).1
  · simp only [zc, getD_trim]
    cases i with
    | zero =>
      rw [show c.head + 1 - ((0 + 1 : Nat) : Int) = c.head by omega]
      have h := (hr.2 0).1
      simp only [Int.natCast_zero, Int.add_zero] at h
      exact h.trans (by cases z.r <;> rfl)
    | succ j =>
      rw [show c.head + 1 - ((j + 1 + 1 : Nat) : Int) = c.head - ((j + 1 : Nat) : Int) by omega]
      simpa using (hr.2 j).2

/-- A checked restored window transports to exactly the maintained zipper step count. -/
theorem check_restore {M : TMN} {n q q' : Nat} {cells : FramedWindow.Cells}
    (hc : FramedWindow.check (table M) n q 0 cells q' 1 = true) (l r : List Bool)
    (hm : FramedWindow.overlay cells (tape (zc q l r)) = tape (zc q l r)) :
    KZip.run M n (zc q l r) = some (zc q' (r.headD false :: l) r.tail) := by
  have hs := FramedWindow.arbitrary_tape (table M) n q 0 cells q' 1 hc
    (tape (zc q l r)) hm
  have h := run_reflect (rel_full (zc q l r)) (rel_right (rel_full (zc q l r)) q')
    ⟨trim_trim _, trim_trim _⟩ ⟨trim_trim _, trim_trim _⟩ hs
  simpa only [zc, headD_trim, tail_trim, trim_cons_trim] using h

/-- Positive certified windows give the progress needed by the machine simulation. -/
theorem check_restore_pos {M : TMN} {n q q' : Nat} {cells : FramedWindow.Cells}
    (hn : 0 < n) (hc : FramedWindow.check (table M) n q 0 cells q' 1 = true)
    (l r : List Bool)
    (hm : FramedWindow.overlay cells (tape (zc q l r)) = tape (zc q l r)) :
    Reach1 M (zc q l r) (zc q' (r.headD false :: l) r.tail) := by
  cases n with
  | zero => omega
  | succ n => exact ⟨n, check_restore hc l r hm⟩

#print axioms rel_step
#print axioms rel_run
#print axioms run_reflect
#print axioms rel_full
#print axioms check_restore
#print axioms check_restore_pos
end SetTheory.BusyBeaver.ZFC.KZipTape
