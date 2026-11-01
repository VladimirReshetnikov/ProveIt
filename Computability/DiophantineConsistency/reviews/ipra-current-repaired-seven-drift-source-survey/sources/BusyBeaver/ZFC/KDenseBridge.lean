import BusyBeaver.Core
import BusyBeaver.ZFC.KZip

/-!
From a dense `Machine n` to a sparse-label zipper table (the analogue of the Rocq endpoints'
`Dense*.v` relabelling).

The dense machine's working states `0 .. n-1` are relabelled by `ex` into the sparse table `M`;
its halt (`next = none`) goes to the sparse terminal label `H`, which has no row. If every dense
row commutes with the relabelling (`Commutes`), the blank-tape Core run halts iff the zipper run
from `zc (ex 0) [] []` does. The tape relation reads every cell of Core's finite-support tape off
the two zipper sides; the zipper drops trailing blanks, which read as blanks.
-/

namespace SetTheory.BusyBeaver.ZFC.KDenseBridge

open KZip

/-- The actual blank Core run reaches the halt state. -/
def BlankHalts {states : Nat} (M : Machine states) : Prop :=
  ∃ t, (M.run t).state = none

/-- The sparse label of a dense state, the halt going to `H`. -/
def lab {n : Nat} (ex : Nat → Nat) (H : Nat) : Option (Fin n) → Nat
  | some q => ex q.val
  | none => H

def Commutes {n : Nat} (D : Machine n) (M : TMN) (ex : Nat → Nat) (H : Nat) : Prop :=
  ∀ (q : Fin n) (b : Bool),
    M (ex q.val) b = some ((D.transition q b).write, decide ((D.transition q b).move = .right),
      lab ex H (D.transition q b).next)

theorem getD_trim : ∀ (l : List Bool) (i : Nat), (trim l).getD i false = l.getD i false
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

theorem getD_tail (l : List Bool) (i : Nat) : l.tail.getD i false = l.getD (i + 1) false := by
  cases l <;> simp

/-- The zipper `z` shows the Core configuration `c`. -/
def Rel {n : Nat} (ex : Nat → Nat) (H : Nat) (c : Config n) (z : Conf) : Prop :=
  z.q = lab ex H c.state ∧
    ∀ i : Nat, Tape.read c.tape (c.head + (i : Int)) = z.r.getD i false ∧
      Tape.read c.tape (c.head - ((i + 1 : Nat) : Int)) = z.l.getD i false

section Bridge

variable {n : Nat} {D : Machine n} {M : TMN} {ex : Nat → Nat} {H : Nat}

theorem rel_step (hc : Commutes D M ex H) {c : Config n} {z : Conf} {q : Fin n}
    (hr : Rel ex H c z) (hq : c.state = some q) :
    ∃ z', step M z = some z' ∧ Rel ex H (D.step c) z' := by
  obtain ⟨hzq, ht⟩ := hr
  rw [hq] at hzq
  replace hzq : z.q = ex q.val := hzq
  have hread : Tape.read c.tape c.head = z.r.headD false := by
    have := (ht 0).1
    simp only [Int.natCast_zero, Int.add_zero] at this
    rw [this]; cases z.r <;> rfl
  have hrow := hc q (z.r.headD false)
  rw [← hzq] at hrow
  have hds : D.step c = Config.mk (D.transition q (z.r.headD false)).next
      ((D.transition q (z.r.headD false)).move.apply c.head)
      (Tape.write c.tape c.head (D.transition q (z.r.headD false)).write) := by
    unfold Machine.step; rw [hq]; simp only [hread]
  rw [hds]
  generalize D.transition q (z.r.headD false) = a at hrow
  obtain ⟨w, mv, nx⟩ := a
  have hq' : lab ex H nx = lab ex H (Config.mk nx (Move.apply mv c.head) (Tape.write c.tape c.head w)).state := rfl
  cases mv with
  | right =>
      refine ⟨zc (lab ex H nx) (w :: z.l) z.r.tail, ?_, ?_⟩
      · unfold step; rw [hrow]; rfl
      · refine ⟨hq', fun i => ⟨?_, ?_⟩⟩
        · simp only [zc, getD_trim, getD_tail, Move.apply]
          rw [Tape.read_write_of_ne _ (by omega)]
          have e : c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) := by omega
          rw [e]; exact (ht (i + 1)).1
        · simp only [zc, getD_trim, Move.apply]
          cases i with
          | zero =>
              have e : c.head + 1 - ((0 + 1 : Nat) : Int) = c.head := by omega
              rw [e, Tape.read_write_same]; rfl
          | succ j =>
              rw [Tape.read_write_of_ne _ (by omega)]
              have e : c.head + 1 - ((j + 1 + 1 : Nat) : Int) = c.head - ((j + 1 : Nat) : Int) := by
                omega
              rw [e]; simpa using (ht j).2
  | left =>
      refine ⟨zl (lab ex H nx) z.l (w :: z.r.tail), ?_, ?_⟩
      · unfold step; rw [hrow]; rfl
      · refine ⟨hq', fun i => ⟨?_, ?_⟩⟩
        · simp only [zl, zc, getD_trim, Move.apply]
          match i with
          | 0 =>
              rw [Tape.read_write_of_ne _ (by omega)]
              have e : c.head - 1 + ((0 : Nat) : Int) = c.head - ((0 + 1 : Nat) : Int) := by omega
              rw [e, (ht 0).2]; cases z.l <;> rfl
          | 1 =>
              have e : c.head - 1 + ((1 : Nat) : Int) = c.head := by omega
              rw [e, Tape.read_write_same]; rfl
          | j + 2 =>
              rw [Tape.read_write_of_ne _ (by omega)]
              have e : c.head - 1 + ((j + 2 : Nat) : Int) = c.head + ((j + 1 : Nat) : Int) := by omega
              rw [e, (ht (j + 1)).1]
              simp
        · simp only [zl, zc, getD_trim, getD_tail, Move.apply]
          rw [Tape.read_write_of_ne _ (by omega)]
          have e : c.head - 1 - ((i + 1 : Nat) : Int) = c.head - ((i + 1 + 1 : Nat) : Int) := by omega
          rw [e]; exact (ht (i + 1)).2

theorem rel_halt (hH : ∀ b, M H b = none) {c : Config n} {z : Conf} (hr : Rel ex H c z)
    (hq : c.state = none) : step M z = none := by
  obtain ⟨hzq, _⟩ := hr
  rw [hq] at hzq
  simp only [step, hzq, lab, hH]

theorem run_succ (M : TMN) (t : Nat) (c : Conf) :
    run M (t + 1) c = match run M t c with | none => none | some c' => step M c' := by
  rw [run_add]
  cases run M t c with
  | none => rfl
  | some c' => simp only [run]; cases step M c' <;> rfl

end Bridge

/-- **Dense bridge.** A dense machine whose rows commute with the relabelling halts on the blank
tape iff the sparse zipper machine halts from the relabelled blank configuration. -/
theorem blank_iff {m : Nat} {D : Machine (m + 1)} {M : TMN} {ex : Nat → Nat} {H : Nat}
    (hc : Commutes D M ex H) (hH : ∀ b, M H b = none) :
    BlankHalts D ↔ Halts M (zc (ex 0) [] []) := by
  have h0 : Rel ex H (D.run 0) (zc (ex 0) [] []) :=
    ⟨rfl, fun _ => by constructor <;> simp [Machine.run, initial, Tape.read, zc]⟩
  -- Remember both sides' halting in the stopped branch. This one invariant
  -- supplies both directions; a second induction over the sparse run is unnecessary.
  have key : ∀ t, (BlankHalts D ∧ Halts M (zc (ex 0) [] [])) ∨
      ∃ z, run M t (zc (ex 0) [] []) = some z ∧ Rel ex H (D.run t) z := by
    intro t
    induction t with
    | zero => exact Or.inr ⟨_, rfl, h0⟩
    | succ t ih =>
        rcases ih with hh | ⟨z, hz, hr⟩
        · exact Or.inl hh
        · cases hs : (D.run t).state with
          | none => exact Or.inl ⟨⟨t, hs⟩, z, ⟨t, hz⟩, rel_halt hH hr hs⟩
          | some q =>
              obtain ⟨z', h1, h2⟩ := rel_step hc hr hs
              exact Or.inr ⟨z', by rwa [run_succ, hz], h2⟩
  constructor
  · rintro ⟨t, ht⟩
    rcases key t with hh | ⟨z, hz, hr⟩
    · exact hh.2
    · exact ⟨z, ⟨t, hz⟩, rel_halt hH hr ht⟩
  · rintro ⟨y, ⟨k, hk⟩, hy⟩
    rcases key (k + 1) with hh | ⟨z, hz, _⟩
    · exact hh.1
    · simp [run_succ, hk, hy] at hz

end SetTheory.BusyBeaver.ZFC.KDenseBridge
