/-!
List-zipper machines for the K-family runtime (port of K230's `TM230`/`Zip`).

Layer B of the 225/224 Lean endpoints ports the TM side of Elliot Glazer's k230-rocq
(`coq/tm`, commit `3142e4d`). Rocq's busycoq tapes are streams, so a tape padded with blanks is
literally the same tape; here a tape side is a list of bits with **no trailing blanks** (`trim`),
renormalized after every step, so padding is again an equality (`zc_padl`, `zc_padr`).

A machine is a numeric transition function `tmn q b = some (w, right?, q')`; `none` is the
terminal (halting) row. `zc q l r` has the head on the first cell of `r`, `zl q l r` on the
first cell of `l` (both sides read away from the head).
-/

namespace SetTheory.BusyBeaver.ZFC.KZip

/-- A transition function: `some (write, moveRight, next)`, or `none` to halt. -/
abbrev TMN := Nat → Bool → Option (Bool × Bool × Nat)

/-- Drop trailing blanks. -/
def trim : List Bool → List Bool
  | [] => []
  | b :: l => if b = false ∧ trim l = [] then [] else b :: trim l

/-- A configuration: state, left side (read leftwards), right side starting at the head. -/
structure Conf where
  q : Nat
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def zc (q : Nat) (l r : List Bool) : Conf := ⟨q, trim l, trim r⟩

def zl (q : Nat) (l r : List Bool) : Conf := zc q l.tail (l.headD false :: r)

def step (M : TMN) (c : Conf) : Option Conf :=
  match M c.q (c.r.headD false) with
  | none => none
  | some (w, true, q') => some (zc q' (w :: c.l) c.r.tail)
  | some (w, false, q') => some (zl q' c.l (w :: c.r.tail))

def run (M : TMN) : Nat → Conf → Option Conf
  | 0, c => some c
  | k + 1, c => match step M c with
    | none => none
    | some c' => run M k c'

/-- `c` reaches `c'` in some number of steps. -/
def Reach (M : TMN) (c c' : Conf) : Prop := ∃ k, run M k c = some c'

/-- `c` reaches `c'` in at least one step. -/
def Reach1 (M : TMN) (c c' : Conf) : Prop := ∃ k, run M (k + 1) c = some c'

/-- `c` halts: it reaches a configuration with no row. -/
def Halts (M : TMN) (c : Conf) : Prop := ∃ c', Reach M c c' ∧ step M c' = none

/-! ## Trimming -/

@[simp] theorem trim_nil : trim [] = [] := rfl

theorem trim_cons (b : Bool) (l : List Bool) :
    trim (b :: l) = if b = false ∧ trim l = [] then [] else b :: trim l := rfl

theorem trim_trim : ∀ l : List Bool, trim (trim l) = trim l
  | [] => rfl
  | b :: l => by
      rw [trim_cons]
      split
      · rfl
      · rename_i h; rw [trim_cons, trim_trim l]; simp only [h, if_false]

/-- `trim (a :: t)` depends only on `trim t`. -/
theorem trim_cons_congr (a : Bool) {t t' : List Bool} (h : trim t = trim t') :
    trim (a :: t) = trim (a :: t') := by
  rw [trim_cons, trim_cons, h]

theorem trim_cons_trim (b : Bool) (l : List Bool) : trim (b :: trim l) = trim (b :: l) :=
  trim_cons_congr b (trim_trim l)

theorem trim_append_false : ∀ l : List Bool, trim (l ++ [false]) = trim l
  | [] => rfl
  | b :: l => trim_cons_congr b (trim_append_false l)

theorem trim_append_zeros (l : List Bool) (n : Nat) :
    trim (l ++ List.replicate n false) = trim l := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ', ← List.append_assoc, trim_append_false, ih]

theorem headD_trim : ∀ l : List Bool, (trim l).headD false = l.headD false
  | [] => rfl
  | b :: l => by
      rw [trim_cons]; split
      · rename_i h; simp [h.1]
      · rfl

theorem tail_trim : ∀ l : List Bool, trim (trim l).tail = trim l.tail
  | [] => rfl
  | b :: l => by
      rw [trim_cons]; split
      · rename_i h; simp [h.2]
      · simp [trim_trim]

theorem zc_padl (q : Nat) (l r : List Bool) (n : Nat) :
    zc q (l ++ List.replicate n false) r = zc q l r := by
  simp [zc, trim_append_zeros]

theorem zc_padr (q : Nat) (l r : List Bool) (n : Nat) :
    zc q l (r ++ List.replicate n false) = zc q l r := by
  simp [zc, trim_append_zeros]

theorem zl_padl (q : Nat) (l r : List Bool) (n : Nat) :
    zl q (l ++ List.replicate n false) r = zl q l r := by
  cases l with
  | nil =>
      cases n with
      | zero => rfl
      | succ n =>
          have hz : trim (List.replicate n false) = [] := by
            simpa [trim_nil] using trim_append_zeros [] n
          simp only [List.nil_append, List.replicate_succ, zl, List.tail_cons, List.headD_cons,
            List.tail_nil, List.headD_nil, zc, hz, trim_nil]
  | cons b l => simp [zl, zc, trim_append_zeros]

/-! ## Single steps on the zipper views -/

theorem step_zc (M : TMN) (q : Nat) (l r : List Bool) :
    step M (zc q l r) =
      match M q (r.headD false) with
      | none => none
      | some (w, true, q') => some (zc q' (w :: l) r.tail)
      | some (w, false, q') => some (zl q' l (w :: r.tail)) := by
  simp only [step, zc, headD_trim]
  split
  · rfl
  · simp only [zc, trim_cons_trim, tail_trim]
  · simp only [zl, zc, tail_trim, headD_trim]
    congr 2
    exact trim_cons_congr _ (trim_cons_congr _ (tail_trim r))

theorem zR {M : TMN} {q q' : Nat} {l r : List Bool} {b w : Bool}
    (h : M q b = some (w, true, q')) :
    step M (zc q l (b :: r)) = some (zc q' (w :: l) r) := by
  rw [step_zc]; simp [h]

theorem zL {M : TMN} {q q' : Nat} {l r : List Bool} {b w : Bool}
    (h : M q b = some (w, false, q')) :
    step M (zc q l (b :: r)) = some (zl q' l (w :: r)) := by
  rw [step_zc]; simp [h]

theorem zl_cons (q : Nat) (x : Bool) (l r : List Bool) : zl q (x :: l) r = zc q l (x :: r) := rfl

/-! ## Runs -/

theorem run_add (M : TMN) (a b : Nat) (c : Conf) :
    run M (a + b) c = match run M a c with | none => none | some c' => run M b c' := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [run]
      cases step M c with
      | none => rfl
      | some c1 => exact ih c1

theorem Reach.refl (M : TMN) (c : Conf) : Reach M c c := ⟨0, rfl⟩

theorem Reach.trans {M : TMN} {a b c : Conf} (h1 : Reach M a b) (h2 : Reach M b c) :
    Reach M a c := by
  obtain ⟨i, hi⟩ := h1; obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rwa [run_add, hi]⟩

theorem Reach.of_eq {M : TMN} {a b : Conf} (h : a = b) : Reach M a b := h ▸ Reach.refl M a

theorem Reach.of_step {M : TMN} {a b : Conf} (h : step M a = some b) : Reach M a b :=
  ⟨1, by simp [run, h]⟩

theorem Reach1.of_step {M : TMN} {a b : Conf} (h : step M a = some b) : Reach1 M a b :=
  ⟨0, by simp [run, h]⟩

theorem Reach1.reach {M : TMN} {a b : Conf} (h : Reach1 M a b) : Reach M a b :=
  let ⟨k, hk⟩ := h; ⟨k + 1, hk⟩

theorem Reach1.trans_reach {M : TMN} {a b c : Conf} (h1 : Reach1 M a b) (h2 : Reach M b c) :
    Reach1 M a c := by
  obtain ⟨i, hi⟩ := h1; obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rwa [show i + j + 1 = (i + 1) + j by omega, run_add, hi]⟩

theorem Reach.trans_reach1 {M : TMN} {a b c : Conf} (h1 : Reach M a b) (h2 : Reach1 M b c) :
    Reach1 M a c := by
  obtain ⟨i, hi⟩ := h1; obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rwa [show i + j + 1 = i + (j + 1) by omega, run_add, hi]⟩

theorem Halts.of_reach {M : TMN} {a b : Conf} (h : Reach M a b) (hb : Halts M b) : Halts M a := by
  obtain ⟨c, hc, hs⟩ := hb; exact ⟨c, h.trans hc, hs⟩

/-! ## Self-loop scans -/

theorem scanR {M : TMN} {q : Nat} {b w : Bool} (h : M q b = some (w, true, q)) :
    ∀ (n : Nat) (l r : List Bool),
      Reach M (zc q l (List.replicate n b ++ r)) (zc q (List.replicate n w ++ l) r)
  | 0, l, r => Reach.refl M _
  | n + 1, l, r => by
      have h1 := zR (l := l) (r := List.replicate n b ++ r) h
      refine (Reach.of_step (by simpa [List.replicate_succ] using h1)).trans ?_
      have := scanR h n (w :: l) r
      have e : List.replicate n w ++ w :: l = List.replicate (n + 1) w ++ l := by
        rw [List.replicate_succ']; simp
      rwa [e] at this

theorem scanL {M : TMN} {q : Nat} {b w : Bool} (h : M q b = some (w, false, q)) :
    ∀ (n : Nat) (l r : List Bool),
      Reach M (zl q (List.replicate n b ++ l) r) (zl q l (List.replicate n w ++ r))
  | 0, l, r => Reach.refl M _
  | n + 1, l, r => by
      rw [List.replicate_succ, List.cons_append, zl_cons]
      have h1 := zL (l := List.replicate n b ++ l) (r := r) h
      refine (Reach.of_step h1).trans ?_
      have := scanL h n l (w :: r)
      have e : List.replicate n w ++ w :: r = List.replicate (n + 1) w ++ r := by
        rw [List.replicate_succ']; simp
      rwa [e] at this

end SetTheory.BusyBeaver.ZFC.KZip
