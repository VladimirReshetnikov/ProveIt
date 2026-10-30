import BusyBeaver.ZFC.KRuntimeCore

/-! A shared all-gap home scan. Source-only candidate, not compiled.
The unchanged-word relation and boundary composition adapt the submitted
further-simplifications/HomeReturn draft. The symbolic upper-bound invariant,
padding extraction and concrete shortcut below are new proof work. -/
namespace SetTheory.BusyBeaver.ZFC.KHome
open KZip KRuntimeCore

inductive LeftWord (M : TMN) : Nat → List Bool → Nat → Prop where
  | nil (q) : LeftWord M q [] q
  | cons {q q1 q2 b W} : M q b = some (b, false, q1) →
      LeftWord M q1 W q2 → LeftWord M q (b :: W) q2

theorem LeftWord.append {M : TMN} {p q r : Nat} {U V : List Bool}
    (h : LeftWord M p U q) (k : LeftWord M q V r) : LeftWord M p (U ++ V) r := by
  induction h generalizing r V with
  | nil => exact k
  | cons hr ht ih => exact .cons hr (ih k)

theorem LeftWord.sound {M : TMN} {q q' : Nat} {W : List Bool}
    (h : LeftWord M q W q') (L R : List Bool) :
    Reach M (zl q (W ++ L) R) (zl q' L (W.reverse ++ R)) := by
  induction h generalizing L R with
  | nil q => simpa using Reach.refl M (zl q L R)
  | @cons q q1 q2 b W hrow htail ih =>
    rw [List.cons_append, zl_cons]
    have hs : step M (zc q (W ++ L) (b :: R)) = some (zl q1 (W ++ L) (b :: R)) := zL hrow
    simpa [List.reverse_cons, List.append_assoc] using (Reach.of_step hs).trans (ih L (b :: R))

def state : Nat → Nat
  | 0 => 2 | 1 => 3 | 2 => 5 | 3 => 9 | 4 => 15 | 5 => 23 | 6 => 34 | 7 => 50 | _ => 2

/-- Only the 15 non-boundary scan rows are used by the word proof. -/
structure Rows (M : TMN) : Prop where
  reset : ∀ i, i < 8 → M (state i) true = some (true, false, state 0)
  next : ∀ i, i + 1 < 8 → M (state i) false = some (false, false, state (i + 1))

def Boundary (M : TMN) : Prop :=
  ∀ R, Reach1 M (zl 2 [] (true :: R)) (zc 84 [true] R)

theorem home_word {M : TMN} (hb : Boundary M) (U R : List Bool) (k : Nat)
    (hw : LeftWord M 2 (U ++ [true]) 2) :
    Reach1 M (zl 2 ((U ++ [true]) ++ List.replicate k false) R)
      (zc 84 [true] (U.reverse ++ R)) := by
  rw [zl_padl]
  have hs' : Reach M (zl 2 (U ++ [true]) R) (zl 2 [] (true :: (U.reverse ++ R))) := by
    simpa [List.reverse_append, List.append_assoc] using hw.sound [] R
  exact hs'.trans_reach1 (hb (U.reverse ++ R))

private theorem zeros {M : TMN} (rows : Rows M) : ∀ k i, i + k < 8 →
    LeftWord M (state i) (List.replicate k false) (state (i + k))
  | 0, i, _ => by simpa using LeftWord.nil (M := M) (state i)
  | k + 1, i, h => by
    have ht := zeros rows k (i + 1) (by omega)
    simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      LeftWord.cons (rows.next i (by omega)) ht

private theorem ones {M : TMN} (rows : Rows M) {k i : Nat} (hi : i < 8) (hk : 0 < k) :
    LeftWord M (state i) (List.replicate k true) (state 0) := by
  have loop : ∀ j, LeftWord M (state 0) (List.replicate j true) (state 0) := by
    intro j
    induction j with
    | zero => exact .nil _
    | succ j ih => exact .cons (rows.reset 0 (by decide)) ih
  cases k with
  | zero => omega
  | succ k => exact .cons (rows.reset i hi) (loop k)

/-- An upper bound on the zero streak. A possibly empty true run leaves the
bound unchanged; its actual nonempty instances can only lower that bound. -/
def scanBound : Nat → List Seg → Option Nat
  | i, [] => some i
  | _, .bit true :: xs => scanBound 0 xs
  | i, .bit false :: xs => if i + 1 < 8 then scanBound (i + 1) xs else none
  | i, .run true _ c :: xs => scanBound (if c = 0 then i else 0) xs
  | i, .run false a c :: xs =>
      if a = 0 ∧ i + c < 8 then scanBound (i + c) xs else none
  | _, .box _ :: _ => none

/-- Successful symbolic inspection works for every n and every register file;
the actual exit counter may be smaller than the conservative bound. -/
theorem scanBound_sound {M : TMN} (rows : Rows M) (n : Nat) (vs : List Nat)
    {xs : List Seg} {i k j : Nat} (h : scanBound i xs = some k) (hi : i < 8) (hj : j ≤ i) :
    ∃ j', j' ≤ k ∧ j' < 8 ∧ LeftWord M (state j) (flat n vs xs) (state j') := by
  induction xs generalizing i k j with
  | nil =>
    simp only [scanBound, Option.some.injEq] at h
    subst k
    exact ⟨j, hj, by omega, .nil _⟩
  | cons x xs ih =>
    cases x with
    | bit b =>
      cases b with
      | true =>
        obtain ⟨j', hk, h8, ht⟩ := ih h (by decide : 0 < 8) (Nat.le_refl 0)
        exact ⟨j', hk, h8, by simpa [flat_cons, segList] using LeftWord.cons (rows.reset j (by omega)) ht⟩
      | false =>
        by_cases hb : i + 1 < 8
        · simp only [scanBound, hb, if_true] at h
          obtain ⟨j', hk, h8, ht⟩ := ih h hb (Nat.succ_le_succ hj)
          exact ⟨j', hk, h8, by simpa [flat_cons, segList] using LeftWord.cons (rows.next j (by omega)) ht⟩
        · simp [scanBound, hb] at h
    | run b a c =>
      cases b with
      | true =>
        by_cases hz : a * n + c = 0
        · have hc : c = 0 := by omega
          simp only [scanBound, hc, if_true] at h
          obtain ⟨j', hk, h8, ht⟩ := ih h hi hj
          exact ⟨j', hk, h8, by simpa [flat_cons, segList, hz] using ht⟩
        · have hb : (if c = 0 then i else 0) < 8 := by split <;> omega
          obtain ⟨j', hk, h8, ht⟩ := ih h hb (Nat.zero_le _)
          have hp := ones rows (i := j) (by omega) (show 0 < a * n + c by omega)
          exact ⟨j', hk, h8, by simpa [flat_cons, segList] using hp.append ht⟩
      | false =>
        by_cases hb : a = 0 ∧ i + c < 8
        · simp only [scanBound, hb] at h
          obtain ⟨rfl, hi'⟩ := hb
          obtain ⟨j', hk, h8, ht⟩ := ih h hi' (Nat.add_le_add_right hj c)
          exact ⟨j', hk, h8, by simpa [flat_cons, segList] using (zeros rows c j (by omega)).append ht⟩
        · simp [scanBound, hb] at h
    | box x => simp [scanBound] at h

private theorem scanBound_tail {i k : Nat} {x : Seg} {xs : List Seg}
    (h : scanBound i (x :: xs) = some k) : ∃ j, scanBound j xs = some k := by
  cases x with
  | bit b =>
    cases b with
    | true => exact ⟨0, h⟩
    | false =>
      by_cases hb : i + 1 < 8
      · exact ⟨i + 1, by simpa [scanBound, hb] using h⟩
      · simp [scanBound, hb] at h
  | run b a c =>
    cases b with
    | true => exact ⟨if c = 0 then i else 0, h⟩
    | false =>
      by_cases hb : a = 0 ∧ i + c < 8
      · exact ⟨i + c, by simpa [scanBound, hb] using h⟩
      · simp [scanBound, hb] at h
  | box x => simp [scanBound] at h

private theorem flat_append (n : Nat) (vs : List Nat) (xs ys : List Seg) :
    flat n vs (xs ++ ys) = flat n vs xs ++ flat n vs ys := by simp [flat]

/-- No box occurs in an accepted word; every retained segment is reversal-invariant. -/
theorem flat_reverse {n : Nat} {vs : List Nat} {i k : Nat} {xs : List Seg}
    (h : scanBound i xs = some k) : flat n vs xs.reverse = (flat n vs xs).reverse := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    have ⟨j, hj⟩ := scanBound_tail h
    cases x with
    | box x => simp [scanBound] at h
    | bit b | run b a c => simp [List.reverse_cons, flat_append, flat_cons, flat_nil, segList, ih hj]

/-- Inspect the left list in reverse: discard only blank exterior segments,
then remove one literal marker. The result is the reversed scanned prefix. -/
def stripBlank : List Seg → Option (List Seg)
  | .bit false :: xs => stripBlank xs
  | .run false _ _ :: xs => stripBlank xs
  | .bit true :: xs => some xs
  | _ => none

private theorem stripBlank_shape {r u : List Seg} (h : stripBlank r = some u) :
    ∃ p, r = p ++ (.bit true :: u) ∧
      ∀ n vs, ∃ k, flat n vs p.reverse = List.replicate k false := by
  induction r with
  | nil => simp [stripBlank] at h
  | cons x xs ih =>
    cases x with
    | bit b =>
      cases b with
      | true =>
        simp only [stripBlank, Option.some.injEq] at h
        subst u
        exact ⟨[], rfl, fun _ _ => ⟨0, rfl⟩⟩
      | false =>
        obtain ⟨p, he, hp⟩ := ih h
        refine ⟨.bit false :: p, by simp [he], ?_⟩
        intro n vs
        obtain ⟨k, hk⟩ := hp n vs
        refine ⟨k + 1, ?_⟩
        simp [List.reverse_cons, flat_append, flat_cons, flat_nil, segList, hk,
          List.replicate_succ']
    | run b a c =>
      cases b with
      | true => simp [stripBlank] at h
      | false =>
        obtain ⟨p, he, hp⟩ := ih h
        refine ⟨.run false a c :: p, by simp [he], ?_⟩
        intro n vs
        obtain ⟨k, hk⟩ := hp n vs
        refine ⟨k + (a * n + c), ?_⟩
        simp [List.reverse_cons, flat_append, flat_cons, flat_nil, segList, hk,
          List.replicate_append_replicate]
    | box x => simp [stripBlank] at h

/-- A shortcut only for the home scanner, with no inspection of the right frame. -/
def home : SConf → Option SConf
  | (q, onl, l, r) =>
    if q = 2 ∧ onl = true then
      match stripBlank l.reverse with
      | none => none
      | some u => match scanBound 0 u.reverse with
        | none => none
        | some _ => some (84, false, [.bit true], u ++ r)
    else none

theorem home_sound {M : TMN} (rows : Rows M) (hb : Boundary M) (n : Nat) (vs : List Nat)
    {s t : SConf} (h : home s = some t) : Reach1 M (conc n vs s) (conc n vs t) := by
  obtain ⟨q, onl, l, r⟩ := s
  change (if q = 2 ∧ onl = true then
      (match stripBlank l.reverse with
      | none => none
      | some u => match scanBound 0 u.reverse with
        | none => none
        | some _ => some (84, false, [.bit true], u ++ r))
    else none) = some t at h
  split at h
  · rename_i hq
    obtain ⟨rfl, rfl⟩ := hq
    cases hs : stripBlank l.reverse with
    | none => simp [hs] at h
    | some u =>
      cases hg : scanBound 0 u.reverse with
      | none => simp [hs, hg] at h
      | some k =>
        simp only [hs, hg, Option.some.injEq] at h
        subst t
        obtain ⟨p, he, hp⟩ := stripBlank_shape hs
        have hl : l = u.reverse ++ [.bit true] ++ p.reverse := by
          simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
            congrArg List.reverse he
        obtain ⟨z, hz⟩ := hp n vs
        obtain ⟨j, _, hj, hw⟩ := scanBound_sound rows n vs hg (by decide) (Nat.le_refl 0)
        have ht : LeftWord M 2 (flat n vs u.reverse ++ [true]) 2 :=
          hw.append (.cons (rows.reset j hj) (.nil _))
        have hr := home_word hb (flat n vs u.reverse) (flat n vs r) z ht
        have hf := flat_reverse (n := n) (vs := vs) hg
        simpa [conc, hl, flat_append, flat_cons, flat_nil, segList, hz, ← hf] using hr
  · simp at h

end SetTheory.BusyBeaver.ZFC.KHome

#print axioms SetTheory.BusyBeaver.ZFC.KHome.scanBound_sound
#print axioms SetTheory.BusyBeaver.ZFC.KHome.flat_reverse
#print axioms SetTheory.BusyBeaver.ZFC.KHome.home_sound
