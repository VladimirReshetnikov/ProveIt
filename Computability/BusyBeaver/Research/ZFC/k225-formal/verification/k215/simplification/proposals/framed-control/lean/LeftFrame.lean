import BusyBeaver.ZFC.KHome

/-!
Guarded left frames for the maintained K215 symbolic executor.

This file completes the generic proof obligations in the repository's
round13-left-frame proposal. All source semantics and the machine table are
unchanged. The local checker rejects precisely the boundary case in which an
empty explicit left list would be interpreted as a blank cell.
-/
namespace SetTheory.BusyBeaver.ZFC.KLeftFrame
open KZip KRuntimeCore

def addLeft (F : List Seg) : SConf → SConf
  | (q, onl, l, r) => (q, onl, l ++ F, r)

def safeLeft : SConf → Bool
  | (_, true, [], _) => false
  | _ => true

private theorem peelLeft_addLeft (q : Nat) (b : Bool) (a c : Nat)
    (l r F : List Seg) :
    peelLeft q b a c (l ++ F) r =
      (peelLeft q b a c l r).map (fun p => (addLeft F p.1, p.2)) := by
  cases c <;> cases a <;> rfl

private theorem peelRight_addLeft (q : Nat) (b : Bool) (a c : Nat)
    (l r F : List Seg) :
    peelRight q b a c (l ++ F) r =
      (peelRight q b a c l r).map (fun p => (addLeft F p.1, p.2)) := by
  cases c <;> cases a <;> rfl

/-- Exact symbolic equality, including the progress flag. -/
theorem sstep_addLeft_eq {M : TMN} {br : Branch} {s : SConf}
    (hs : safeLeft s = true) (F : List Seg) :
    sstep M br (addLeft F s) =
      (sstep M br s).map (fun p => (addLeft F p.1, p.2)) := by
  rcases s with ⟨q, onl, l, r⟩
  cases onl with
  | false =>
    cases r with
    | nil => rfl
    | cons x r =>
      cases x with
      | bit b =>
        cases hm : M q b with
        | none => simp [addLeft, sstep, hm]
        | some p =>
          rcases p with ⟨w, d, q'⟩
          cases d <;> simp [addLeft, sstep, hm]
      | run b a c =>
        cases hm : M q b with
        | none => simpa [addLeft, sstep, hm] using peelRight_addLeft q b a c l r F
        | some p =>
          rcases p with ⟨w, d, q'⟩
          cases d with
          | false => simpa [addLeft, sstep, hm] using peelRight_addLeft q b a c l r F
          | true =>
            by_cases hq : q' = q
            · simp [addLeft, sstep, hm, hq]
            · simpa [addLeft, sstep, hm, hq] using peelRight_addLeft q b a c l r F
      | box x =>
        cases r with
        | cons y r => rfl
        | nil =>
          cases ho : oracle q br x with
          | some p =>
            rcases p with ⟨q', x', extra⟩
            cases extra <;> simp [addLeft, sstep, ho]
          | none =>
            cases hm : M q false with
            | none => simp [addLeft, sstep, ho, hm]
            | some p =>
              rcases p with ⟨w, d, q'⟩
              cases w <;> cases d <;> simp [addLeft, sstep, ho, hm]
  | true =>
    cases l with
    | nil => simp [safeLeft] at hs
    | cons x l =>
      cases x with
      | bit b => simp [addLeft, sstep]
      | box x => rfl
      | run b a c =>
        cases hm : M q b with
        | none => simpa [addLeft, sstep, hm] using peelLeft_addLeft q b a c l r F
        | some p =>
          rcases p with ⟨w, d, q'⟩
          cases d with
          | true => simpa [addLeft, sstep, hm] using peelLeft_addLeft q b a c l r F
          | false =>
            by_cases hq : q' = q
            · simp [addLeft, sstep, hm, hq]
            · simpa [addLeft, sstep, hm, hq] using peelLeft_addLeft q b a c l r F

theorem sstep_addLeft {M : TMN} {br : Branch} {s t : SConf} {m : Bool}
    (hs : safeLeft s = true) (h : sstep M br s = some (t, m)) (F : List Seg) :
    sstep M br (addLeft F s) = some (addLeft F t, m) := by
  rw [sstep_addLeft_eq hs, h]
  rfl

/-- A fixed number of guarded symbolic steps, retaining positive progress. -/
def runLocal (M : TMN) (br : Branch) : Nat → SConf → Option (SConf × Bool)
  | 0, s => some (s, false)
  | k + 1, s =>
    if safeLeft s then do
      let (t, m) ← sstep M br s
      let (u, moved) ← runLocal M br k t
      pure (u, m || moved)
    else none

/-- Accepted replay is sound for every appended symbolic left frame.
    The Boolean is a sufficient, conservative witness of positive progress. -/
theorem runLocal_sound {M : TMN} (B : BoxLemmas M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs) (F : List Seg) :
    ∀ k s t m, runLocal M br k s = some (t, m) →
      StepOk M n vs (addLeft F s) (addLeft F t) m := by
  intro k
  induction k with
  | zero =>
    intro s t m h
    simp only [runLocal, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨.refl _ _, fun h => by cases h⟩
  | succ k ih =>
    intro s t m h
    cases hs : safeLeft s with
    | false => simp [runLocal, hs] at h
    | true =>
      cases he : sstep M br s with
      | none => simp [runLocal, hs, he] at h
      | some p =>
        rcases p with ⟨s', m'⟩
        cases ht : runLocal M br k s' with
        | none => simp [runLocal, hs, he, ht] at h
        | some p =>
          rcases p with ⟨t', m''⟩
          have hh : t' = t ∧ (m' || m'') = m := by
            simpa [runLocal, hs, he, ht] using h
          rcases hh with ⟨rfl, rfl⟩
          have hstep := sstep_sound B n (sstep_addLeft hs he F) hv
          have htail := ih s' _ m'' ht
          refine ⟨hstep.1.trans htail.1, ?_⟩
          intro hm
          simp only [Bool.or_eq_true] at hm
          rcases hm with hm | hm
          · exact (hstep.2 hm).trans_reach htail.1
          · exact hstep.1.trans_reach1 (htail.2 hm)

theorem flat_bits (n : Nat) (vs : List Nat) (xs : List Bool) :
    flat n vs (xs.map Seg.bit) = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa [flat, segList] using congrArg (List.cons b) ih

/-- A finite checker for a read-only leftward return word. -/
def wordEnd (M : TMN) : Nat → List Bool → Option Nat
  | q, [] => some q
  | q, b :: bs =>
    match M q b with
    | some (w, false, q') => if w = b then wordEnd M q' bs else none
    | _ => none

theorem wordEnd_sound {M : TMN} {W : List Bool} {q q' : Nat}
    (h : wordEnd M q W = some q') : KHome.LeftWord M q W q' := by
  induction W generalizing q with
  | nil =>
    simp only [wordEnd, Option.some.injEq] at h
    subst q'
    exact .nil _
  | cons b bs ih =>
    cases hr : M q b with
    | none => simp [wordEnd, hr] at h
    | some p =>
      rcases p with ⟨w, d, q1⟩
      cases d with
      | true => simp [wordEnd, hr] at h
      | false =>
        by_cases hw : w = b
        · subst w
          exact .cons hr (ih (by simpa [wordEnd, hr] using h))
        · simp [wordEnd, hr, hw] at h

/-- A word-return contract can begin at any return state, including 1 or 2.
    No arbitrary nonblank far-left exterior is allowed: only trailing blanks. -/
theorem home_framed_word {M : TMN} (hb : KHome.Boundary M)
    (q : Nat) (P R : List Bool) (blanks : Nat)
    (hw : KHome.LeftWord M q (P.reverse ++ [true]) 2) :
    Reach1 M (zl q ((P.reverse ++ [true]) ++ List.replicate blanks false) R)
      (zc 84 [true] (P ++ R)) := by
  rw [zl_padl]
  have hs : Reach M (zl q (P.reverse ++ [true]) R)
      (zl 2 [] (true :: (P ++ R))) := by
    simpa [List.reverse_append, List.append_assoc] using hw.sound [] R
  exact hs.trans_reach1 (hb (P ++ R))

/-- The original bounded Home scan supplies a reusable word contract. -/
theorem prefix_word {M : TMN} (rows : KHome.Rows M) (P : List Bool) {k : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k) :
    KHome.LeftWord M 2 (P.reverse ++ [true]) 2 := by
  obtain ⟨j, _, hj, hword⟩ := KHome.scanBound_sound rows 0 [] hs
    (by decide : 0 < 8) (Nat.le_refl 0)
  have hp : KHome.LeftWord M 2 P.reverse (KHome.state j) := by
    simpa only [flat_bits, KHome.state] using hword
  exact hp.append (.cons (rows.reset j hj) (.nil _))

theorem home_prefix {M : TMN} (rows : KHome.Rows M) (hb : KHome.Boundary M)
    (P R : List Bool) (blanks : Nat) {k : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k) :
    Reach1 M (zl 2 ((P.reverse ++ [true]) ++ List.replicate blanks false) R)
      (zc 84 [true] (P ++ R)) :=
  home_framed_word hb 2 P R blanks (prefix_word rows P hs)

/-- A successful local replay ending immediately before Home yields a complete
    positive macro step, with all tape contents and the frame preserved. -/
theorem runLocal_home_word {M : TMN} (B : BoxLemmas M)
    (hb : KHome.Boundary M) {br : Branch} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (P : List Bool) {q steps : Nat} {s : SConf}
    {r : List Seg} {m : Bool}
    (hword : KHome.LeftWord M q (P.reverse ++ [true]) 2)
    (hlocal : runLocal M br steps s = some ((q, true, [], r), m)) :
    Reach1 M
      (conc n vs (addLeft ((P.reverse.map Seg.bit) ++ [.bit true]) s))
      (zc 84 [true] (P ++ flat n vs r)) := by
  have hrun := (runLocal_sound B n hv ((P.reverse.map Seg.bit) ++ [.bit true])
    steps s (q, true, [], r) m hlocal).1
  have hhome := home_framed_word hb q P (flat n vs r) 0 hword
  have heq : conc n vs (addLeft ((P.reverse.map Seg.bit) ++ [.bit true])
      (q, true, [], r)) = zl q (P.reverse ++ [true]) (flat n vs r) := by
    change zl q (flat n vs ((P.reverse.map Seg.bit) ++ [.bit true])) (flat n vs r) = _
    have ha (xs ys : List Seg) : flat n vs (xs ++ ys) = flat n vs xs ++ flat n vs ys :=
      List.flatMap_append
    rw [ha, flat_bits]
    rfl
  rw [heq] at hrun
  exact hrun.trans_reach1 (by simpa using hhome)

theorem runLocal_home {M : TMN} (B : BoxLemmas M) (rows : KHome.Rows M)
    (hb : KHome.Boundary M) {br : Branch} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (P : List Bool) {k steps : Nat} {s : SConf}
    {r : List Seg} {m : Bool}
    (hscan : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k)
    (hlocal : runLocal M br steps s = some ((2, true, [], r), m)) :
    Reach1 M
      (conc n vs (addLeft ((P.reverse.map Seg.bit) ++ [.bit true]) s))
      (zc 84 [true] (P ++ flat n vs r)) :=
  runLocal_home_word B hb n hv P (prefix_word rows P hscan) hlocal

/-- Removing the guard invalidates symbolic frame transport, even for one bit.
    This structural counterexample holds for every transition table. -/
theorem unsafe_boundary_counterexample (M : TMN) (br : Branch) :
    sstep M br (addLeft [.bit true] (0, true, [], [])) ≠
      (sstep M br (0, true, [], [])).map
        (fun p => (addLeft [.bit true] p.1, p.2)) := by
  simp [sstep, addLeft]

#print axioms sstep_addLeft_eq
#print axioms sstep_addLeft
#print axioms runLocal_sound
#print axioms wordEnd_sound
#print axioms home_framed_word
#print axioms home_prefix
#print axioms runLocal_home_word
#print axioms runLocal_home
#print axioms unsafe_boundary_counterexample

end SetTheory.BusyBeaver.ZFC.KLeftFrame
