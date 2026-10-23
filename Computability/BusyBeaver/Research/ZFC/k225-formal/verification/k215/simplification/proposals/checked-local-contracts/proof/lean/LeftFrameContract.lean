import BusyBeaver.ZFC.KHome

/-!
Guarded left-frame lifting for the unchanged K-family symbolic executor.

This is a checked-realization candidate for the previously uncompiled contract
in verification/k215/simplification/proposals/round13-left-frame/runtime/
LeftFrameContract.lean.proposal. The decomposition and 35-template discovery
belong to that earlier proposal. This file supplies explicit algebraic proofs,
the finite-run lifting theorem, and a counterexample to deleting the guard.

No transition, segment interpretation, normalization, or machine is changed.
The new finite-run theorem concludes Reach. A final positive Home theorem is
still needed to obtain Reach1 for the entire control instruction.
-/

namespace SetTheory.BusyBeaver.ZFC.KLeftFrame

open KZip KRuntimeCore

def addLeft (F : List Seg) : SConf → SConf
  | (q, onl, l, r) => (q, onl, l ++ F, r)

def safeLeft : SConf → Bool
  | (_, true, [], _) => false
  | _ => true

def frameResult (F : List Seg) (x : SConf × Bool) : SConf × Bool :=
  (addLeft F x.1, x.2)

private theorem peelLeft_frame (q : Nat) (b : Bool) (a c : Nat)
    (l r F : List Seg) :
    peelLeft q b a c (l ++ F) r = (peelLeft q b a c l r).map (frameResult F) := by
  cases c <;> cases a <;> rfl

private theorem peelRight_frame (q : Nat) (b : Bool) (a c : Nat)
    (l r F : List Seg) :
    peelRight q b a c (l ++ F) r = (peelRight q b a c l r).map (frameResult F) := by
  cases c <;> cases a <;> rfl

/-- Guarded naturality of the exact step function, including its progress flag. -/
theorem sstep_addLeft_map {M : TMN} {br : Branch} {s : SConf}
    (hs : safeLeft s = true) (F : List Seg) :
    sstep M br (addLeft F s) = (sstep M br s).map (frameResult F) := by
  rcases s with ⟨q, onl, l, r⟩
  cases onl with
  | true =>
      cases l with
      | nil => simp [safeLeft] at hs
      | cons x l =>
          cases x with
          | bit b => rfl
          | box x => rfl
          | run b a c =>
              cases hM : M q b with
              | none => simpa [addLeft, sstep, hM] using peelLeft_frame q b a c l r F
              | some row =>
                  rcases row with ⟨w, dir, q2⟩
                  cases dir with
                  | true => simpa [addLeft, sstep, hM] using peelLeft_frame q b a c l r F
                  | false =>
                      by_cases heq : q2 = q
                      · simp [addLeft, sstep, hM, heq, frameResult]
                      · simpa [addLeft, sstep, hM, heq] using peelLeft_frame q b a c l r F
  | false =>
      cases r with
      | nil => rfl
      | cons x r =>
          cases x with
          | bit b =>
              cases hM : M q b with
              | none => simp [addLeft, sstep, hM]
              | some row =>
                  rcases row with ⟨w, dir, q2⟩
                  cases dir <;> simp [addLeft, sstep, hM, frameResult]
          | run b a c =>
              cases hM : M q b with
              | none => simpa [addLeft, sstep, hM] using peelRight_frame q b a c l r F
              | some row =>
                  rcases row with ⟨w, dir, q2⟩
                  cases dir with
                  | false => simpa [addLeft, sstep, hM] using peelRight_frame q b a c l r F
                  | true =>
                      by_cases heq : q2 = q
                      · simp [addLeft, sstep, hM, heq, frameResult]
                      · simpa [addLeft, sstep, hM, heq] using peelRight_frame q b a c l r F
          | box x =>
              cases r with
              | cons y r => rfl
              | nil =>
                  cases ho : oracle q br x with
                  | some row =>
                      rcases row with ⟨q2, x2, extra⟩
                      cases extra <;> simp [addLeft, sstep, ho, frameResult]
                  | none =>
                      cases hM : M q false with
                      | none => simp [addLeft, sstep, ho, hM]
                      | some row =>
                          rcases row with ⟨w, dir, q2⟩
                          cases w <;> cases dir <;> simp [addLeft, sstep, ho, hM, frameResult]

theorem sstep_addLeft {M : TMN} {br : Branch} {s t : SConf} {m : Bool}
    (hs : safeLeft s = true) (h : sstep M br s = some (t, m)) (F : List Seg) :
    sstep M br (addLeft F s) = some (addLeft F t, m) := by
  rw [sstep_addLeft_map hs F, h]
  rfl

/-- A local trace may finish at an unsafe boundary, but may not step beyond it. -/
def runLocal (M : TMN) (br : Branch) : Nat → SConf → Option SConf
  | 0, s => some s
  | k + 1, s =>
      if safeLeft s then do
        let (t, _) ← sstep M br s
        runLocal M br k t
      else none

/-- The unchanged symbolic semantics lifts the entire successful local trace
to every left frame, gap parameter, and register file satisfying Valid. -/
theorem runLocal_sound {M : TMN} (B : BoxLemmas M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs) (F : List Seg) :
    ∀ k s t, runLocal M br k s = some t →
      Reach M (conc n vs (addLeft F s)) (conc n vs (addLeft F t)) := by
  intro k
  induction k with
  | zero =>
      intro s t h
      simp only [runLocal, Option.some.injEq] at h
      subst t
      exact .refl _ _
  | succ k ih =>
      intro s t h
      cases hs : safeLeft s with
      | false => simp [runLocal, hs] at h
      | true =>
          cases he : sstep M br s with
          | none => simp [runLocal, hs, he] at h
          | some pair =>
              rcases pair with ⟨s', m⟩
              have htail : runLocal M br k s' = some t := by
                simpa only [runLocal, hs, if_true, he, Option.bind_eq_bind, Option.bind_some] using h
              have hstep := sstep_sound B n (sstep_addLeft hs he F) hv
              exact hstep.1.trans (ih s' t htail)

private theorem flat_bits_frame (n : Nat) (vs : List Nat) (P : List Bool) :
    flat n vs (P.map .bit) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.map_cons, flat_cons, segList, ih]; rfl

/-- Use the existing Home theorem on the entire preserved prefix. This does not
assume the prefix is nonempty or ends in one. -/
theorem home_prefix {M : TMN} (rows : KHome.Rows M) (hb : KHome.Boundary M)
    (P R : List Bool) (blanks : Nat) {k : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k) :
    Reach1 M (zl 2 ((P.reverse ++ [true]) ++ List.replicate blanks false) R)
      (zc 84 [true] (P ++ R)) := by
  obtain ⟨j, _, hj, hword⟩ := KHome.scanBound_sound rows 0 [] hs
    (by decide : 0 < 8) (Nat.le_refl 0)
  have hw : KHome.LeftWord M 2 (P.reverse ++ [true]) 2 := by
    have hp : KHome.LeftWord M 2 P.reverse (KHome.state j) := by
      simpa only [flat_bits_frame, KHome.state] using hword
    exact hp.append (.cons (rows.reset j hj) (.nil _))
  simpa only [List.reverse_reverse] using KHome.home_word hb P.reverse R blanks hw

/-- A guarded local trace followed by Home gives a positive whole-tape contract.
All prefix cells, all gap lengths and all admissible register values are quantified. -/
theorem local_home_sound {M : TMN} (B : BoxLemmas M)
    (rows : KHome.Rows M) (hb : KHome.Boundary M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs)
    (P : List Bool) {k j : Nat} {s : SConf} {R : List Seg}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j)
    (hr : runLocal M br k s = some (2, true, [], R)) :
    Reach1 M
      (conc n vs (addLeft (P.reverse.map .bit ++ [.bit true]) s))
      (zc 84 [true] (P ++ flat n vs R)) := by
  have hlocal := runLocal_sound B n hv (P.reverse.map .bit ++ [.bit true]) k s _ hr
  apply hlocal.trans_reach1
  have hh := home_prefix rows hb P (flat n vs R) 0 hs
  have hf : flat n vs (P.reverse.map .bit ++ [.bit true]) = P.reverse ++ [true] := by
    rw [show flat n vs (P.reverse.map .bit ++ [.bit true]) =
      flat n vs (P.reverse.map .bit) ++ flat n vs [.bit true] from by simp [flat]]
    rw [flat_bits_frame]
    rfl
  simpa only [addLeft, List.nil_append, conc, hf, List.replicate_zero, List.append_nil] using hh

/-- With empty explicit left side the original executor inserts a blank;
appending a nonblank frame changes which cell is exposed. The guard is necessary. -/
theorem unguarded_frame_counterexample (M : TMN) (br : Branch) :
    sstep M br (addLeft [.bit true] (0, true, [], [])) ≠
      (sstep M br (0, true, [], [])).map (frameResult [.bit true]) := by
  simp [sstep, addLeft, frameResult]

theorem rejects_unsafe_start (M : TMN) (br : Branch) (q k : Nat) (r : List Seg) :
    runLocal M br (k + 1) (q, true, [], r) = none := rfl

theorem accepts_terminal_boundary (M : TMN) (br : Branch) (q : Nat) (r : List Seg) :
    runLocal M br 0 (q, true, [], r) = some (q, true, [], r) := rfl

/-- Unframed equality after dropping trailing blanks cannot be framed.
The same normalized unframed pair becomes two different concrete tapes. -/
theorem normalization_frame_counterexample :
    sMatches (0, false, [], []) (0, false, [.bit false], []) = true ∧
      conc 0 [] (addLeft [.bit true] (0, false, [], [])) ≠
        conc 0 [] (addLeft [.bit true] (0, false, [.bit false], [])) := by
  decide

#print axioms sstep_addLeft_map
#print axioms sstep_addLeft
#print axioms runLocal_sound
#print axioms home_prefix
#print axioms local_home_sound
#print axioms unguarded_frame_counterexample
#print axioms normalization_frame_counterexample

end SetTheory.BusyBeaver.ZFC.KLeftFrame
