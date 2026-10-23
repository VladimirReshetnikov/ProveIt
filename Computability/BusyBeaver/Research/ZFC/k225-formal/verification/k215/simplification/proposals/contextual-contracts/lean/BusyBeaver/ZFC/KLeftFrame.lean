import BusyBeaver.ZFC.KHome

/-!
A guarded frame rule for the maintained K-family symbolic executor.
The appended left fragment is arbitrary, including symbolic register boxes.
The guard rejects the sole branch that invents a blank for an empty left side.
Local execution stops before that boundary; the existing Home theorem then
supplies positive progress and finishes the whole-tape contract.

This completes the generic obligations proposed in round13-left-frame.
-/
namespace SetTheory.BusyBeaver.ZFC.KLeftFrame
open KZip KRuntimeCore

def addLeft (F : List Seg) : SConf → SConf
  | (q, onl, l, r) => (q, onl, l ++ F, r)

def safeLeft : SConf → Bool
  | (_, true, [], _) => false
  | _ => true

def mapStep (F : List Seg) : Option (SConf × Bool) → Option (SConf × Bool) :=
  Option.map fun (s, moved) => (addLeft F s, moved)

theorem peelLeft_addLeft (F l r : List Seg) (q : Nat) (b : Bool) (a c : Nat) :
    peelLeft q b a c (l ++ F) r = mapStep F (peelLeft q b a c l r) := by
  cases c <;> cases a <;> rfl

theorem peelRight_addLeft (F l r : List Seg) (q : Nat) (b : Bool) (a c : Nat) :
    peelRight q b a c (l ++ F) r = mapStep F (peelRight q b a c l r) := by
  cases c <;> cases a <;> rfl

/-- On guarded inputs even failure commutes with append-left framing. -/
theorem sstep_natural (M : TMN) (br : Branch) (F : List Seg) (s : SConf)
    (hs : safeLeft s = true) :
    sstep M br (addLeft F s) = mapStep F (sstep M br s) := by
  obtain ⟨q, onl, l, r⟩ := s
  cases onl with
  | true =>
    cases l with
    | nil => cases hs
    | cons x l =>
      cases x with
      | bit x => rfl
      | box x => rfl
      | run b a c =>
        simp only [addLeft, List.cons_append, sstep]
        cases h : M q b with
        | none => exact peelLeft_addLeft F l r q b a c
        | some row =>
          obtain ⟨w, d, q2⟩ := row
          cases d with
          | true => exact peelLeft_addLeft F l r q b a c
          | false =>
            by_cases hq : q2 = q
            · simp only [hq, if_true]; rfl
            · simpa only [hq, if_false] using peelLeft_addLeft F l r q b a c
  | false =>
    cases r with
    | nil => rfl
    | cons x r =>
      cases x with
      | bit x =>
        simp only [addLeft, sstep]
        cases h : M q x with
        | none => rfl
        | some row =>
          obtain ⟨w, d, q2⟩ := row
          cases d <;> rfl
      | run b a c =>
        simp only [addLeft, sstep]
        cases h : M q b with
        | none => exact peelRight_addLeft F l r q b a c
        | some row =>
          obtain ⟨w, d, q2⟩ := row
          cases d with
          | false => exact peelRight_addLeft F l r q b a c
          | true =>
            by_cases hq : q2 = q
            · simp only [hq, if_true]; rfl
            · simpa only [hq, if_false] using peelRight_addLeft F l r q b a c
      | box x =>
        cases r with
        | cons y r => rfl
        | nil =>
          simp only [addLeft, sstep]
          cases h : oracle q br x with
          | some row =>
            obtain ⟨q2, x2, extra⟩ := row
            cases extra <;> rfl
          | none =>
            cases h : M q false with
            | none => rfl
            | some row =>
              obtain ⟨w, d, q2⟩ := row
              cases w <;> cases d <;> rfl

theorem sstep_addLeft {M : TMN} {br : Branch} {s t : SConf} {m : Bool}
    (hs : safeLeft s = true) (h : sstep M br s = some (t, m)) (F : List Seg) :
    sstep M br (addLeft F s) = some (addLeft F t, m) := by
  rw [sstep_natural M br F s hs, h]
  rfl

/-- Dropping the guard would be false even for a transitionless table. -/
theorem unsafe_frame_counterexample :
    sstep (fun _ _ => none) none (addLeft [.bit true] (0, true, [], [])) ≠
      mapStep [.bit true] (sstep (fun _ _ => none) none (0, true, [], [])) := by
  decide

/-- A fixed-length local replay may end at the boundary, but cannot cross it. -/
def runLocal (M : TMN) (br : Branch) : Nat → SConf → Option SConf
  | 0, s => some s
  | k + 1, s =>
    if safeLeft s then do
      let (t, _) ← sstep M br s
      runLocal M br k t
    else none

theorem runLocal_sound {M : TMN} (B : BoxLemmas M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs) (F : List Seg) :
    ∀ k s t, runLocal M br k s = some t →
      Reach M (conc n vs (addLeft F s)) (conc n vs (addLeft F t)) := by
  intro k
  induction k with
  | zero =>
    intro s t h
    cases h
    exact .refl _ _
  | succ k ih =>
    intro s t h
    cases hs : safeLeft s with
    | false => simp [runLocal, hs] at h
    | true =>
      cases he : sstep M br s with
      | none => simp [runLocal, hs, he] at h
      | some pair =>
        obtain ⟨s', m⟩ := pair
        have ht : runLocal M br k s' = some t := by
          simpa [runLocal, hs, he] using h
        exact (sstep_sound B n (sstep_addLeft hs he F) hv).1.trans (ih s' t ht)

theorem flat_bits (n : Nat) (vs : List Nat) (P : List Bool) :
    flat n vs (P.map Seg.bit) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.map_cons, flat_cons, segList, ih]; rfl

theorem flat_append (n : Nat) (vs : List Nat) (L R : List Seg) :
    flat n vs (L ++ R) = flat n vs L ++ flat n vs R := by
  simp [flat, List.flatMap_append]

/-- Home scans the caller's prefix and marker after the local left list empties.
No restriction on the last prefix bit is imposed. Far-left exterior is blank.
-/
theorem home_prefix {M : TMN} (rows : KHome.Rows M) (hb : KHome.Boundary M)
    (P R : List Bool) (blanks : Nat) {k : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k) :
    Reach1 M (zl 2 ((P.reverse ++ [true]) ++ List.replicate blanks false) R)
      (zc 84 [true] (P ++ R)) := by
  obtain ⟨j, _, hj, hword⟩ := KHome.scanBound_sound rows 0 [] hs
    (by decide : 0 < 8) (Nat.le_refl 0)
  have hw : KHome.LeftWord M 2 (P.reverse ++ [true]) 2 := by
    have hp : KHome.LeftWord M 2 P.reverse (KHome.state j) := by
      simpa only [flat_bits, KHome.state] using hword
    exact hp.append (.cons (rows.reset j hj) (.nil _))
  simpa only [List.reverse_reverse] using KHome.home_word hb P.reverse R blanks hw

/-- A single local certificate gives a whole-tape contract for every safe prefix,
every gap parameter, and every valid register file. Positive progress comes from Home.
-/
theorem local_home {M : TMN} (B : BoxLemmas M) (rows : KHome.Rows M)
    (hb : KHome.Boundary M) {br : Branch} {steps : Nat} {s : SConf} {R : List Seg}
    (hr : runLocal M br steps s = some (2, true, [], R))
    (P : List Bool) {k : Nat}
    (hp : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k)
    (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    Reach1 M (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) s))
      (zc 84 [true] (P ++ flat n vs R)) := by
  have hr' := runLocal_sound B n hv (P.reverse.map Seg.bit ++ [.bit true]) steps s _ hr
  have hh := home_prefix rows hb P (flat n vs R) 0 hp
  apply hr'.trans_reach1
  simpa only [addLeft, List.nil_append, conc, flat_append, flat_bits,
    flat_cons, segList, flat_nil, List.append_nil, List.replicate_zero] using hh

#print axioms sstep_natural
#print axioms unsafe_frame_counterexample
#print axioms runLocal_sound
#print axioms home_prefix
#print axioms local_home

end SetTheory.BusyBeaver.ZFC.KLeftFrame
