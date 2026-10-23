import BusyBeaver.ZFC.KHome

/-!
Guarded append-left frames for the maintained K-family symbolic executor.
The uncompiled round13-left-frame proposal identified this interface. This
module supplies a concrete proof without changing sstep, conc, Seg, or Home.
-/
namespace SetTheory.BusyBeaver.ZFC.KLeftFrame

open KZip KRuntimeCore

def addLeft (F : List Seg) : SConf → SConf
  | (q, onl, l, r) => (q, onl, l ++ F, r)

def safeLeft : SConf → Bool
  | (_, true, [], _) => false
  | _ => true

def frameResult (F : List Seg) (z : SConf × Bool) : SConf × Bool :=
  (addLeft F z.1, z.2)

private theorem peelLeft_frame (q : Nat) (b : Bool) (a c : Nat)
    (l r F : List Seg) :
    peelLeft q b a c (l ++ F) r =
      (peelLeft q b a c l r).map (frameResult F) := by
  cases c <;> cases a <;> rfl

private theorem peelRight_frame (q : Nat) (b : Bool) (a c : Nat)
    (l r F : List Seg) :
    peelRight q b a c (l ++ F) r =
      (peelRight q b a c l r).map (frameResult F) := by
  cases c <;> cases a <;> rfl

/-- Before the frame is exposed, one symbolic step commutes with appending it.
The progress bit is preserved exactly; the frame may contain arbitrary Segs. -/
theorem sstep_frame {M : TMN} {br : Branch} {s : SConf}
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
              simp only [addLeft, List.cons_append, sstep]
              cases hm : M q b with
              | none => exact peelLeft_frame q b a c l r F
              | some z =>
                  rcases z with ⟨w, dir, q2⟩
                  cases dir with
                  | true => exact peelLeft_frame q b a c l r F
                  | false =>
                      by_cases hq : q2 = q
                      · simp only [hq, if_true, Option.map_some, frameResult, addLeft]
                      · simp only [hq, if_false]
                        exact peelLeft_frame q b a c l r F
  | false =>
      cases r with
      | nil => rfl
      | cons x r =>
          cases x with
          | bit b =>
              simp only [addLeft, sstep]
              cases hm : M q b with
              | none => rfl
              | some z =>
                  rcases z with ⟨w, dir, q2⟩
                  cases dir <;> rfl
          | run b a c =>
              simp only [addLeft, sstep]
              cases hm : M q b with
              | none => exact peelRight_frame q b a c l r F
              | some z =>
                  rcases z with ⟨w, dir, q2⟩
                  cases dir with
                  | false => exact peelRight_frame q b a c l r F
                  | true =>
                      by_cases hq : q2 = q
                      · simp only [hq, if_true, Option.map_some, frameResult, addLeft,
                          List.cons_append]
                      · simp only [hq, if_false]
                        exact peelRight_frame q b a c l r F
          | box x =>
              cases r with
              | cons y r => rfl
              | nil =>
                  simp only [addLeft, sstep]
                  cases ho : oracle q br x with
                  | some z =>
                      rcases z with ⟨q2, x2, extra⟩
                      cases extra <;> rfl
                  | none =>
                      cases hm : M q false with
                      | none => rfl
                      | some z =>
                          rcases z with ⟨w, dir, q2⟩
                          cases w <;> cases dir <;> rfl

theorem sstep_addLeft {M : TMN} {br : Branch} {s t : SConf} {m : Bool}
    (hs : safeLeft s = true) (h : sstep M br s = some (t, m)) (F : List Seg) :
    sstep M br (addLeft F s) = some (addLeft F t, m) := by
  rw [sstep_frame hs F, h]
  rfl

/-- A fixed-length local replay stops before an exposed left boundary is read.
Zero local transitions are allowed; positivity is supplied by the final Home. -/
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
                simpa [runLocal, hs, he] using h
              have hstep := sstep_sound B n (sstep_addLeft hs he F) hv
              exact hstep.1.trans (ih s' t htail)

/-- A fixed local trace, followed by the existing Home theorem, gives one
positive whole-configuration contract for every admissible symbolic frame.
The Home equation is an explicit premise, so it cannot discard a bad prefix. -/
theorem local_home_sound {M : TMN} (B : BoxLemmas M)
    (rows : KHome.Rows M) (hb : KHome.Boundary M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs)
    (F : List Seg) {k : Nat} {s t u : SConf}
    (hlocal : runLocal M br k s = some t)
    (hhome : KHome.home (addLeft F t) = some u) :
    Reach1 M (conc n vs (addLeft F s)) (conc n vs u) :=
  (runLocal_sound B n hv F k s t hlocal).trans_reach1
    (KHome.home_sound rows hb n vs hhome)

/-- An empty-left local exit lets Home scan only the caller's preserved prefix. -/
theorem home_prefix (P : List Bool) (r : List Seg) {j : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j) :
    KHome.home (addLeft (P.reverse.map Seg.bit ++ [.bit true]) (2, true, [], r)) =
      some (84, false, [.bit true], P.map Seg.bit ++ r) := by
  simp [KHome.home, addLeft, KHome.stripBlank, List.reverse_append,
    List.reverse_map, List.reverse_reverse, hs]

theorem local_prefix_sound {M : TMN} (B : BoxLemmas M)
    (rows : KHome.Rows M) (hb : KHome.Boundary M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs)
    (P : List Bool) {j k : Nat} {s : SConf} {r : List Seg}
    (hlocal : runLocal M br k s = some (2, true, [], r))
    (hscan : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j) :
    Reach1 M (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) s))
      (conc n vs (84, false, [.bit true], P.map Seg.bit ++ r)) :=
  local_home_sound B rows hb n hv _ hlocal (home_prefix P r hscan)

end SetTheory.BusyBeaver.ZFC.KLeftFrame

#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame.sstep_frame
#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame.runLocal_sound
#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame.local_prefix_sound
