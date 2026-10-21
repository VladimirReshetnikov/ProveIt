import BusyBeaver.ZFC.KRuntimeCore

/-!
UNCOMPILED RESEARCH DRAFT. No new axiom or sorry is asserted here.
This factors the generic word scan and shows the precise hook into StepOk.
The concrete 18-step boundary theorem and all-n symbolic guard theorem are
remaining obligations, explicitly supplied as hypotheses below.
-/
namespace SetTheory.BusyBeaver.ZFC.KHomeProposal
open KZip KRuntimeCore

/-- Every cell is preserved and the head moves left exactly once per cell. -/
inductive LeftWord (M : TMN) : Nat → List Bool → Nat → Prop where
  | nil (q) : LeftWord M q [] q
  | cons {q q1 q2 b W} : M q b = some (b, false, q1) →
      LeftWord M q1 W q2 → LeftWord M q (b :: W) q2

/-- Arbitrary left AND right frames. This is not a leaf-site theorem. -/
theorem LeftWord.sound {M : TMN} {q q' : Nat} {W : List Bool}
    (h : LeftWord M q W q') (L R : List Bool) :
    Reach M (zl q (W ++ L) R) (zl q' L (W.reverse ++ R)) := by
  induction h generalizing L R with
  | nil q => simpa using Reach.refl M (zl q L R)
  | @cons q q1 q2 b W hrow htail ih =>
      rw [List.cons_append, zl_cons]
      have hs : step M (zc q (W ++ L) (b :: R)) = some (zl q1 (W ++ L) (b :: R)) := zL hrow
      have ht := ih L (b :: R)
      simpa [List.reverse_cons, List.append_assoc] using (Reach.of_step hs).trans ht

/-- The remaining concrete boundary proof concerns only eight left zeros,
    nine right zeros, and the final marker. It must prove positive progress. -/
def Boundary (M : TMN) : Prop :=
  ∀ R, Reach1 M (zl 2 [] (true :: R)) (zc 84 [true] R)

/-- A word-level home contract. All right-hand data are framed unchanged;
    left exterior is blank, not arbitrary. This theorem states no exact clock;
    the intended table-specific |U|+19 clock needs a counted boundary theorem. -/
theorem home_from_boundary {M : TMN} (hb : Boundary M) (U R : List Bool) (k : Nat)
    (hw : LeftWord M 2 (U ++ [true]) 2) :
    Reach1 M (zl 2 ((U ++ [true]) ++ List.replicate k false) R)
      (zc 84 [true] (U.reverse ++ R)) := by
  rw [zl_padl]
  have hs := hw.sound [] R
  have hs' : Reach M (zl 2 (U ++ [true]) R) (zl 2 [] (true :: (U.reverse ++ R))) := by
    simpa [List.reverse_append, List.append_assoc] using hs
  exact hs'.trans_reach1 (hb (U.reverse ++ R))

/-- Small wrapper only; the old symbolic interpreter remains the fallback. -/
def stepWith (shortcut : SConf → Option SConf) (M : TMN) (br : Branch) (s : SConf) :
    Option (SConf × Bool) :=
  match shortcut s with
  | some t => some (t, true)
  | none => sstep M br s

/-- The extra shortcut proof is entirely box-independent and quantifies all n/vs.
    The existing register engine assumptions are used only by the fallback. -/
theorem stepWith_sound {M : TMN} (B : BoxLemmas M) (shortcut : SConf → Option SConf)
    (hshortcut : ∀ n vs s t, shortcut s = some t → Reach1 M (conc n vs s) (conc n vs t))
    {br : Branch} {s t : SConf} {m : Bool} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (h : stepWith shortcut M br s = some (t, m)) :
    StepOk M n vs s t m := by
  unfold stepWith at h
  cases hs : shortcut s with
  | none =>
      rw [hs] at h
      exact sstep_sound B n h hv
  | some u =>
      rw [hs] at h
      cases h
      have hr := hshortcut n vs s u hs
      exact ⟨hr.reach, fun _ => hr⟩

end SetTheory.BusyBeaver.ZFC.KHomeProposal
