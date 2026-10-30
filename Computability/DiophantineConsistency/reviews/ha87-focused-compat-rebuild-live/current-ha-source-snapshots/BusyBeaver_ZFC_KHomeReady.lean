import BusyBeaver.ZFC.KHome
import BusyBeaver.ZFC.KZipTape

/-! A decidable table certificate for the Home shortcut. Every theorem is
uniform in M. Unsupported tables use the original symbolic stepper unchanged. -/
namespace SetTheory.BusyBeaver.ZFC.KHomeReady
open KZip KRuntimeCore

private def cells : FramedWindow.Cells :=
  [(1, true), (0, false), (-1, false), (-2, false), (-3, false),
   (-4, false), (-5, false), (-6, false), (-7, false), (-8, false)]

def rowsCheck (M : TMN) : Bool :=
  (List.range 8).all (fun i => decide (M (KHome.state i) true = some (true, false, 2))) &&
  (List.range 7).all (fun i => decide (M (KHome.state i) false = some (false, false, KHome.state (i + 1))))

def ready (M : TMN) : Bool :=
  rowsCheck M && FramedWindow.check (KZipTape.table M) 18 2 0 cells 84 2

private theorem rowsCheck_sound {M : TMN} (h : rowsCheck M = true) : KHome.Rows M := by
  simp only [rowsCheck, Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · intro i hi
    exact of_decide_eq_true (h.1 i (List.mem_range.mpr hi))
  · intro i hi
    exact of_decide_eq_true (h.2 i (List.mem_range.mpr (by omega)))

private theorem overlay_eq (xs : FramedWindow.Cells) (t : FramedWindow.Tape)
    (h : ∀ p ∈ xs, t p.1 = p.2) : FramedWindow.overlay xs t = t := by
  funext i
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    by_cases hi : i = p.1
    · subst i
      simpa [FramedWindow.overlay, FramedWindow.lookup] using (h p (by simp)).symm
    · have ht := ih (fun p hp => h p (by simp [hp]))
      simpa only [FramedWindow.overlay, FramedWindow.lookup, if_neg hi] using ht

/-- The checked window returns across the blank-left boundary on every right frame. -/
private theorem boundary_of_check {M : TMN}
    (hc : FramedWindow.check (KZipTape.table M) 18 2 0 cells 84 2 = true) : KHome.Boundary M := by
  intro R
  let s := zc 2 [] (false :: true :: R)
  have hm : FramedWindow.overlay cells (KZipTape.tape s) = KZipTape.tape s := by
    apply overlay_eq
    intro p hp
    simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [KZipTape.tape, s, zc, trim_cons] <;> rfl
  have hs := FramedWindow.arbitrary_tape (KZipTape.table M) 18 2 0 cells 84 2
    hc (KZipTape.tape s) hm
  have he : KZipTape.Rel ⟨84, 2, KZipTape.tape s⟩ (zc 84 [true] R) := by
    simpa [KZipTape.full, s, zc, trim_cons, trim_trim] using
      KZipTape.rel_right (KZipTape.rel_right (KZipTape.rel_full s) 2) 84
  have hr := KZipTape.run_reflect (KZipTape.rel_full s) he
    (by exact ⟨trim_trim _, trim_trim _⟩) ⟨trim_trim _, trim_trim _⟩ hs
  exact ⟨17, by simpa [s, zl] using hr⟩

theorem ready_sound {M : TMN} (h : ready M = true) : KHome.Rows M ∧ KHome.Boundary M := by
  simp only [ready, Bool.and_eq_true] at h
  exact ⟨rowsCheck_sound h.1, boundary_of_check h.2⟩

/-- A positive Home shortcut, otherwise exactly the old abstract step. -/
def homeStep (M : TMN) (br : Branch) (s : SConf) : Option (SConf × Bool) :=
  match KHome.home s with
  | some t => some (t, true)
  | none => sstep M br s

/-- This decision is outside the executor recursion. -/
def stepper (M : TMN) (br : Branch) : SConf → Option (SConf × Bool) :=
  if ready M then homeStep M br else sstep M br

theorem stepper_sound {M : TMN} (B : BoxLemmas M) {br : Branch}
    (n : Nat) {vs : List Nat} (hv : Valid br vs) {s t : SConf} {m : Bool}
    (h : stepper M br s = some (t, m)) : StepOk M n vs s t m := by
  by_cases hr : ready M = true
  · obtain ⟨rows, hb⟩ := ready_sound hr
    simp only [stepper, hr, if_true] at h
    cases hh : KHome.home s with
    | none => exact sstep_sound B n (by simpa [homeStep, hh] using h) hv
    | some u =>
      simp only [homeStep, hh, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp := KHome.home_sound rows hb n vs hh
      exact ⟨hp.reach, fun _ => hp⟩
  · exact sstep_sound B n (by simpa [stepper, hr] using h) hv

def exec (M : TMN) (br : Branch) (tgt : SConf → Bool) : Nat → SConf → Bool → Option SConf :=
  execWith (stepper M br) tgt

theorem exec_sound {M : TMN} (B : BoxLemmas M) {br : Branch} {tgt : SConf → Bool}
    (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    ∀ (f : Nat) (s : SConf) (m0 : Bool) (s' : SConf), exec M br tgt f s m0 = some s' →
      tgt s' = true ∧ Reach M (conc n vs s) (conc n vs s') ∧
        (m0 = false → Reach1 M (conc n vs s) (conc n vs s')) :=
  execWith_sound n vs (fun _ _ _ h => stepper_sound B n hv h)

#print axioms ready_sound
#print axioms exec_sound
end SetTheory.BusyBeaver.ZFC.KHomeReady
