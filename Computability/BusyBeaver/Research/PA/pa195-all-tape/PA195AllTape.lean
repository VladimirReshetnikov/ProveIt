import PA195LocalQuotient
import Mathlib.Logic.Function.Basic

/-! Lifting a checked local step to a tape over all integers. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195LocalQuotient

structure Configuration where
  state : Nat
  pos : Int
  tape : Int → Bool

def fullStep (rows : List Row) (c : Configuration) : Option Configuration := do
  let r ← lookup rows c.state (c.tape c.pos)
  return ⟨r.target, c.pos + (if r.right then 1 else -1), Function.update c.tape c.pos r.write⟩

/-- Any successful local step lifts to every tape agreeing on the two cells,
with all other cells unchanged. There is no restriction on the other cells. -/
theorem localStep_lift (rows : List Row) (q : Nat) (p : Int) (t : Int → Bool) (w : Window)
    (h : localStep rows ⟨q, p, t (-1), t 0⟩ = some w) :
    ∃ t' : Int → Bool,
      fullStep rows ⟨q, p, t⟩ = some ⟨w.state, w.pos, t'⟩ ∧
      t' (-1) = w.left ∧ t' 0 = w.here ∧
      ∀ i, i ≠ -1 → i ≠ 0 → t' i = t i := by
  have hp : p = -1 ∨ p = 0 := by
    by_contra hnot
    have h1 : p ≠ -1 := fun e => hnot (Or.inl e)
    have h0 : p ≠ 0 := fun e => hnot (Or.inr e)
    simp [localStep, h1, h0] at h
  rcases hp with hp | hp
  · subst p
    cases hr : lookup rows q (t (-1)) with
    | none => simp [localStep, hr] at h
    | some r =>
      have hw : w = ⟨r.target, -1 + (if r.right then 1 else -1), r.write, t 0⟩ := by
        simpa [localStep, hr] using h.symm
      subst w
      refine ⟨Function.update t (-1) r.write, ?_, ?_, ?_, ?_⟩
      · simp [fullStep, hr]
      · simp
      · simp
      · intro i hi _
        simp [hi]
  · subst p
    cases hr : lookup rows q (t 0) with
    | none => simp [localStep, hr] at h
    | some r =>
      have hw : w = ⟨r.target, 0 + (if r.right then 1 else -1), t (-1), r.write⟩ := by
        simpa [localStep, hr] using h.symm
      subst w
      refine ⟨Function.update t 0 r.write, ?_, ?_, ?_, ?_⟩
      · simp [fullStep, hr]
      · simp
      · simp
      · intro i _ hi
        simp [hi]

def fullRun (rows : List Row) : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => (fullStep rows c).bind (fullRun rows n)

/-- A successful local run lifts to arbitrary full tapes and preserves every
cell outside the window, even when its length is not bounded in the theorem. -/
theorem localRun_lift (rows : List Row) (n : Nat) (q : Nat) (p : Int) (t : Int → Bool) (w : Window)
    (h : localRun rows n ⟨q, p, t (-1), t 0⟩ = some w) :
    ∃ t' : Int → Bool,
      fullRun rows n ⟨q, p, t⟩ = some ⟨w.state, w.pos, t'⟩ ∧
      t' (-1) = w.left ∧ t' 0 = w.here ∧
      ∀ i, i ≠ -1 → i ≠ 0 → t' i = t i := by
  induction n generalizing q p t w with
  | zero =>
    simp only [localRun, Option.some.injEq] at h
    subst w
    exact ⟨t, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    cases hs : localStep rows ⟨q, p, t (-1), t 0⟩ with
    | none => simp [localRun, hs] at h
    | some v =>
      have hr : localRun rows n v = some w := by simpa [localRun, hs] using h
      obtain ⟨t', hstep, hleft, hhere, hframe⟩ := localStep_lift rows q p t v hs
      have hr' : localRun rows n ⟨v.state, v.pos, t' (-1), t' 0⟩ = some w := by
        rw [hleft, hhere]
        cases v
        exact hr
      obtain ⟨t'', hrun, hleft', hhere', hframe'⟩ := ih v.state v.pos t' w hr'
      refine ⟨t'', ?_, hleft', hhere', ?_⟩
      · simp [fullRun, hstep, hrun]
      · intro i hi1 hi0
        exact (hframe' i hi1 hi0).trans (hframe i hi1 hi0)

/-- Every one of the 28 checked cases simulates a parent transition on an
arbitrary full tape. Only the recorded history bit and current bit are assumed. -/
theorem checked_case_all_tapes (c : Case) (hc : c ∈ cases) (t : Int → Bool)
    (hleft : t (-1) = c.left) (hhere : t 0 = c.read) :
    ∃ a : Configuration,
      fullStep parent ⟨c.state, 0, t⟩ = some a ∧
      fullRun folded c.duration ⟨project c.state, 0, t⟩ =
        some ⟨project a.state, a.pos, a.tape⟩ := by
  have hall : cases.all checkCase = true := by
    rcases finite_certificate with ⟨_, _, _, _, _, _, _, _, h, _, _⟩
    exact h
  have hcase := (List.all_eq_true.mp hall) c hc
  let ini : Window := ⟨c.state, 0, c.left, c.read⟩
  let fin : Window := ⟨project c.state, 0, c.left, c.read⟩
  cases ha : localStep parent ini with
  | none => simp [checkCase, ini, ha] at hcase
  | some a =>
    cases hb : localRun folded c.duration fin with
    | none => simp [checkCase, ini, fin, ha, hb] at hcase
    | some b =>
      have hab : b = {a with state := project a.state} := by
        have h : (b == {a with state := project a.state}) = true := by
          change (match localStep parent ini, localRun folded c.duration fin with
            | some x, some y => y == {x with state := project x.state}
            | _, _ => false) = true at hcase
          rw [ha, hb] at hcase
          exact hcase
        exact beq_iff_eq.mp h
      have ha' : localStep parent ⟨c.state, 0, t (-1), t 0⟩ = some a := by
        simpa [ini, hleft, hhere] using ha
      have hb' : localRun folded c.duration ⟨project c.state, 0, t (-1), t 0⟩ = some b := by
        simpa [fin, hleft, hhere] using hb
      obtain ⟨ta, hpa, hla, hha, hfa⟩ := localStep_lift parent c.state 0 t a ha'
      obtain ⟨tb, hpb, hlb, hhb, hfb⟩ := localRun_lift folded c.duration (project c.state) 0 t b hb'
      have htb : tb = ta := by
        funext i
        by_cases hi1 : i = -1
        · subst i
          rw [hlb, hla, hab]
        · by_cases hi0 : i = 0
          · subst i
            rw [hhb, hha, hab]
          · exact (hfb i hi1 hi0).trans (hfa i hi1 hi0).symm
      subst tb
      refine ⟨⟨a.state, a.pos, ta⟩, hpa, ?_⟩
      simpa [hab] using hpb

#print axioms checked_case_all_tapes
#print axioms localStep_lift
#print axioms localRun_lift
end PA195LocalQuotient
