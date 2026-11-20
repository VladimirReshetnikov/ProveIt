import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas

/-! The rational core of the minimax computation on the unit interval.
The inequalities involve only rational arithmetic. Completion and reification
in the object language are described in the paper. -/
namespace Precision.Variational
abbrev Q := ℚ

def err (t : Q) := (1-t)^2/2

def best (t x : Q) : Q :=
  err t + (if x ≤ t then x*x else 2*t*x-t*t)

def feasible (L : Q) (f : Q → Q) : Prop :=
  (∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ f x ∧ f x ≤ 1) ∧
  (∀ x y, 0 ≤ x → x ≤ y → y ≤ 1 →
      -(L*(y-x)) ≤ f y-f x ∧ f y-f x ≤ L*(y-x))

def approximates (e : Q) (f : Q → Q) : Prop :=
  ∀ x, 0 ≤ x → x ≤ 1 → -e ≤ f x-x*x ∧ f x-x*x ≤ e

private theorem increments {t x y : Q} (ht : 0 ≤ t) (hx : 0 ≤ x) (hxy : x ≤ y) :
    0 ≤ best t y - best t x ∧ best t y - best t x ≤ (2*t)*(y-x) := by
  by_cases hy : y ≤ t
  · have hxt : x ≤ t := le_trans hxy hy
    simp only [best, if_pos hy, if_pos hxt]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ y+x by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2*t-y-x by linarith)]
  · by_cases hxt : x ≤ t
    · simp only [best, if_neg hy, if_pos hxt]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hxt) (show 0 ≤ t+x by linarith),
                    mul_nonneg ht (show 0 ≤ y-t by linarith)]
      · nlinarith [sq_nonneg (t-x)]
    · simp only [best, if_neg hy, if_neg hxt]
      constructor
      · nlinarith [mul_nonneg ht (show 0 ≤ y-x by linarith)]
      · linarith

theorem best_feasible {t : Q} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    feasible (2*t) (best t) := by
  constructor
  · intro x hx hx1
    have lo := (increments ht (x := 0) (y := x) (le_refl _) hx).1
    have hi := (increments ht hx hx1).1
    have hzero : best t 0 = err t := by simp [best, ht]
    have hone : best t 1 = 1-err t := by
      by_cases h : 1 ≤ t
      · have eqt : t = 1 := le_antisymm ht1 h
        subst t
        norm_num [best, err]
      · simp only [best, if_neg h, err]
        ring
    rw [hzero] at lo
    rw [hone] at hi
    have he : 0 ≤ err t := by unfold err; nlinarith [sq_nonneg (1-t)]
    constructor <;> linarith
  · intro x y hx hxy _
    obtain ⟨hlo, hhi⟩ := increments ht hx hxy
    exact ⟨by linarith, hhi⟩

theorem best_attains {t : Q} (_ht : 0 ≤ t) (ht1 : t ≤ 1) :
    approximates (err t) (best t) := by
  intro x _ hx
  by_cases h : x ≤ t
  · simp only [best, if_pos h, err]
    constructor <;> nlinarith [sq_nonneg (1-t)]
  · simp only [best, if_neg h, err]
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ 1-x by linarith) (show 0 ≤ 1+x-2*t by linarith)]
    · nlinarith [sq_nonneg (x-t)]

theorem lower_bound {t e : Q} {f : Q → Q} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : feasible (2*t) f) (her : approximates e f) : err t ≤ e := by
  have hmove := (h.2 t 1 ht ht1 (le_refl _)).2
  have hleft := (her t ht ht1).2
  have hright := (her 1 (by decide) (le_refl _)).1
  unfold err
  nlinarith

theorem minimax {t : Q} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (feasible (2*t) (best t) ∧ approximates (err t) (best t)) ∧
    ∀ (f : Q → Q) (e : Q), feasible (2*t) f → approximates e f → err t ≤ e :=
  ⟨⟨best_feasible ht ht1, best_attains ht ht1⟩, fun _ _ => lower_bound ht ht1⟩

#print axioms minimax
end Precision.Variational
