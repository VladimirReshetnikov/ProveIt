import Arithmetic

namespace SiegelIPRA

def QuarticSeven (x y : Int) : Prop :=
  y*y = x*x*x*x + 7*x*x + 1

/-- Complete classification, not merely a computation below a guessed cutoff. -/
theorem quartic_seven_complete (x y : Int) :
    QuarticSeven x y ↔
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      ((x = 1 ∨ x = -1) ∧ (y = 3 ∨ y = -3)) := by
  constructor
  · intro h
    have hb := quartic_bounds 7 1 x y (by decide) h
    have hxlow : -(x.natAbs : Int) ≤ x := by
      have hn : -x ≤ ((-x).natAbs : Int) := Int.le_natAbs
      simp only [Int.natAbs_neg] at hn
      omega
    have hxhigh : x ≤ (x.natAbs : Int) := Int.le_natAbs
    have hxn : x.natAbs ≤ 2 := by
      by_cases hx : x.natAbs ≤ 2
      · exact hx
      · have hc : (3 : Int) ≤ (x.natAbs : Int) := by omega
        have hs := Int.mul_self_le_mul_self (by decide : (0 : Int) ≤ 3) hc
        have he : (x.natAbs : Int)*(x.natAbs : Int)=x*x := by
          simpa only [← Int.natCast_mul] using (Int.natAbs_mul_self (a := x))
        rw [he] at hs
        simp only [Int.reduceMul, Int.reduceSub] at hb
        simp only [Int.mul_assoc] at hb
        omega
    have hxn' : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by omega
    have hylo : -(y.natAbs : Int) ≤ y := by
      have hn : -y ≤ ((-y).natAbs : Int) := Int.le_natAbs
      simp only [Int.natAbs_neg] at hn
      omega
    have hyhi : y ≤ (y.natAbs : Int) := Int.le_natAbs
    have hyn : -11 ≤ y ∧ y ≤ 11 := by
      simp only [Int.reduceMul, Int.reduceSub] at hb
      constructor <;> omega
    have hyn' : y = (-11) ∨ y = (-10) ∨ y = (-9) ∨ y = (-8) ∨ y = (-7) ∨ y = (-6) ∨ y = (-5) ∨ y = (-4) ∨ y = (-3) ∨ y = (-2) ∨ y = (-1) ∨ y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
    rcases hxn' with hx | hx | hx | hx | hx <;> subst x <;>
      rcases hyn' with hy0 | hy1 | hy2 | hy3 | hy4 | hy5 | hy6 | hy7 | hy8 | hy9 | hy10 | hy11 | hy12 | hy13 | hy14 | hy15 | hy16 | hy17 | hy18 | hy19 | hy20 | hy21 | hy22 <;>
      subst y <;> simp_all [QuarticSeven]
  · intro h
    rcases h with h | h
    · rcases h with ⟨hx,hy | hy⟩ <;> subst x <;> subst y <;> unfold QuarticSeven <;> decide
    · rcases h with ⟨hx | hx,hy | hy⟩ <;> subst x <;> subst y <;> unfold QuarticSeven <;> decide

end SiegelIPRA
