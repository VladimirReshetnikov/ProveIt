import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.Order.Basic

/-! Negative main-root orientation in one restricted 85-gap template. -/

theorem cubic_modulus_general (X Y q A : ℤ) (hq : q ∣ Y)
    (hdiv : (4*Y*(X+1)+3) ∣ Y*q^2*A) :
    (4*Y*(X+1)+3) ∣ 27*A := by
  obtain ⟨v,hv⟩ := hq
  obtain ⟨z,hz⟩ := hdiv
  let H := 4*Y*(X+1)+3
  let d := 4*Y*(X+1)
  have hY3 : Y^3*A = H*(v^2*z) := by
    calc
      Y^3*A = (Y*q^2*A)*v^2 := by rw [hv]; ring
      _ = H*z*v^2 := by rw [hz]
      _ = H*(v^2*z) := by ring
  refine ⟨(d^2-3*d+9)*A-64*(X+1)^3*v^2*z, ?_⟩
  calc
    27*A = (H*(d^2-3*d+9)-d^3)*A := by dsimp [H,d]; ring
    _ = H*((d^2-3*d+9)*A)-64*(X+1)^3*(Y^3*A) := by dsimp [d]; ring
    _ = H*((d^2-3*d+9)*A)-64*(X+1)^3*(H*(v^2*z)) := by rw [hY3]
    _ = H*((d^2-3*d+9)*A-64*(X+1)^3*v^2*z) := by ring

theorem negative_root_modulus (X Y q gamma B : ℤ)
    (hroot :
      -(Y*q^2) * (4*(Y*(X+1)+2)^3 - 3*(Y*(X+1)+2)) =
      (Y*q^2) * (X + (Y*(X+1))*(4*((Y*(X+1))^2+4*(Y*(X+1))+3)+3)) +
      (4*Y*(X+1)+3) * ((Y*q^2)*gamma+B)) :
    (4*Y*(X+1)+3) ∣ Y*q^2*(8*X+1) := by
  let a := Y*(X+1)
  let H := 4*a+3
  let U := Y*q^2
  let c := 4*(a^2+4*a+3)+3
  let S := 4*(a+2)^3-3*(a+2)
  let P := 16*a^2+68*a+69
  have hr : -U*S=U*(X+a*c)+H*(U*gamma+B) := by
    dsimp [a,H,U,c,S]
    ring_nf at hroot ⊢
    exact hroot
  have hs : 8*(S+(X+a*c)) = H*P+(8*X+1) := by dsimp [S,c,H,P]; ring
  refine ⟨-8*(U*gamma+B)-U*P, ?_⟩
  have hs' : 8*X+1 = 8*(S+(X+a*c))-H*P := by rw [hs]; ring
  have hsum : U*S+U*(X+a*c) = -H*(U*gamma+B) := by nlinarith only [hr]
  have ht : U*(8*X+1) = H*(-8*(U*gamma+B)-U*P) := by
    calc
      U*(8*X+1) = 8*U*(S+(X+a*c))-U*H*P := by rw [hs']; ring
      _ = 8*(U*S+U*(X+a*c))-U*H*P := by ring
      _ = -8*H*(U*gamma+B)-U*H*P := by rw [hsum]; ring
      _ = H*(-8*(U*gamma+B)-U*P) := by ring
  simpa only [U,H,a,mul_assoc] using ht

/-- The negative-oriented template forces `Y<54`; hence no claim about the
remaining small-Y cases, arbitrary signs, or arbitrary 85 zeros. -/
theorem negative_template_Y_lt_54 (X Y q gamma B : ℤ)
    (hX : 1 ≤ X) (hq : q ∣ Y)
    (hroot :
      -(Y*q^2) * (4*(Y*(X+1)+2)^3 - 3*(Y*(X+1)+2)) =
      (Y*q^2) * (X + (Y*(X+1))*(4*((Y*(X+1))^2+4*(Y*(X+1))+3)+3)) +
      (4*Y*(X+1)+3) * ((Y*q^2)*gamma+B)) : Y < 54 := by
  have hdiv := cubic_modulus_general X Y q (8*X+1) hq
    (negative_root_modulus X Y q gamma B hroot)
  by_contra hn
  have hy : 54 ≤ Y := by omega
  have hp : 0 ≤ (Y-54)*(X+1) := mul_nonneg (by omega) (by omega)
  have hnonneg : 0 ≤ 27*(8*X+1) := by omega
  have hlt : 27*(8*X+1) < 4*Y*(X+1)+3 := by nlinarith
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hdiv
  omega

/-- The negative-oriented special template is impossible when the first-factor
constraint q³∣Y and the positive eta condition are also supplied. -/
theorem exclude_negative_template (X Y q eta gamma B : ℤ)
    (hX : 1 ≤ X) (hY : 8 ≤ Y) (hq : 2 ≤ q) (hEta : 0 < eta)
    (hq3 : q^3 ∣ Y)
    (heta : eta = 4*((Y*(X+1))^2+4*Y*(X+1)+3)+3 - Y*(8*X*Y^2+4))
    (hroot :
      -(Y*q^2) * (4*(Y*(X+1)+2)^3 - 3*(Y*(X+1)+2)) =
      (Y*q^2) * (X + (Y*(X+1))*(4*((Y*(X+1))^2+4*(Y*(X+1))+3)+3)) +
      (4*Y*(X+1)+3) * ((Y*q^2)*gamma+B)) : False := by
  have hqY : q ∣ Y := by
    obtain ⟨v,hv⟩ := hq3
    refine ⟨q^2*v, ?_⟩
    rw [hv]
    ring
  have hYlt : Y < 54 := negative_template_Y_lt_54 X Y q gamma B hX hqY hroot
  have hq3le : q^3 ≤ Y := Int.le_of_dvd (by omega) hq3
  have hqle : q ≤ 3 := by
    by_contra hn
    have h4 : 4 ≤ q := by omega
    have hp : 0 ≤ (q-4)*(q^2+4*q+16) := mul_nonneg (by omega) (by nlinarith [sq_nonneg q])
    nlinarith
  let H := 4*Y*(X+1)+3
  have hH : 0 < H := by dsimp [H]; nlinarith
  have hd := cubic_modulus_general X Y q (8*X+1) hqY (negative_root_modulus X Y q gamma B hroot)
  obtain ⟨m,hm⟩ := hd
  change 27*(8*X+1)=H*m at hm
  have hm1 : 1 ≤ m := by
    by_contra hn
    have hp : 0 ≤ H*(-m) := mul_nonneg (le_of_lt hH) (by omega)
    nlinarith
  have hm6 : m ≤ 6 := by
    by_contra hn
    have hp : 0 ≤ H*(m-7) := mul_nonneg (le_of_lt hH) (by omega)
    have hyx : 0 ≤ (Y-8)*(X+1) := mul_nonneg (by omega) (by omega)
    dsimp [H] at *
    nlinarith
  dsimp [H] at hm
  interval_cases q <;> norm_num at hq3
  all_goals interval_cases Y <;> norm_num at hq3
  all_goals interval_cases m <;> norm_num at hm
  all_goals nlinarith [heta]
