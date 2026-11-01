import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Int.Order.Basic

/-! A necessary congruence and positivity obstruction for one restricted
85-gap Pell template. No statement about arbitrary 85 zeros is made. -/

theorem cubic_modulus (X Y q : ℤ) (hq : q ∣ Y)
    (hdiv : (4*Y*(X+1)+3) ∣ Y*q^2*(8-X)) :
    (4*Y*(X+1)+3) ∣ 27*(8-X) := by
  obtain ⟨v,hv⟩ := hq
  obtain ⟨z,hz⟩ := hdiv
  let H := 4*Y*(X+1)+3
  let d := 4*Y*(X+1)
  have hY3 : Y^3*(8-X) = H*(v^2*z) := by
    calc
      Y^3*(8-X) = (Y*q^2*(8-X))*v^2 := by rw [hv]; ring
      _ = H*z*v^2 := by rw [hz]
      _ = H*(v^2*z) := by ring
  refine ⟨(d^2-3*d+9)*(8-X)-64*(X+1)^3*v^2*z, ?_⟩
  calc
    27*(8-X) = (H*(d^2-3*d+9)-d^3)*(8-X) := by dsimp [H,d]; ring
    _ = H*((d^2-3*d+9)*(8-X))-64*(X+1)^3*(Y^3*(8-X)) := by dsimp [d]; ring
    _ = H*((d^2-3*d+9)*(8-X))-64*(X+1)^3*(H*(v^2*z)) := by rw [hY3]
    _ = H*((d^2-3*d+9)*(8-X)-64*(X+1)^3*v^2*z) := by ring

theorem positivity_excludes (X Y eta : ℤ) (hX : 1 ≤ X) (hY : 8 ≤ Y)
    (hEta : 0 < eta)
    (heta : eta = 4*((Y*(X+1))^2+4*Y*(X+1)+3)+3 - Y*(8*X*Y^2+4))
    (hdiv : (4*Y*(X+1)+3) ∣ 27*(8-X)) : False := by
  have hy2 : 0 ≤ Y^2 := sq_nonneg Y
  have hycube : 8*Y^2 ≤ Y^3 := by nlinarith [mul_nonneg (show 0 ≤ Y-8 by omega) hy2]
  have hx4 : 4 ≤ X := by
    by_contra hn
    have hx : X=1 ∨ X=2 ∨ X=3 := by omega
    rcases hx with rfl | rfl | rfl <;> nlinarith
  let H := 4*Y*(X+1)+3
  have hH : 0 < H := by dsimp [H]; nlinarith
  have hYmul : 0 ≤ (Y-8)*(X+1) := mul_nonneg (by omega) (by omega)
  have hx8 : X=8 := by
    by_cases h : X ≤ 8
    · have hnonneg : 0 ≤ 27*(8-X) := by omega
      have hlt : 27*(8-X) < H := by dsimp [H]; nlinarith
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hdiv
      omega
    · have hnonneg : 0 ≤ 27*(X-8) := by omega
      have hlt : 27*(X-8) < H := by dsimp [H]; nlinarith
      have hneg : H ∣ 27*(X-8) := by
        obtain ⟨z,hz⟩ := hdiv
        refine ⟨-z, ?_⟩
        change 27*(8-X) = H*z at hz
        calc
          27*(X-8) = -(27*(8-X)) := by ring
          _ = -(H*z) := by rw [hz]
          _ = H*(-z) := by ring
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hneg
      omega
  subst X
  nlinarith

/-- Positive orientation of the main root yields the small modulus. -/
theorem positive_root_modulus (X Y q gamma B : ℤ)
    (hroot :
      (Y*q^2) * (4*(Y*(X+1)+2)^3 - 3*(Y*(X+1)+2)) =
      (Y*q^2) * (X + (Y*(X+1))*(4*((Y*(X+1))^2+4*(Y*(X+1))+3)+3)) +
      (4*Y*(X+1)+3) * ((Y*q^2)*gamma+B)) :
    (4*Y*(X+1)+3) ∣ Y*q^2*(8-X) := by
  let a := Y*(X+1)
  let H := 4*a+3
  let U := Y*q^2
  let c := 4*(a^2+4*a+3)+3
  let S := 4*(a+2)^3-3*(a+2)
  have hr : U*S=U*(X+a*c)+H*(U*gamma+B) := by
    dsimp [a,H,U,c,S]
    ring_nf at hroot ⊢
    exact hroot
  have hs : S = X+a*c+H*(2*a+6)+(8-X) := by dsimp [S,c,H]; ring
  refine ⟨U*gamma+B-U*(2*a+6), ?_⟩
  have ht : U*(8-X) = H*(U*gamma+B-U*(2*a+6)) := by
    calc
      U*(8-X) = U*S-U*(X+a*c)-U*H*(2*a+6) := by rw [hs]; ring
      _ = H*(U*gamma+B)-U*H*(2*a+6) := by rw [hr]; ring
      _ = H*(U*gamma+B-U*(2*a+6)) := by ring
  simpa only [U,H,a,mul_assoc] using ht

/-- The restricted positive-oriented Pell template has no positive eta. -/
theorem exclude_positive_template (X Y q eta gamma B : ℤ)
    (hX : 1 ≤ X) (hY : 8 ≤ Y) (hEta : 0 < eta) (hq : q ∣ Y)
    (heta : eta = 4*((Y*(X+1))^2+4*Y*(X+1)+3)+3 - Y*(8*X*Y^2+4))
    (hroot :
      (Y*q^2) * (4*(Y*(X+1)+2)^3 - 3*(Y*(X+1)+2)) =
      (Y*q^2) * (X + (Y*(X+1))*(4*((Y*(X+1))^2+4*(Y*(X+1))+3)+3)) +
      (4*Y*(X+1)+3) * ((Y*q^2)*gamma+B)) : False := by
  exact positivity_excludes X Y eta hX hY hEta heta
    (cubic_modulus X Y q hq (positive_root_modulus X Y q gamma B hroot))
