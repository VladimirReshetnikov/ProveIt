import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliShape
import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderCenteredBernoulli

/-!
# A denominator-cleared identity for the positive Bernoulli shape

This lifts the identity at rational arguments to a universal integer
polynomial identity, so the same comparison applies to the actual
object-arithmetic mesh sample.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliShapeClearing

open Finset
open GaussianStirlingAllOrderBernoulliShape (centeredShape centered_shape_nonnegative centered_at_rational)
open GaussianStirlingAllOrderBernoulliMesh (homogeneous)
open GaussianStirlingAllOrderBernoulliCoefficients (normalized integer_polynomial_evaluation)
open GaussianStirlingAllOrderCenteredBernoulli (factor)
open BernoulliBounds (bint bden)

noncomputable def degree (m : ℕ) : ℕ := (centeredShape m).natDegree
noncomputable def scale (m : ℕ) : ℕ := ∏ i ∈ range (degree m+1), ((centeredShape m).coeff i).den

theorem scale_positive (m : ℕ) : 0 < scale m :=
  prod_pos fun i _ => ((centeredShape m).coeff i).den_pos

noncomputable def coefficient (m : ℕ) (i : Fin (degree m+1)) : ℕ :=
  ((centeredShape m).coeff i).num.toNat * (scale m/((centeredShape m).coeff i).den)

theorem coefficient_value (m : ℕ) (i : Fin (degree m+1)) :
    (coefficient m i : ℚ) = (centeredShape m).coeff i*scale m := by
  let c := (centeredShape m).coeff i
  have hd : c.den ∣ scale m := dvd_prod_of_mem _ (mem_range.mpr i.isLt)
  have hn : 0 ≤ c.num := Rat.num_nonneg.mpr (centered_shape_nonnegative m i)
  have hD : (c.den : ℚ) ≠ 0 := by positivity
  change (((c.num.toNat*(scale m/c.den):ℕ):ℚ)) = c*scale m
  rw [Nat.cast_mul,← Int.cast_natCast,Int.toNat_of_nonneg hn,Nat.cast_div hd hD]
  conv_rhs => rw [← Rat.num_div_den c]
  field_simp

noncomputable def value {R : Type*} [CommRing R] (m : ℕ) (x y : R) : R :=
  ∑ i : Fin (degree m+1), (coefficient m i : R)*x^(i : ℕ)*y^(degree m-(i : ℕ))

private theorem scaled_monomial (d i : ℕ) (p q : ℚ) (hi : i ≤ d) (hq : q ≠ 0) :
    (p/q)^i*q^d = p^i*q^(d-i) := by
  rw [div_pow]
  calc
    p^i/q^i*q^d = p^i/q^i*(q^i*q^(d-i)) := by rw [← pow_add,Nat.add_sub_of_le hi]
    _ = _ := by field_simp

private theorem value_rational (m : ℕ) (p q : ℚ) (hq : q ≠ 0) :
    value m p q = (scale m : ℚ)*(centeredShape m).eval (p/q)*q^(degree m) := by
  have hd : (centeredShape m).natDegree < degree m+1 := Nat.lt_succ_self _
  rw [Polynomial.eval_eq_sum_range' hd,mul_sum,sum_mul,← Fin.sum_univ_eq_sum_range]
  unfold value
  refine sum_congr rfl fun i _ => ?_
  rw [coefficient_value]
  have h := scaled_monomial (degree m) i p q (Nat.le_of_lt_succ i.isLt) hq
  linear_combination -((centeredShape m).coeff i*scale m)*h

private theorem bernoulli_rational (j : ℕ) (p q : ℚ) (hq : q ≠ 0) :
    homogeneous j p q = (bden j : ℚ)*(normalized j).eval (p/q)*q^j := by
  rw [← integer_polynomial_evaluation, sum_mul]
  unfold homogeneous
  refine sum_congr rfl fun i _ => ?_
  have h := scaled_monomial j i p q (Nat.le_of_lt_succ i.isLt) hq
  linear_combination -(bint j i : ℚ)*h

noncomputable def left {R : Type*} [CommRing R] (m : ℕ) (p q : R) : R :=
  ((scale m : R)*(q*q)^(degree m))*
    ((factor (m+1) : R)*(homogeneous (2*(m+1)) p q - homogeneous (2*(m+1)) 0 q))

noncomputable def right {R : Type*} [CommRing R] (m : ℕ) (p q : R) : R :=
  ((bden (2*(m+1)) : R)*q^(2*(m+1)))*value m (4*p*(q-p)) (q*q)

private theorem rational_identity (m : ℕ) (p q : ℚ) (hq : q ≠ 0) :
    left m p q = right m p q := by
  let j := 2*(m+1)
  have jrep : j = 2*m+2 := by dsimp [j]; omega
  have h := centered_at_rational m (p/q)
  have shape : (factor (m+1) : ℚ)*((normalized j).eval (p/q)-(normalized j).eval 0) =
      (centeredShape m).eval (4*p*(q-p)/(q*q)) := by
    have a : 4*(p/q)*(1-p/q) = 4*p*(q-p)/(q*q) := by field_simp
    simpa only [factor,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,jrep,show 2*(m+1)=2*m+2 by omega,a] using h
  unfold left right
  change (↑(scale m)*(q*q)^degree m)*(↑(factor (m+1))*(homogeneous j p q - homogeneous j 0 q)) =
    (↑(bden j)*q^j)*value m (4*p*(q-p)) (q*q)
  rw [bernoulli_rational j p q hq,bernoulli_rational j 0 q hq,value_rational _ _ _ (mul_ne_zero hq hq),_root_.zero_div]
  rw [← shape]
  ring

private theorem map_left {R S : Type*} [CommRing R] [CommRing S] (F : R →+* S) (m : ℕ) (p q : R) :
    F (left m p q) = left m (F p) (F q) := by simp [left,homogeneous]
private theorem map_right {R S : Type*} [CommRing R] [CommRing S] (F : R →+* S) (m : ℕ) (p q : R) :
    F (right m p q) = right m (F p) (F q) := by simp [right,value,map_ofNat]

private theorem universal (m : ℕ) :
    left m (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) (MvPolynomial.X 1) =
      right m (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) (MvPolynomial.X 1) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  let S : Fin 2 → Set ℚ := fun _ => Set.univ \ {0}
  apply MvPolynomial.funext_set S (fun _ => Set.infinite_univ.sdiff (Set.finite_singleton 0))
  intro x hx
  have h : x 1 ≠ 0 := by simpa [S] using Set.mem_pi.mp hx (1 : Fin 2) (Set.mem_univ _)
  simp only [MvPolynomial.eval_map]
  simpa only [← MvPolynomial.coe_eval₂Hom,map_left,map_right,MvPolynomial.eval₂Hom_X'] using
    rational_identity m (x 0) (x 1) h

theorem cleared_identity {R : Type*} [CommRing R] (m : ℕ) (p q : R) :
    left m p q = right m p q := by
  let x : Fin 2 → R := ![p,q]
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) x) (universal m)
  simpa only [map_left,map_right,MvPolynomial.eval₂Hom_X',x,Matrix.cons_val_zero,Matrix.cons_val_one] using h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliShapeClearing
