import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous equations under scalar rescaling

Generic polynomial algebra for the projective clearing assertion
`odg:cor:projectiveclear`.
-/

namespace Surreal

/-- Evaluation of a homogeneous polynomial scales by the corresponding power. -/
theorem homogeneous_eval_mul {R σ : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d)
    (c : R) (x : σ → R) :
    p.eval (fun i => c * x i) = c ^ d * p.eval x := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd : ∑ i ∈ a.support, a i = d := by
    have h := hp (MvPolynomial.mem_support_iff.mp ha)
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

/-- Every homogeneous equation vanishing on a tuple still vanishes after scaling. -/
theorem homogeneous_eval_mul_eq_zero {R σ : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d)
    (c : R) {x : σ → R} (hx : p.eval x = 0) :
    p.eval (fun i => c * x i) = 0 := by
  rw [homogeneous_eval_mul hp, hx, mul_zero]

end Surreal
