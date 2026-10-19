import GowersSzemeredi.Proofs05Downstream
import Mathlib.Algebra.Polynomial.Degree.Monomial

/-!
# The polynomial degree drop in Corollary 5.6

After choosing a recurrence step d for the leading coefficient a, restrict
phi to x+d*t and split off a*d^k*t^k. The remaining polynomial has degree at
most k-1. The argument works over ZMod N without primality or invertibility
of d, including vanishing leading coefficients.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The coefficient encoding in the catalogue agrees with bounded-degree
polynomials in Mathlib. -/
theorem polynomialOn_univ_iff_polynomial {N k : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) :
    PolynomialOn k Finset.univ phi ↔
      ∃ p : Polynomial (ZMod N), p.natDegree ≤ k ∧ ∀ x, phi x = p.eval x := by
  constructor
  · rintro ⟨c, hc⟩
    let p : Polynomial (ZMod N) := Polynomial.ofFn (k + 1) c
    have hp : p.natDegree < k + 1 := Polynomial.ofFn_natDegree_lt (by omega) c
    refine ⟨p, by omega, ?_⟩
    intro x
    rw [hc x (Finset.mem_univ _), Polynomial.eval_eq_sum_range' hp,
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [show p.coeff (i : Nat) = c i from Polynomial.ofFn_coeff_eq_val_of_lt c i.isLt]
  · rintro ⟨p, hp, heval⟩
    refine ⟨fun i => p.coeff i, ?_⟩
    intro x _
    rw [heval x, Polynomial.eval_eq_sum_range' (by omega : p.natDegree < k + 1),
      ← Fin.sum_univ_eq_sum_range]

/-- At a degree bound, affine substitution multiplies the top coefficient by
the appropriate power of its slope, even in rings with zero divisors. -/
theorem polynomial_affine_top_coefficient {R : Type*} [CommRing R]
    (p : Polynomial R) (k : Nat) (hk : 0 < k) (hp : p.natDegree ≤ k) (x d : R) :
    (p.comp (Polynomial.C d * Polynomial.X + Polynomial.C x)).coeff k =
      p.coeff k * d ^ k := by
  rcases hp.lt_or_eq with hpk | rfl
  · have hcomp : (p.comp (Polynomial.C d * Polynomial.X + Polynomial.C x)).natDegree < k :=
      Polynomial.natDegree_comp_le.trans_lt <|
        (Nat.mul_le_mul_left _ Polynomial.natDegree_linear_le).trans_lt (by rwa [mul_one])
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hcomp,
      Polynomial.coeff_eq_zero_of_natDegree_lt hpk, zero_mul]
  rcases eq_or_ne d 0 with rfl | hd
  · simp [Polynomial.comp_C, Polynomial.coeff_C, hk.ne']
  have h := Polynomial.coeff_comp_degree_mul_degree (p := p)
    (q := Polynomial.C d * Polynomial.X + Polynomial.C x)
    ((Polynomial.natDegree_linear hd).trans_ne one_ne_zero)
  rwa [Polynomial.natDegree_linear hd, mul_one, Polynomial.leadingCoeff_linear hd,
    Polynomial.leadingCoeff] at h

/-- A single leading coefficient works at every translate and every step in
the induction: the top-degree oscillation is separated from a lower-degree
polynomial on the progression indices. -/
theorem polynomialOn_affine_degree_drop {N k : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (hphi : PolynomialOn (k + 1) Finset.univ phi) :
    ∃ a : ZMod N, ∀ x d : ZMod N, ∃ psi : ZMod N → ZMod N,
      PolynomialOn k Finset.univ psi ∧
      ∀ t, phi (x + t * d) = a * d ^ (k + 1) * t ^ (k + 1) + psi t := by
  obtain ⟨p, hp, heval⟩ := (polynomialOn_univ_iff_polynomial phi).mp hphi
  refine ⟨p.coeff (k + 1), fun x d => ?_⟩
  let q := p.comp (Polynomial.C d * Polynomial.X + Polynomial.C x)
  let r := q - Polynomial.C (p.coeff (k + 1) * d ^ (k + 1)) * Polynomial.X ^ (k + 1)
  have hle : r.natDegree ≤ k + 1 := (Polynomial.natDegree_sub_le _ _).trans <|
    max_le ((Polynomial.natDegree_comp_le.trans
      (Nat.mul_le_mul hp Polynomial.natDegree_linear_le)).trans_eq (mul_one _))
      (Polynomial.natDegree_C_mul_X_pow_le _ _)
  have hzero : r.coeff (k + 1) = 0 := by
    simp only [r, q, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self,
      mul_one, sub_self, polynomial_affine_top_coefficient p (k + 1) k.succ_pos hp x d]
  refine ⟨fun t => r.eval t, (polynomialOn_univ_iff_polynomial _).mpr
    ⟨r, by simpa using Polynomial.natDegree_le_pred hle hzero, fun _ => rfl⟩, fun t => ?_⟩
  rw [heval, show x + t * d = d * t + x by ring]
  simp only [r, q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_add]
  ring

end LeanProofs.GowersSzemeredi
