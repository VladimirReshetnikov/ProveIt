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
  let q : Polynomial R := Polynomial.C d * Polynomial.X + Polynomial.C x
  have hq : q.natDegree ≤ 1 := by
    rw [show q = Polynomial.C d * Polynomial.X + Polynomial.C x from rfl,
      Polynomial.natDegree_add_C]
    exact (Polynomial.natDegree_C_mul_le d Polynomial.X).trans Polynomial.natDegree_X_le
  by_cases hpk : p.natDegree = k
  · by_cases hd : d = 0
    · simp [hd, Polynomial.comp_C, Polynomial.coeff_C, Nat.ne_of_gt hk]
    · have hqd : q.natDegree = 1 := by
        simp only [q, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X d hd]
      have hlq : q.leadingCoeff = d := by
        rw [Polynomial.leadingCoeff, hqd]
        simp [q]
      have h := Polynomial.coeff_comp_degree_mul_degree (p := p) (q := q)
        (by omega : q.natDegree ≠ 0)
      rw [hpk, hqd, Nat.mul_one, hlq, Polynomial.leadingCoeff, hpk] at h
      exact h
  · have hpklt : p.natDegree < k := by omega
    have hcomp : (p.comp q).natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_comp_le.trans
        (by simpa using Nat.mul_le_mul_left p.natDegree hq)) hpklt
    change (p.comp q).coeff k = _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hcomp,
      Polynomial.coeff_eq_zero_of_natDegree_lt hpklt, zero_mul]

/-- A single leading coefficient works at every translate and every step in
the induction: the top-degree oscillation is separated from a lower-degree
polynomial on the progression indices. -/
theorem polynomialOn_affine_degree_drop {N k : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (hphi : PolynomialOn (k + 1) Finset.univ phi) :
    ∃ a : ZMod N, ∀ x d : ZMod N, ∃ psi : ZMod N → ZMod N,
      PolynomialOn k Finset.univ psi ∧
      ∀ t, phi (x + t * d) = a * d ^ (k + 1) * t ^ (k + 1) + psi t := by
  obtain ⟨p, hp, heval⟩ := (polynomialOn_univ_iff_polynomial phi).mp hphi
  refine ⟨p.coeff (k + 1), ?_⟩
  intro x d
  let q := p.comp (Polynomial.C d * Polynomial.X + Polynomial.C x)
  let b := p.coeff (k + 1) * d ^ (k + 1)
  let remainder := q - Polynomial.C b * Polynomial.X ^ (k + 1)
  have hqdegree : q.natDegree ≤ k + 1 := by
    apply Polynomial.natDegree_comp_le.trans
    have haff : (Polynomial.C d * Polynomial.X + Polynomial.C x).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_add_C]
      exact (Polynomial.natDegree_C_mul_le d Polynomial.X).trans Polynomial.natDegree_X_le
    simpa using Nat.mul_le_mul hp haff
  have hremDegree : remainder.natDegree ≤ k := by
    have hle : remainder.natDegree ≤ k + 1 := by
      exact (Polynomial.natDegree_sub_le _ _).trans
        (max_le hqdegree (Polynomial.natDegree_C_mul_X_pow_le b (k + 1)))
    have hzero : remainder.coeff (k + 1) = 0 := by
      simp only [remainder, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
      rw [show q.coeff (k + 1) = b from polynomial_affine_top_coefficient p
        (k + 1) (by omega) hp x d]
      exact sub_self _
    simpa using Polynomial.natDegree_le_pred hle hzero
  refine ⟨fun t => remainder.eval t, ?_, ?_⟩
  · exact (polynomialOn_univ_iff_polynomial _).mpr ⟨remainder, hremDegree, fun _ => rfl⟩
  · intro t
    rw [heval]
    simp only [remainder, q, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, b]
    rw [show d * t + x = x + t * d by ring]
    ring

end LeanProofs.GowersSzemeredi
