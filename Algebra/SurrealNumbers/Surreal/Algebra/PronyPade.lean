import Surreal.Algebra.PronyHankel
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The finite Padé identity and cross-numerator control

This file proves `prony:lem:pade` (with `prony:eq:numerators` and `prony:eq:pade`),
`prony:lem:cross` (with `prony:eq:cross`) and `prony:eq:Dvalues` of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`. Everything except the
valuation clause holds over an arbitrary field, and the valuation clause holds for an arbitrary
additive valuation. It is then specialised to Hahn series `R((t^Γ))`, with `R` any field and
`Γ` any ordered abelian group.

## Polynomial form of the Laurent statements

The source works with Laurent series in `X⁻¹`. Here they are cleared of denominators.
`momentSeriesPoly N m = ∑_{k<N} m_k X^{N-1-k}` is `X^N ∑_{k<N} m_k X^{-k-1}`. The polynomial
part `[F(X) ∑_{k<N} m_k X^{-k-1}]_+` of `prony:eq:numerators` is therefore the quotient
`padeNumerator N m F = (F · momentSeriesPoly N m) /ₘ X^N`. For `F` monic of degree `n`, the
Padé statement `Â/F = ∑_{k<2n} m_k X^{-k-1} + O(X^{-2n-1})` of `prony:eq:pade` is equivalent
to `deg (F · momentSeriesPoly (2n) m - X^{2n} Â) < n`. Indeed the difference of the two sides
is `-(F · momentSeriesPoly (2n) m - X^{2n} Â) / (X^{2n} F)`, and `X^{2n} F` is monic of degree
`3n`. This polynomial form is `degree_pade_remainder_lt`. The expansion at infinity is
also proved literally, as `coeff_reflect_padeNumerator_mul_inv`. Put `Y = X⁻¹`,
`Ã = Y^{n-1} Â(1/Y)` and `F̃ = Y^n F(1/Y)`, the reflected polynomials. Then
`Â(X)/F(X) = Y Ã(Y)/F̃(Y)`, and the power series `Ã/F̃` begins with `m_0, …, m_{2n-1}`.

## Contents

* `prony:eq:numerators` (the prose after it). The numerator has degree `< n`
  (`degree_padeNumerator_lt`).
* `prony:lem:pade`. The numerator satisfies the Padé identity (`degree_pade_remainder_lt`,
  `coeff_reflect_padeNumerator_mul_inv`).
  The annihilation hypothesis is only needed on the monomials `X^r`, `r < n`, and the
  polynomial form needs only `natDegree F ≤ n`. If `F` is monic of degree `n` with `n` distinct
  roots `b_i`, the residues `Â(b_i)/F'(b_i)` realize all `2n` moments
  (`moment_padeResidues`). The unperturbed numerator of a configuration `(a, w)` is
  `A = ∑ w_i Q_i` (`padeNumerator_moment_nodePoly`). Its Padé identity holds with no
  hypothesis, not even distinct nodes (`degree_nodePoly_pade_remainder_lt`).
* `prony:lem:cross`. Let `P, P'` have degree at most `n`, and let `A, A'` be any
  polynomials whose Padé identities hold for moment sequences `m, m'`. Then
  `D = A' P - A P' = (P P' · momentSeriesPoly (2n) (m' - m)) /ₘ X^{2n}`
  (`cross_numerator_eq`), and `deg D < 2n` (`degree_cross_lt`). If `P, P'` have integral
  coefficients and `v(m'_k - m_k) ≥ κ` for `k < 2n`, every coefficient of `D` has valuation
  at least `κ` (`le_valuation_coeff_cross`). For Hahn series this is
  `le_orderTop_coeff_cross`. The source's configuration (`P` the node polynomial, `A = ∑ w_i Q_i`,
  `P'` a degree-`n` annihilator of the perturbed moments, `A'` its numerator) is
  `cross_numerator_nodePoly` and `le_orderTop_coeff_cross_nodePoly`. Monicity is not needed
  for these clauses.
* `prony:eq:Dvalues`. In cofactor coordinates `P' = P + ∑ b_j Q_j`,
  `D(a_i) = -w_i p_i² b_i` for every polynomial `A'` (`eval_cross_cofactor`).

Nothing in these three statements is left pending. The weight estimate `prony:lem:weight`,
which uses these results, is not formalized here.
-/

namespace Surreal.Prony

open Polynomial Finset

noncomputable section

variable {K : Type*} [Field K] {n k : ℕ}

section Truncation

/-- The truncated moment series at infinity, cleared of its denominator:
`X^N ∑_{k<N} m_k X^{-k-1} = ∑_{k<N} m_k X^{N-1-k}`. -/
def momentSeriesPoly (N : ℕ) (m : ℕ → K) : K[X] :=
  ∑ j ∈ range N, C (m j) * X ^ (N - 1 - j)

/-- `prony:eq:numerators`: the Padé numerator `[F(X) ∑_{k<N} m_k X^{-k-1}]_+`. This is the
polynomial part of a Laurent polynomial in `X⁻¹`, computed as a quotient by `X^N`. -/
def padeNumerator (N : ℕ) (m : ℕ → K) (F : K[X]) : K[X] :=
  (F * momentSeriesPoly N m) /ₘ X ^ N

theorem coeff_momentSeriesPoly (N : ℕ) (m : ℕ → K) (i : ℕ) :
    (momentSeriesPoly N m).coeff i = if i < N then m (N - 1 - i) else 0 := by
  rw [momentSeriesPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hi
  · rw [Finset.sum_eq_single (N - 1 - i)]
    · rw [if_pos (by omega)]
    · intro j hj hji
      rw [mem_range] at hj
      exact if_neg fun h => hji (by omega)
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  · exact Finset.sum_eq_zero fun j hj => if_neg fun h => hi (by rw [mem_range] at hj; omega)

theorem coeff_momentSeriesPoly_of_lt (m : ℕ → K) {N j : ℕ} (hj : j < N) :
    (momentSeriesPoly N m).coeff (N - 1 - j) = m j := by
  rw [coeff_momentSeriesPoly, if_pos (by omega)]
  congr 1
  omega

theorem degree_momentSeriesPoly_lt (N : ℕ) (m : ℕ → K) :
    (momentSeriesPoly N m).degree < N := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_momentSeriesPoly, if_neg (by omega)]

theorem momentSeriesPoly_sub (N : ℕ) (m m' : ℕ → K) :
    momentSeriesPoly N (m - m') = momentSeriesPoly N m - momentSeriesPoly N m' := by
  ext i
  rw [coeff_sub, coeff_momentSeriesPoly, coeff_momentSeriesPoly, coeff_momentSeriesPoly]
  split_ifs <;> simp

/-- A product of a polynomial of degree at most `d` with one of degree below `N` has no
coefficients from `d + N` on. -/
theorem coeff_mul_eq_zero_of_le {F G : K[X]} {d N j : ℕ} (hF : F.natDegree ≤ d)
    (hG : G.degree < N) (hj : d + N ≤ j) : (F * G).coeff j = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases hp : x.1 ≤ d
  · rw [coeff_eq_zero_of_degree_lt (hG.trans_le (by exact_mod_cast (by omega : N ≤ x.2))),
      mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem degree_mul_lt_of_le {F G : K[X]} {d N : ℕ} (hF : F.natDegree ≤ d) (hG : G.degree < N) :
    (F * G).degree < ((d + N : ℕ) : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  exact fun j hj => coeff_mul_eq_zero_of_le hF hG hj

theorem natDegree_le_sub_one_of_degree_lt {F : K[X]} {d : ℕ} (hF : F.degree < d) :
    F.natDegree ≤ d - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun j hj => (degree_lt_iff_coeff_zero _ _).mp hF j (by omega)

/-- The quotient by `X^N` shifts the coefficients down by `N`. -/
theorem coeff_divByMonic_X_pow (q : K[X]) (N i : ℕ) :
    (q /ₘ X ^ N).coeff i = q.coeff (i + N) := by
  have h := modByMonic_add_div q (X ^ N)
  have h0 : (q %ₘ X ^ N).coeff (i + N) = 0 := by
    refine coeff_eq_zero_of_degree_lt ((degree_modByMonic_lt q (monic_X_pow N)).trans_le ?_)
    rw [degree_X_pow]
    exact_mod_cast (by omega : N ≤ i + N)
  conv_rhs => rw [← h]
  rw [coeff_add, coeff_X_pow_mul, h0, zero_add]

theorem sub_X_pow_mul_divByMonic (q : K[X]) (N : ℕ) : q - X ^ N * (q /ₘ X ^ N) = q %ₘ X ^ N :=
  sub_eq_of_eq_add (modByMonic_add_div q (X ^ N)).symm

theorem coeff_modByMonic_X_pow (q : K[X]) {N i : ℕ} (hi : i < N) :
    (q %ₘ X ^ N).coeff i = q.coeff i := by
  rw [← sub_X_pow_mul_divByMonic, coeff_sub, coeff_X_pow_mul', if_neg (by omega), sub_zero]

theorem degree_divByMonic_X_pow_lt {q : K[X]} {d N : ℕ}
    (hq : q.degree < ((d + N : ℕ) : WithBot ℕ)) : (q /ₘ X ^ N).degree < d := by
  rw [degree_lt_iff_coeff_zero] at hq ⊢
  intro i hi
  rw [coeff_divByMonic_X_pow]
  exact hq _ (by omega)

/-- The coefficient of `X^{N-1-r}` in `F · X^N ∑_{k<N} m_k X^{-k-1}` is `L(F X^r)`: this is the
coefficient of `X^{-r-1}` in the proof of `prony:lem:pade`. -/
theorem coeff_mul_momentSeriesPoly (m : ℕ → K) {F : K[X]} {d r N : ℕ} (hF : F.natDegree ≤ d)
    (hr : d + r < N) :
    (F * momentSeriesPoly N m).coeff (N - 1 - r) = momentLinear m (F * X ^ r) := by
  rw [momentLinear_mul_X_pow m hF r]
  conv_lhs => rw [F.as_sum_range' (d + 1) (by omega)]
  rw [Finset.sum_mul, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
    coeff_momentSeriesPoly, if_pos (by omega)]
  congr 2
  omega

end Truncation

section Pade

/-- `prony:eq:numerators` (the prose following it): the numerator `Â` has degree less than
`n`. -/
theorem degree_padeNumerator_lt (N : ℕ) (m : ℕ → K) {F : K[X]} {d : ℕ}
    (hF : F.natDegree ≤ d) : (padeNumerator N m F).degree < d :=
  degree_divByMonic_X_pow_lt (degree_mul_lt_of_le hF (degree_momentSeriesPoly_lt N m))

/-- `prony:lem:pade`, `prony:eq:pade` in polynomial form. For `F` of degree at most `n`: if
`L(F X^r) = 0` for `r < n`, then
`F · X^{2n} ∑_{k<2n} m_k X^{-k-1} - X^{2n} Â` has degree below `n`. For monic `F` of degree `n`
this says `Â/F = ∑_{k<2n} m_k X^{-k-1} + O(X^{-2n-1})`. -/
theorem degree_pade_remainder_lt (m : ℕ → K) {F : K[X]} (hF : F.natDegree ≤ n)
    (hann : ∀ r < n, momentLinear m (F * X ^ r) = 0) :
    (F * momentSeriesPoly (2 * n) m - X ^ (2 * n) * padeNumerator (2 * n) m F).degree <
      (n : WithBot ℕ) := by
  rw [padeNumerator, sub_X_pow_mul_divByMonic, degree_lt_iff_coeff_zero]
  intro i hi
  by_cases hi2 : i < 2 * n
  · rw [coeff_modByMonic_X_pow _ hi2]
    have h := coeff_mul_momentSeriesPoly m hF (r := 2 * n - 1 - i) (N := 2 * n) (by omega)
    rw [show 2 * n - 1 - (2 * n - 1 - i) = i by omega] at h
    rw [h, hann _ (by omega)]
  · refine coeff_eq_zero_of_degree_lt ((degree_modByMonic_lt _ (monic_X_pow _)).trans_le ?_)
    rw [degree_X_pow]
    exact_mod_cast (by omega : 2 * n ≤ i)

/-- `prony:eq:pade` at infinity. With `Y = X⁻¹`, `Ã = Y^{n-1} Â(1/Y)` and
`F̃ = Y^n F(1/Y)`, one has `Â(X)/F(X) = Y Ã(Y)/F̃(Y)`. The power series `Ã/F̃` begins with
`m_0, …, m_{2n-1}`, so `Â/F = ∑_{k<2n} m_k X^{-k-1} + O(X^{-2n-1})`. -/
theorem coeff_reflect_padeNumerator_mul_inv (m : ℕ → K) {F : K[X]} (hF : F.Monic)
    (hFd : F.natDegree = n) (hann : ∀ r < n, momentLinear m (F * X ^ r) = 0) {j : ℕ}
    (hj : j < 2 * n) :
    PowerSeries.coeff j ((reflect (n - 1) (padeNumerator (2 * n) m F) : PowerSeries K) *
      (reflect n F : PowerSeries K)⁻¹) = m j := by
  set A := padeNumerator (2 * n) m F
  set S := momentSeriesPoly (2 * n) m with hS
  set R := F * S - X ^ (2 * n) * A with hR
  have hRn : R.natDegree ≤ n - 1 :=
    natDegree_le_sub_one_of_degree_lt (degree_pade_remainder_lt m hFd.le hann)
  have hAn : A.natDegree ≤ n - 1 :=
    natDegree_le_sub_one_of_degree_lt (degree_padeNumerator_lt (2 * n) m hFd.le)
  have hSn : S.natDegree ≤ 2 * n - 1 :=
    natDegree_le_sub_one_of_degree_lt (degree_momentSeriesPoly_lt (2 * n) m)
  have hpoly : reflect n F * reflect (2 * n - 1) S =
      reflect (n - 1) R * X ^ (2 * n) + reflect (n - 1) A := by
    have h1 := reflect_mul F S hFd.le hSn
    have h2 := reflect_mul R 1 (G := 2 * n) hRn (natDegree_one.le.trans (Nat.zero_le _))
    have h3 := reflect_mul A (X ^ (2 * n)) hAn (natDegree_X_pow_le (2 * n))
    rw [reflect_one, mul_one] at h2
    rw [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, mul_one] at h3
    rw [show n + (2 * n - 1) = n - 1 + 2 * n by omega] at h1
    rw [← h1, ← h2, ← h3, ← reflect_add]
    congr 1
    rw [hR]
    ring
  have hc : PowerSeries.constantCoeff (reflect n F : PowerSeries K) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_reflect, revAt_zero, ← hFd, hF.coeff_natDegree]
    exact one_ne_zero
  have hps := congrArg (fun p : K[X] => (p : PowerSeries K)) hpoly
  simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_pow,
    Polynomial.coe_X] at hps
  have hmain : (reflect (n - 1) A : PowerSeries K) * (reflect n F : PowerSeries K)⁻¹ =
      (reflect (2 * n - 1) S : PowerSeries K) - PowerSeries.X ^ (2 * n) *
        ((reflect (n - 1) R : PowerSeries K) * (reflect n F : PowerSeries K)⁻¹) := by
    have hinv := PowerSeries.mul_inv_cancel _ hc
    calc (reflect (n - 1) A : PowerSeries K) * (reflect n F : PowerSeries K)⁻¹ =
          ((reflect n F : PowerSeries K) * (reflect (2 * n - 1) S : PowerSeries K) -
            (reflect (n - 1) R : PowerSeries K) * PowerSeries.X ^ (2 * n)) *
            (reflect n F : PowerSeries K)⁻¹ := by
          rw [hps]
          ring
      _ = (reflect (2 * n - 1) S : PowerSeries K) *
            ((reflect n F : PowerSeries K) * (reflect n F : PowerSeries K)⁻¹) -
            PowerSeries.X ^ (2 * n) *
              ((reflect (n - 1) R : PowerSeries K) * (reflect n F : PowerSeries K)⁻¹) := by
          ring
      _ = _ := by rw [hinv, mul_one]
  rw [hmain, map_sub, PowerSeries.coeff_X_pow_mul', if_neg (by omega), sub_zero,
    Polynomial.coeff_coe, coeff_reflect, revAt_le (by omega), hS,
    coeff_momentSeriesPoly_of_lt m hj]

end Pade

section Configuration

/-- The truncated moment series of a configuration `(a, w)`, multiplied by its node polynomial:
`P · X^N ∑_{k<N} m_k X^{-k-1} = X^N ∑ w_i Q_i - ∑ w_i a_i^N Q_i`. No hypothesis on the
nodes or weights is needed. -/
theorem nodePoly_mul_momentSeriesPoly_moment (a w : Fin k → K) (N : ℕ) :
    nodePoly a * momentSeriesPoly N (moment a w) =
      X ^ N * ∑ i, C (w i) * cofactor a i - ∑ i, C (w i * a i ^ N) * cofactor a i := by
  have hS : momentSeriesPoly N (moment a w) =
      ∑ i, C (w i) * ∑ j ∈ range N, C (a i) ^ j * X ^ (N - 1 - j) := by
    simp only [momentSeriesPoly, moment, map_sum, map_mul, map_pow, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hg := Commute.mul_neg_geom_sum₂ (Commute.all (C (a i)) (X : K[X])) N
  rw [nodePoly_eq_mul_cofactor a i, map_mul, map_pow]
  linear_combination (C (w i) * cofactor a i) * hg

/-- `prony:eq:numerators`: a combination `∑ c_i Q_i` of cofactors, such as the unperturbed
numerator `A = ∑ w_i Q_i`, has degree less than the number of nodes. -/
theorem degree_sum_C_mul_cofactor_lt (a c : Fin k → K) :
    (∑ i, C (c i) * cofactor a i).degree < k := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hk := Fin.pos i
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [natDegree_cofactor]; omega), mul_zero]

/-- `prony:eq:numerators`: the unperturbed numerator is `A = ∑ w_i Q_i`. It needs only
`k ≤ N`, and no distinctness of the nodes. -/
theorem padeNumerator_moment_nodePoly (a w : Fin k → K) {N : ℕ} (hN : k ≤ N) :
    padeNumerator N (moment a w) (nodePoly a) = ∑ i, C (w i) * cofactor a i := by
  rw [padeNumerator]
  refine (div_modByMonic_unique _ (-∑ i, C (w i * a i ^ N) * cofactor a i) (monic_X_pow N)
    ⟨?_, ?_⟩).1
  · rw [nodePoly_mul_momentSeriesPoly_moment]
    ring
  · rw [degree_neg, degree_X_pow]
    exact (degree_sum_C_mul_cofactor_lt a _).trans_le (by exact_mod_cast hN)

/-- `prony:eq:pade` for the unperturbed data: `A/P = ∑_{k<2n} m_k X^{-k-1} + O(X^{-2n-1})`
with `A = ∑ w_i Q_i`. This holds for every configuration. -/
theorem degree_nodePoly_pade_remainder_lt (a w : Fin n → K) :
    (nodePoly a * momentSeriesPoly (2 * n) (moment a w) -
      X ^ (2 * n) * ∑ i, C (w i) * cofactor a i).degree < (n : WithBot ℕ) := by
  rw [nodePoly_mul_momentSeriesPoly_moment, sub_sub_cancel_left, degree_neg]
  exact degree_sum_C_mul_cofactor_lt a _

/-- Partial fractions: a polynomial of degree below `n` is a combination of the cofactors of
`n` distinct nodes, with coefficients `f(b_i)/Q_i(b_i)`. -/
theorem eq_sum_C_mul_cofactor {b : Fin n → K} (hb : Function.Injective b) {f : K[X]}
    (hf : f.degree < (n : WithBot ℕ)) :
    f = ∑ i, C (f.eval (b i) / (cofactor b i).eval (b i)) * cofactor b i := by
  have hf' : f.degree < (univ : Finset (Fin n)).card := by simpa using hf
  conv_lhs => rw [Lagrange.eq_interpolate (v := b) hb.injOn hf']
  rw [Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lagrange_basis_eq, div_eq_mul_inv, C_mul]
  ring

/-- `P'(a_i) = Q_i(a_i) = p_i`. -/
theorem eval_derivative_nodePoly (b : Fin k → K) (i : Fin k) :
    (nodePoly b).derivative.eval (b i) = (cofactor b i).eval (b i) := by
  rw [nodePoly_eq_mul_cofactor b i, derivative_mul]
  simp

/-- A monic polynomial of degree `n` with `n` distinct roots is their node polynomial. -/
theorem eq_nodePoly_of_isRoot {F : K[X]} (hF : F.Monic) (hFd : F.natDegree = n)
    {b : Fin n → K} (hb : Function.Injective b) (hroot : ∀ i, F.eval (b i) = 0) :
    F = nodePoly b := by
  refine eq_of_degree_sub_lt_of_eval_index_eq univ hb.injOn ?_ fun i _ => ?_
  · have hdeg : F.degree = (nodePoly b).degree := by
      rw [degree_eq_natDegree hF.ne_zero, degree_eq_natDegree (nodePoly_monic b).ne_zero, hFd,
        natDegree_nodePoly]
    calc (F - nodePoly b).degree < F.degree :=
          degree_sub_lt hdeg hF.ne_zero (by rw [hF.leadingCoeff, (nodePoly_monic b).leadingCoeff])
      _ = (univ : Finset (Fin n)).card := by
          rw [degree_eq_natDegree hF.ne_zero, hFd, card_univ, Fintype.card_fin]
  · rw [hroot i, (eval_nodePoly_eq_zero_iff b _).mpr ⟨i, rfl⟩]

/-- If the Padé numerator of the node polynomial of `n` nodes `b` is `∑ w'_i Q_i`, then
`(b, w')` realizes the first `2n` moments. -/
theorem moment_eq_of_padeNumerator_eq {m : ℕ → K} {b w' : Fin n → K}
    (hann : ∀ r < n, momentLinear m (nodePoly b * X ^ r) = 0)
    (hA : padeNumerator (2 * n) m (nodePoly b) = ∑ i, C (w' i) * cofactor b i) {j : ℕ}
    (hj : j < 2 * n) : moment b w' j = m j := by
  have h1 := nodePoly_mul_momentSeriesPoly_moment b w' (2 * n)
  have h2 := degree_pade_remainder_lt m (natDegree_nodePoly b).le hann
  rw [hA] at h2
  have h3 : (nodePoly b * momentSeriesPoly (2 * n) (m - moment b w')).degree <
      (n : WithBot ℕ) := by
    rw [momentSeriesPoly_sub, mul_sub, h1, ← sub_add]
    exact (degree_add_le _ _).trans_lt (max_lt h2 (degree_sum_C_mul_cofactor_lt b _))
  have hS : momentSeriesPoly (2 * n) (m - moment b w') = 0 := by
    by_contra hS
    have hne := (nodePoly_monic b).ne_zero
    rw [degree_eq_natDegree (mul_ne_zero hne hS), natDegree_mul hne hS,
      natDegree_nodePoly] at h3
    norm_cast at h3
    omega
  have h := congrArg (fun p : K[X] => p.coeff (2 * n - 1 - j)) hS
  simp only [coeff_momentSeriesPoly_of_lt _ hj, coeff_zero, Pi.sub_apply, sub_eq_zero] at h
  exact h.symm

/-- `prony:lem:pade`, residue clause. Let `F` be monic of degree `n` with `L(F X^r) = 0` for
`r < n`, and with `n` distinct roots `b_i`. Then the residues `ŵ_i = Â(b_i)/F'(b_i)` realize
all `2n` moments. -/
theorem moment_padeResidues {m : ℕ → K} {F : K[X]} (hF : F.Monic) (hFd : F.natDegree = n)
    (hann : ∀ r < n, momentLinear m (F * X ^ r) = 0) {b : Fin n → K}
    (hb : Function.Injective b) (hroot : ∀ i, F.eval (b i) = 0) {j : ℕ} (hj : j < 2 * n) :
    moment b (fun i => (padeNumerator (2 * n) m F).eval (b i) / F.derivative.eval (b i)) j =
      m j := by
  obtain rfl := eq_nodePoly_of_isRoot hF hFd hb hroot
  refine moment_eq_of_padeNumerator_eq hann ?_ hj
  conv_lhs => rw [eq_sum_C_mul_cofactor hb
    (degree_padeNumerator_lt (2 * n) m (natDegree_nodePoly b).le)]
  simp only [eval_derivative_nodePoly]

end Configuration

section Cross

/-- `prony:lem:cross`, `prony:eq:cross`. Suppose `P, P'` have degree at most `n`, and the
rational functions `A/P`, `A'/P'` agree with `m`, `m'` through `X^{-2n}`, in the polynomial
form of `prony:eq:pade`. Then `D = A' P - A P'` is the polynomial part of
`P P' ∑_{k<2n} (m'_k - m_k) X^{-k-1}`. -/
theorem cross_numerator_eq {m m' : ℕ → K} {P P' A A' : K[X]} (hP : P.natDegree ≤ n)
    (hP' : P'.natDegree ≤ n)
    (hA : (P * momentSeriesPoly (2 * n) m - X ^ (2 * n) * A).degree < (n : WithBot ℕ))
    (hA' : (P' * momentSeriesPoly (2 * n) m' - X ^ (2 * n) * A').degree < (n : WithBot ℕ)) :
    A' * P - A * P' = (P * P' * momentSeriesPoly (2 * n) (m' - m)) /ₘ X ^ (2 * n) := by
  refine ((div_modByMonic_unique (A' * P - A * P')
    (P * (P' * momentSeriesPoly (2 * n) m' - X ^ (2 * n) * A') -
      P' * (P * momentSeriesPoly (2 * n) m - X ^ (2 * n) * A)) (monic_X_pow _)
    ⟨?_, ?_⟩).1).symm
  · rw [momentSeriesPoly_sub]
    ring
  · rw [degree_X_pow]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_mul_lt_of_le hP hA').trans_le (by exact_mod_cast (by omega : n + n ≤ 2 * n))
    · exact (degree_mul_lt_of_le hP' hA).trans_le (by exact_mod_cast (by omega : n + n ≤ 2 * n))

/-- `prony:eq:cross`: `deg D < 2n`. -/
theorem degree_cross_lt {m m' : ℕ → K} {P P' A A' : K[X]} (hP : P.natDegree ≤ n)
    (hP' : P'.natDegree ≤ n)
    (hA : (P * momentSeriesPoly (2 * n) m - X ^ (2 * n) * A).degree < (n : WithBot ℕ))
    (hA' : (P' * momentSeriesPoly (2 * n) m' - X ^ (2 * n) * A').degree < (n : WithBot ℕ)) :
    (A' * P - A * P').degree < ((2 * n : ℕ) : WithBot ℕ) := by
  rw [cross_numerator_eq hP hP' hA hA']
  exact degree_divByMonic_X_pow_lt (degree_mul_lt_of_le
    (natDegree_mul_le.trans (by omega)) (degree_momentSeriesPoly_lt _ _))

/-- `prony:lem:cross` in the source's configuration. `P` is the node polynomial of `(a, w)`,
`A = ∑ w_i Q_i`, `P'` is any annihilator of degree at most `n` of the perturbed moments `m'`,
and `A'` is its numerator. -/
theorem cross_numerator_nodePoly (a w : Fin n → K) {m' : ℕ → K} {P' : K[X]}
    (hP' : P'.natDegree ≤ n) (hann' : ∀ r < n, momentLinear m' (P' * X ^ r) = 0) :
    padeNumerator (2 * n) m' P' * nodePoly a - (∑ i, C (w i) * cofactor a i) * P' =
        (nodePoly a * P' * momentSeriesPoly (2 * n) (m' - moment a w)) /ₘ X ^ (2 * n) ∧
      (padeNumerator (2 * n) m' P' * nodePoly a - (∑ i, C (w i) * cofactor a i) * P').degree <
        ((2 * n : ℕ) : WithBot ℕ) :=
  ⟨cross_numerator_eq (natDegree_nodePoly a).le hP' (degree_nodePoly_pade_remainder_lt a w)
      (degree_pade_remainder_lt m' hP' hann'),
    degree_cross_lt (natDegree_nodePoly a).le hP' (degree_nodePoly_pade_remainder_lt a w)
      (degree_pade_remainder_lt m' hP' hann')⟩

theorem eval_sum_C_mul_cofactor (a c : Fin k → K) (i : Fin k) :
    (∑ j, C (c j) * cofactor a j).eval (a i) = c i * (cofactor a i).eval (a i) := by
  rw [eval_finsetSum, Finset.sum_eq_single i]
  · rw [eval_mul, eval_C]
  · intro j _ hji
    rw [eval_mul, eval_cofactor_of_ne a (Ne.symm hji), mul_zero]
  · simp

/-- `prony:eq:Dvalues`: in cofactor coordinates `P' = P + ∑ b_j Q_j`, the cross numerator
`D = A' P - A P'` with `A = ∑ w_j Q_j` takes the values `D(a_i) = -w_i p_i² b_i = -u_i`,
whatever the polynomial `A'`. -/
theorem eval_cross_cofactor (a w b : Fin n → K) (A' : K[X]) (i : Fin n) :
    (A' * nodePoly a - (∑ j, C (w j) * cofactor a j) *
      (nodePoly a + ∑ j, C (b j) * cofactor a j)).eval (a i) =
      -(w i * (cofactor a i).eval (a i) ^ 2 * b i) := by
  rw [eval_sub, eval_mul, eval_mul, eval_add, (eval_nodePoly_eq_zero_iff a _).mpr ⟨i, rfl⟩,
    eval_sum_C_mul_cofactor, eval_sum_C_mul_cofactor]
  ring

end Cross

section Valuation

variable {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀] (v : AddValuation K Γ₀)

theorem le_valuation_coeff_mul {F G : K[X]} {α β : Γ₀} (hF : ∀ j, α ≤ v (F.coeff j))
    (hG : ∀ j, β ≤ v (G.coeff j)) (j : ℕ) : α + β ≤ v ((F * G).coeff j) := by
  rw [coeff_mul]
  exact v.map_le_sum fun x _ => by
    rw [v.map_mul]
    exact add_le_add (hF _) (hG _)

theorem le_valuation_coeff_momentSeriesPoly {N : ℕ} {m : ℕ → K} {κ : Γ₀}
    (hm : ∀ j < N, κ ≤ v (m j)) (i : ℕ) : κ ≤ v ((momentSeriesPoly N m).coeff i) := by
  rw [coeff_momentSeriesPoly]
  split_ifs with hi
  · exact hm _ (by omega)
  · rw [v.map_zero]
    exact le_top

/-- `prony:lem:cross`, valuation clause, for any additive valuation. If `P, P'` have integral
coefficients and `v(m'_k - m_k) ≥ κ` for `k < 2n`, then every coefficient of `D = A' P - A P'`
has valuation at least `κ`. -/
theorem le_valuation_coeff_cross {m m' : ℕ → K} {P P' A A' : K[X]} (hP : P.natDegree ≤ n)
    (hP' : P'.natDegree ≤ n)
    (hA : (P * momentSeriesPoly (2 * n) m - X ^ (2 * n) * A).degree < (n : WithBot ℕ))
    (hA' : (P' * momentSeriesPoly (2 * n) m' - X ^ (2 * n) * A').degree < (n : WithBot ℕ))
    (hPi : ∀ j, 0 ≤ v (P.coeff j)) (hP'i : ∀ j, 0 ≤ v (P'.coeff j)) {κ : Γ₀}
    (hε : ∀ j < 2 * n, κ ≤ v (m' j - m j)) (r : ℕ) :
    κ ≤ v ((A' * P - A * P').coeff r) := by
  rw [cross_numerator_eq hP hP' hA hA', coeff_divByMonic_X_pow]
  have h := le_valuation_coeff_mul v (le_valuation_coeff_mul v hPi hP'i)
    (le_valuation_coeff_momentSeriesPoly v (m := m' - m) hε) (r + 2 * n)
  rwa [add_zero, zero_add] at h

end Valuation

section Hahn

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

/-- `prony:lem:cross`, valuation clause, over the Hahn field `R((t^Γ))`. If `P, P'` have
integral coefficients and every moment error `m'_k - m_k`, `k < 2n`, has order at least `κ`,
then every coefficient of `D = A' P - A P'` has order at least `κ`. -/
theorem le_orderTop_coeff_cross {m m' : ℕ → HahnSeries Γ R} {P P' A A' : (HahnSeries Γ R)[X]}
    (hP : P.natDegree ≤ n) (hP' : P'.natDegree ≤ n)
    (hA : (P * momentSeriesPoly (2 * n) m - X ^ (2 * n) * A).degree < (n : WithBot ℕ))
    (hA' : (P' * momentSeriesPoly (2 * n) m' - X ^ (2 * n) * A').degree < (n : WithBot ℕ))
    (hPi : ∀ j, 0 ≤ (P.coeff j).orderTop) (hP'i : ∀ j, 0 ≤ (P'.coeff j).orderTop)
    {κ : WithTop Γ} (hε : ∀ j < 2 * n, κ ≤ (m' j - m j).orderTop) (r : ℕ) :
    κ ≤ ((A' * P - A * P').coeff r).orderTop := by
  have h := le_valuation_coeff_cross (HahnSeries.addVal Γ R) hP hP' hA hA'
    (fun j => by rw [HahnSeries.addVal_apply]; exact hPi j)
    (fun j => by rw [HahnSeries.addVal_apply]; exact hP'i j)
    (fun j hj => by rw [HahnSeries.addVal_apply]; exact hε j hj) r
  rwa [HahnSeries.addVal_apply] at h

/-- `prony:lem:cross` over `R((t^Γ))` in the source's configuration: the integral node
polynomial `P` of `(a, w)`, `A = ∑ w_i Q_i`, a degree-`n` integral annihilator `P'` of the
perturbed moments, and its numerator `Â`. -/
theorem le_orderTop_coeff_cross_nodePoly (a w : Fin n → HahnSeries Γ R)
    {m' : ℕ → HahnSeries Γ R} {P' : (HahnSeries Γ R)[X]} (hP' : P'.natDegree ≤ n)
    (hann' : ∀ r < n, momentLinear m' (P' * X ^ r) = 0)
    (hPi : ∀ j, 0 ≤ ((nodePoly a).coeff j).orderTop) (hP'i : ∀ j, 0 ≤ (P'.coeff j).orderTop)
    {κ : WithTop Γ} (hε : ∀ j < 2 * n, κ ≤ (m' j - moment a w j).orderTop) (r : ℕ) :
    κ ≤ ((padeNumerator (2 * n) m' P' * nodePoly a -
      (∑ i, C (w i) * cofactor a i) * P').coeff r).orderTop :=
  le_orderTop_coeff_cross (natDegree_nodePoly a).le hP' (degree_nodePoly_pade_remainder_lt a w)
    (degree_pade_remainder_lt m' hP' hann') hPi hP'i hε r

end Hahn

end

end Surreal.Prony
