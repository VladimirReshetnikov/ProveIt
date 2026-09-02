import FabiusFunction.QuantumBinomial
import FabiusFunction.QMultinomial
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The noncommutative `q`-multinomial theorem

Let `x_0, …, x_{r-1}` be elements of a semiring with `x_j x_i = q x_i x_j` for `i < j`, where
`q` commutes with every `x_i`.  Then

`(x_0 + ⋯ + x_{r-1})^n = ∑_{t_0 + ⋯ + t_{r-1} = n} [n; t_0, …, t_{r-1}]_q x_0^{t_0} ⋯ x_{r-1}^{t_{r-1}}`,

the factors written in increasing order of index: the `q`-multinomial coefficients are the
structure constants expanding powers of `x_0 + ⋯ + x_{r-1}` in the ordered monomial basis of
quantum affine space.  The proof peels off `x_0`: the tail `x_1 + ⋯ + x_{r-1}` satisfies the
quantum-plane relation with `x_0`, the noncommutative `q`-binomial theorem applies, and the
tail powers expand by induction; the composition `(t_0, t)` is matched with the pair
`([n, t_0]_q, [n - t_0; t]_q)` through the symmetry `[n, n-k]_q = [n,k]_q`, which is
transported to arbitrary semirings from the universal polynomial `[n,k]_X ∈ ℕ[X]`.

## Main declarations

* `sum_antidiagonalTuple_succ`: summing over `(k+1)`-tuples with sum `n` by the first entry.
* `gaussianBinomial_symm'`: the symmetry `[n, n-k]_q = [n,k]_q` in every semiring.
* `Commute.qMultinomial_left`: `q`-multinomial coefficients commute with whatever `q` does.
* `quantum_multinomial`: the theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

section Antidiagonal

/-- Summing over `(k+1)`-tuples with sum `n` by the first entry `a` and the remaining
`k`-tuple with sum `n - a`. -/
theorem sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ t ∈ Nat.antidiagonalTuple (k + 1) n, f t =
      ∑ ab ∈ antidiagonal n, ∑ t ∈ Nat.antidiagonalTuple k ab.2, f (Fin.cons ab.1 t) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun t : Fin (k + 1) → ℕ =>
      (⟨(t 0, ∑ i : Fin k, t i.succ), Fin.tail t⟩ : Σ _ : ℕ × ℕ, Fin k → ℕ))
    (fun x : Σ _ : ℕ × ℕ, Fin k → ℕ => Fin.cons x.1.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Nat.mem_antidiagonalTuple] at ht
    simp only [Finset.mem_sigma, mem_antidiagonal, Nat.mem_antidiagonalTuple]
    exact ⟨by rw [← ht, Fin.sum_univ_succ], rfl⟩
  · intro x hx
    simp only [Finset.mem_sigma, mem_antidiagonal, Nat.mem_antidiagonalTuple] at hx
    rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [hx.2, hx.1]
  · intro t _
    exact Fin.cons_self_tail t
  · rintro ⟨⟨a, b⟩, t⟩ hx
    simp only [Finset.mem_sigma, mem_antidiagonal, Nat.mem_antidiagonalTuple] at hx
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons, hx.2]
  · intro t _
    simp only [Fin.cons_self_tail]

end Antidiagonal

variable {A : Type*} [Semiring A]

/-- Gaussian coefficients in any semiring are values of the universal polynomial
`[n,k]_X ∈ ℕ[X]` (the natural-number coefficients commute with everything). -/
theorem gaussianBinomial_eq_eval₂RingHom' (q : A) (n k : ℕ) :
    gaussianBinomial q n k =
      eval₂RingHom' (Nat.castRingHom A) q (fun a => by simpa using Nat.cast_commute a q)
        (gaussianBinomial (X : ℕ[X]) n k) := by
  have h := map_gaussianBinomial
    (eval₂RingHom' (Nat.castRingHom A) q (fun a => by simpa using Nat.cast_commute a q))
    (X : ℕ[X]) n k
  have hX : eval₂RingHom' (Nat.castRingHom A) q (fun a => by simpa using Nat.cast_commute a q)
      (X : ℕ[X]) = q := eval₂_X _ _
  rw [hX] at h
  exact h.symm

/-- **Symmetry in every semiring**: `[n, n-k]_q = [n,k]_q`. -/
theorem gaussianBinomial_symm' (q : A) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q n (n - k) = gaussianBinomial q n k := by
  rw [gaussianBinomial_eq_eval₂RingHom' q n (n - k), gaussianBinomial_eq_eval₂RingHom' q n k,
    gaussianBinomial_symm (X : ℕ[X]) hk]

/-- `q`-multinomial coefficients commute with every element that `q` commutes with. -/
theorem _root_.Commute.qMultinomial_left {q x : A} (h : Commute q x) (l : List ℕ) :
    Commute (qMultinomial q l) x := by
  induction l with
  | nil => rw [qMultinomial_nil]; exact Commute.one_left x
  | cons n l ih => rw [qMultinomial_cons]; exact (h.gaussianBinomial_left _ _).mul_left ih

/-- Reassociation across a commuting pair: `a (b (c d)) = (a c) (b d)` when `b c = c b`. -/
private theorem mul_mul_mul_of_commute {a b c d : A} (hbc : Commute b c) :
    a * (b * (c * d)) = a * c * (b * d) := by
  rw [mul_assoc a c, ← mul_assoc b, hbc.eq, mul_assoc]

/-- **The noncommutative `q`-multinomial theorem.**  If `x_j x_i = q x_i x_j` for `i < j` and `q`
commutes with every `x_i`, then

`(x_0 + ⋯ + x_{r-1})^n = ∑_{t} [n; t_0, …, t_{r-1}]_q x_0^{t_0} ⋯ x_{r-1}^{t_{r-1}}`,

summed over all `r`-tuples `t` with `∑ t_i = n`, the factors in increasing order of index. -/
theorem quantum_multinomial {q : A} : ∀ {r : ℕ} (x : Fin r → A), (∀ i, Commute q (x i)) →
    (∀ i j : Fin r, i < j → x j * x i = q * (x i * x j)) → ∀ n : ℕ,
    (∑ i, x i) ^ n =
      ∑ t ∈ Nat.antidiagonalTuple r n,
        qMultinomial q (List.ofFn t) * (List.ofFn fun i => x i ^ t i).prod := by
  intro r
  induction r with
  | zero =>
      intro x _ _ n
      rcases n with _ | n
      · simp
      · rw [show Nat.antidiagonalTuple 0 (n + 1) = ∅ from Nat.antidiagonalTuple_zero_succ n]
        simp
  | succ r ih =>
      intro x hq h n
      have hqS : Commute q (∑ i : Fin r, x i.succ) := by
        show q * (∑ i : Fin r, x i.succ) = (∑ i : Fin r, x i.succ) * q
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (hq i.succ).eq
      have hcomm : (∑ i : Fin r, x i.succ) * x 0 = q * (x 0 * ∑ i : Fin r, x i.succ) := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => h 0 i.succ (Fin.succ_pos i)
      rw [Fin.sum_univ_succ, quantum_binomial (hq 0) hqS hcomm n, sum_antidiagonalTuple_succ,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        ← Finset.sum_range_reflect
          (fun k => gaussianBinomial q n k * (x 0 ^ (n - k) * (∑ i : Fin r, x i.succ) ^ k))
          (n + 1)]
      dsimp only
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
      simp only [Nat.add_sub_cancel, Nat.sub_sub_self hj', gaussianBinomial_symm' q hj']
      rw [ih (fun i => x i.succ) (fun i => hq i.succ)
          (fun i j hij => h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)) (n - j),
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hts : ∑ i, t i = n - j := Nat.mem_antidiagonalTuple.mp ht
      rw [List.ofFn_succ, List.ofFn_succ, Fin.cons_zero, qMultinomial_cons, List.sum_ofFn,
        List.prod_cons]
      simp only [Fin.cons_succ]
      rw [hts, Nat.add_sub_cancel' hj']
      exact mul_mul_mul_of_commute (((hq 0).qMultinomial_left _).pow_right j).symm

end Fabius
