import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Finite polynomial functionals determined by their moments

A finite weighted evaluation functional on polynomials is completely
determined by its monomial moments.  This module isolates that elementary
principle in a scalar-extension form reusable by the Prouhet, Lagrange, and
Richardson layers.

Let `φ : R →+* S`, let `weight` and `node` be finite families in a
commutative semiring `S`, and write

`L(p) = ∑ i, weight i * p.eval₂ φ (node i)`.

* `sum_weight_mul_eval₂_eq_sum_coeff_mul_moment` expands `L(p)` as the sum
  of the mapped coefficients of `p` times the corresponding node moments.
* `sum_weight_mul_eval₂_eq_coeff_mul_moment` says that, when every moment
  through a degree bound vanishes except the one in degree `r`, `L` selects
  exactly the coefficient of degree `r` times that surviving moment.
* `sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments` is the degree-valued
  top-coefficient form with a supplied exact top moment.
* `sum_weight_mul_eval_eq_zero_of_degree_lt` is its same-ring strict-degree
  annihilation corollary.

The nodes may repeat, the surviving moment may itself be zero, and no field
or subtraction is needed.  The endpoint `r = N` is the algebra behind
finite differences and Prouhet extraction; `r = 0` is the algebra behind
polynomially exact Richardson filters and evaluation at zero.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Moment expansion of a finite weighted polynomial functional.**  If
`p` has degree at most `N`, then its weighted evaluations are the sum, over
degrees `0,…,N`, of its mapped coefficients times the corresponding
weighted node moments.

The statement allows scalar extension from an arbitrary semiring `R` to an
arbitrary commutative semiring `S`. -/
theorem sum_weight_mul_eval₂_eq_sum_coeff_mul_moment
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (p : Polynomial R) (N : ℕ) (hdeg : p.natDegree ≤ N) :
    ∑ i ∈ s, weight i * p.eval₂ φ (node i) =
      ∑ d ∈ range (N + 1),
        φ (p.coeff d) * ∑ i ∈ s, weight i * node i ^ d := by
  have hdeg' : p.natDegree < N + 1 := Nat.lt_succ_of_le hdeg
  simp_rw [Polynomial.eval₂_eq_sum_range' φ hdeg', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _hd => ?_
  refine Finset.sum_congr rfl fun i _hi => ?_
  ac_rfl

/-- **Selected-coefficient principle.**  Suppose all weighted node moments
through degree `N` vanish except possibly the moment in degree `r`.  On every
polynomial of degree at most `N`, weighted evaluation then selects precisely
the coefficient of degree `r`, multiplied by that surviving moment.

No distinctness or nonzeroness assumptions on the nodes or weights are
required, and `r` may be any degree between `0` and `N`. -/
theorem sum_weight_mul_eval₂_eq_coeff_mul_moment
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (p : Polynomial R) {N r : ℕ} (hdeg : p.natDegree ≤ N) (hr : r ≤ N)
    (hvanish : ∀ d ≤ N, d ≠ r →
      ∑ i ∈ s, weight i * node i ^ d = 0) :
    ∑ i ∈ s, weight i * p.eval₂ φ (node i) =
      φ (p.coeff r) * ∑ i ∈ s, weight i * node i ^ r := by
  rw [sum_weight_mul_eval₂_eq_sum_coeff_mul_moment φ s weight node p N hdeg,
    Finset.sum_eq_single r]
  · intro d hd hdne
    have hdle : d ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    rw [hvanish d hdle hdne, mul_zero]
  · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))).elim

/-- **Top-coefficient specialization.**  If the weighted node moments vanish
in every degree strictly below `N`, then weighted evaluation on polynomials
of degree at most `N` extracts the coefficient of degree `N` times the
`N`-th moment. -/
theorem sum_weight_mul_eval₂_eq_topCoeff_mul_moment
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (p : Polynomial R) (N : ℕ) (hdeg : p.natDegree ≤ N)
    (hvanish : ∀ d < N, ∑ i ∈ s, weight i * node i ^ d = 0) :
    ∑ i ∈ s, weight i * p.eval₂ φ (node i) =
      φ (p.coeff N) * ∑ i ∈ s, weight i * node i ^ N := by
  exact sum_weight_mul_eval₂_eq_coeff_mul_moment φ s weight node p hdeg le_rfl
    fun d hd hdne => hvanish d (lt_of_le_of_ne hd hdne)

/-- **Constant-coefficient specialization.**  If the weighted node moments
vanish in every positive degree through `N`, then weighted evaluation on
polynomials of degree at most `N` is the mapped constant coefficient times
the total mass of the weights.  A normalized row therefore evaluates every
such polynomial at zero, which is the algebraic core of Richardson
extrapolation. -/
theorem sum_weight_mul_eval₂_eq_constantCoeff_mul_sum
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (p : Polynomial R) (N : ℕ) (hdeg : p.natDegree ≤ N)
    (hvanish : ∀ d, 0 < d → d ≤ N →
      ∑ i ∈ s, weight i * node i ^ d = 0) :
    ∑ i ∈ s, weight i * p.eval₂ φ (node i) =
      φ (p.coeff 0) * ∑ i ∈ s, weight i := by
  simpa only [pow_zero, mul_one] using
    sum_weight_mul_eval₂_eq_coeff_mul_moment φ s weight node p hdeg
      (Nat.zero_le N) fun d hd hdne => hvanish d (Nat.pos_of_ne_zero hdne) hd

/-- A normalized finite row whose positive moments through `N` vanish
evaluates every degree-`N` polynomial at zero after scalar extension. -/
theorem sum_weight_mul_eval₂_eq_constantCoeff
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (p : Polynomial R) (N : ℕ) (hdeg : p.natDegree ≤ N)
    (hmass : ∑ i ∈ s, weight i = 1)
    (hvanish : ∀ d, 0 < d → d ≤ N →
      ∑ i ∈ s, weight i * node i ^ d = 0) :
    ∑ i ∈ s, weight i * p.eval₂ φ (node i) = φ (p.coeff 0) := by
  rw [sum_weight_mul_eval₂_eq_constantCoeff_mul_sum φ s weight node p N hdeg
    hvanish, hmass, mul_one]

/-! ## Degree-valued top-moment API -/

/-- **Finite moment extraction after scalar extension.**  Let the polynomial
coefficients lie in a semiring `R`, while the weights and nodes lie in a
commutative semiring `S`.  If the lower moments vanish and the moment in
degree `n` is `c`, evaluation through any ring homomorphism from `R` to `S`
extracts the image of the coefficient in degree `n` times `c`.

Unlike the range-sum engine above, this public form uses `Polynomial.degree`.
It therefore expresses the zero-polynomial boundary correctly even when
`n = 0`; mapping is allowed to lower the degree and need not be injective. -/
theorem sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (n : ℕ) (c : S)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (htop : (∑ i ∈ s, weight i * node i ^ n) = c)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval₂ φ (node i)) =
      φ (p.coeff n) * c := by
  rw [sum_weight_mul_eval₂_eq_topCoeff_mul_moment φ s weight node p n
      (Polynomial.natDegree_le_of_degree_le hp) hlower,
    htop]

/-- Normalization-free degree-valued form of top-coefficient extraction.
The top moment remains in its defining finite-sum form. -/
theorem sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval₂ φ (node i)) =
      φ (p.coeff n) * ∑ i ∈ s, weight i * node i ^ n := by
  exact sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments
    φ s weight node n (∑ i ∈ s, weight i * node i ^ n)
      hlower rfl p hp

/-- **Strict-degree cancellation after scalar extension.**  A weighted node
family whose moments below `n` vanish annihilates the image of every
polynomial of degree strictly below `n`. -/
theorem sum_weight_mul_eval₂_eq_zero_of_degree_lt
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree < (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval₂ φ (node i)) = 0 := by
  rw [sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
      φ s weight node n hlower p hp.le,
    Polynomial.coeff_eq_zero_of_degree_lt hp, map_zero, zero_mul]

/-- **Mapped top-coefficient congruence.**  Two degree-bounded polynomials
have equal weighted evaluation sums whenever the coefficient homomorphism
identifies their coefficients of degree `n`. -/
theorem sum_weight_mul_eval₂_congr_of_map_coeff_eq
    {R S ι : Type*} [Semiring R] [CommSemiring S]
    (φ : R →+* S) (s : Finset ι) (weight node : ι → S)
    (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p q : Polynomial R)
    (hp : p.degree ≤ (n : WithBot ℕ))
    (hq : q.degree ≤ (n : WithBot ℕ))
    (hcoeff : φ (p.coeff n) = φ (q.coeff n)) :
    (∑ i ∈ s, weight i * p.eval₂ φ (node i)) =
      ∑ i ∈ s, weight i * q.eval₂ φ (node i) := by
  rw [sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
      φ s weight node n hlower p hp,
    sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
      φ s weight node n hlower q hq,
    hcoeff]

/-! ### Same-ring conveniences -/

/-- Same-ring finite moment extraction with a supplied exact top moment. -/
theorem sum_weight_mul_eval_eq_coeff_mul_of_moments
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (weight node : ι → R) (n : ℕ) (c : R)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (htop : (∑ i ∈ s, weight i * node i ^ n) = c)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval (node i)) = p.coeff n * c := by
  simpa only [Polynomial.eval₂_id, RingHom.id_apply] using
    (sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments
      (RingHom.id R) s weight node n c hlower htop p hp)

/-- Same-ring, normalization-free top-coefficient extraction. -/
theorem sum_weight_mul_eval_eq_coeff_mul_top_moment
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (weight node : ι → R) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval (node i)) =
      p.coeff n * ∑ i ∈ s, weight i * node i ^ n := by
  exact sum_weight_mul_eval_eq_coeff_mul_of_moments
    s weight node n (∑ i ∈ s, weight i * node i ^ n)
      hlower rfl p hp

/-- Same-ring strict-degree finite moment cancellation. -/
theorem sum_weight_mul_eval_eq_zero_of_degree_lt
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (weight node : ι → R) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree < (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval (node i)) = 0 := by
  rw [sum_weight_mul_eval_eq_coeff_mul_top_moment
      s weight node n hlower p hp.le,
    Polynomial.coeff_eq_zero_of_degree_lt hp, zero_mul]

/-- Same-ring congruence for degree-bounded polynomials having the same top
coefficient. -/
theorem sum_weight_mul_eval_congr_of_coeff_eq
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (weight node : ι → R) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p q : Polynomial R)
    (hp : p.degree ≤ (n : WithBot ℕ))
    (hq : q.degree ≤ (n : WithBot ℕ))
    (hcoeff : p.coeff n = q.coeff n) :
    (∑ i ∈ s, weight i * p.eval (node i)) =
      ∑ i ∈ s, weight i * q.eval (node i) := by
  rw [sum_weight_mul_eval_eq_coeff_mul_top_moment
      s weight node n hlower p hp,
    sum_weight_mul_eval_eq_coeff_mul_top_moment
      s weight node n hlower q hq,
    hcoeff]

end Fabius
