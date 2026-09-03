import FabiusFunction.ThetaQuasiPeriodicity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Schröter's lattice dissection

For `‖Q‖ < 1`, `Q ≠ 0` and `x ≠ 0` write the *quadratic* bilateral theta series

`Θ(x; Q) = ∑_{n ∈ ℤ} Q^{n²} x^n`   (`quadTheta Q x`).

**Schröter's formula** dissects a product of two such series with commensurable bases.  For
positive integers `a`, `b`, for `‖q‖ < 1`, `q ≠ 0` and `x, y ≠ 0`,

`Θ(x; q^a) Θ(y; q^b)
    = ∑_{k=0}^{a+b-1} y^k q^{bk²} Θ(x y q^{2bk}; q^{a+b}) Θ(y^a x^{-b} q^{2abk}; q^{ab(a+b)})`

(`schroeter_formula`, `hasSum_schroeter`).

## The proof

Expand the left side over the lattice `(n, m) ∈ ℤ²` (`schroeterTerm`).  The map

`(k, (r, s)) ↦ (n, m) = (r - b s, k + r + a s)`,   `k ∈ Fin (a+b)`, `(r, s) ∈ ℤ²`

is a bijection `ℤ² ≃ Fin (a+b) × ℤ²` (`schroeterEquiv`): the second coordinate minus the first is
`k + (a+b) s`, so `k` is the residue of `m - n` modulo `a + b` and `s` its quotient — which is
exactly `Int.divModEquiv (a+b)` — and then `r = n + b s` recovers the remaining coordinate.  This
is the index-`(a+b)` sublattice description of the monograph's remark on sublattice cosets; the
linear part `(r, s) ↦ (r - b s, r + a s)` has determinant `a + b`.

Under this substitution

* `x^n y^m = y^k (x y)^r (y^a x^{-b})^s`, and
* `a n² + b m² = (a+b) r² + 2bkr + b k² + ab(a+b) s² + 2abks`   (`schroeterExponent`),

the mixed `rs` term cancelling; so each fibre is a product of two quadratic theta series
(`schroeterTerm_reindex`, `hasSum_schroeterFibre`).

The monograph's proof says only "absolute convergence justifies the partition and
rearrangement".  Here that obligation is discharged: `summable_norm_quadThetaTerm` exhibits the
majorant `‖Q²‖^{n(n-1)/2} ‖Qx‖^n` (through the crosswalk `Θ(x; Q) = θ(Qx; Q²)` to the bilateral
Jacobi series), `summable_mul_of_summable_norm` makes the doubly indexed family unconditionally
summable, and the dissection is then a `HasSum` reindexing followed by `HasSum.prod_fiberwise`.

## Main declarations

* `quadTheta`, `hasSum_quadTheta`, `summable_norm_quadThetaTerm`.
* `quadTheta_eq_bilateralTheta`: the crosswalk `Θ(x; Q) = θ(Qx; Q²)`, carrying the hypothesis
  `Q ≠ 0` that the monograph leaves to its standing convention `0 < |q| < 1`.
* `quadTheta_eq_prod`: Jacobi's triple product in the `∑ Q^{n²} x^n` normalisation.
* `schroeterEquiv`, `schroeterExponent`, `schroeterTerm_reindex`.
* `hasSum_schroeterFibre`, `hasSum_schroeter`, `schroeter_formula`.

## Scope relative to the monograph

`qg:thm-schroeter` is covered in full, and generalised in three ways.

1. **Base field.**  The chapter is framed over `ℂ`; every statement here is over an arbitrary
   complete normed field `𝕜`, so it also covers `ℝ` and the `p`-adic fields.  The only analytic
   input is a real majorant.
2. **Mode of convergence.**  The TeX writes `∑_{n ∈ ℤ}` with no summation order specified.
   `hasSum_schroeter` and `hasSum_schroeterFibre` assert `HasSum` over `Fin (a+b)` and over
   `ℤ × ℤ`, i.e. unconditional summability, which is what licenses the lattice partition;
   `summable_norm_quadThetaTerm` records absolute summability separately.
3. **The exponent hypotheses** `0 < a`, `0 < b` are exactly "positive integers"; no
   generalisation is available there, since at `a = 0` the base `q^0 = 1` gives a divergent
   series.

**Not covered.**  (i) The degenerate base `q = 0`.  The identity does still hold there under the
chapter's own zeroth-power convention — both sides collapse to `1` — but the whole proof below is
`zpow` algebra through `zpow_add₀`, and `0 < |q|` is the chapter's own hypothesis.  (ii) The
`ϑ₂/ϑ₃/ϑ₄` crosswalk table preceding the theorem, which needs `q = e^{iπτ}`, `ζ = e^{2πiz}` and
the rational powers `q^{1/4}`, `ζ^{1/2}`: that is analytic, not `q`-algebraic.  (iii) The remark
"Sublattice cosets and diagonalization", which "asserts no additional identity"; its content is
reflected in the shape of `schroeterEquiv` and in `schroeterExponent`, not as separate theorems.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-! ## The quadratic bilateral theta series -/

/-- The crosswalk of summands: `Q^{n²} x^n = (Q²)^{n(n-1)/2} (Qx)^n`, valid for `Q ≠ 0` and every
integer `n`.  This is the term-by-term form of the monograph's displayed identity
`Θ(x; Q) = θ(Qx; Q²)`. -/
theorem quadThetaTerm_eq {Q : 𝕜} (hQ0 : Q ≠ 0) (x : 𝕜) (n : ℤ) :
    Q ^ (n ^ 2) * x ^ n = (Q ^ 2) ^ thetaExponent n * (Q * x) ^ n := by
  have hexp : ((2 * thetaExponent n : ℕ) : ℤ) = n ^ 2 - n := by
    push_cast
    linear_combination two_mul_thetaExponent n
  have h2 : ((Q : 𝕜) ^ 2) ^ thetaExponent n = Q ^ (n ^ 2 - n) := by
    rw [← pow_mul, ← zpow_natCast Q (2 * thetaExponent n), hexp]
  rw [h2, mul_zpow, ← mul_assoc, ← zpow_add₀ hQ0, show n ^ 2 - n + n = n ^ 2 by ring]

/-- **Absolute convergence of the quadratic theta series.**  The monograph asserts, without
exhibiting a majorant, that "the quadratic exponent makes this series absolutely convergent";
the majorant is `‖Q²‖^{n(n-1)/2} ‖Qx‖^n`, summable over `ℤ` by
`summable_pow_thetaExponent_mul_zpow`. -/
theorem summable_norm_quadThetaTerm {Q : 𝕜} (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) {x : 𝕜} (hx : x ≠ 0) :
    Summable fun n : ℤ => ‖Q ^ (n ^ 2) * x ^ n‖ := by
  have hQ2 : ‖(Q : 𝕜) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg Q) hQ (by norm_num)
  have hQx : (Q : 𝕜) * x ≠ 0 := mul_ne_zero hQ0 hx
  have hsum := summable_pow_thetaExponent_mul_zpow (norm_nonneg ((Q : 𝕜) ^ 2)) hQ2
    (norm_pos_iff.mpr hQx)
  refine hsum.congr fun n => ?_
  simp only [quadThetaTerm_eq hQ0 x n, norm_mul, norm_pow, norm_zpow]

/-- The **quadratic bilateral theta series** `Θ(x; Q) = ∑_{n ∈ ℤ} Q^{n²} x^n` of the
monograph. -/
def quadTheta (Q x : 𝕜) : 𝕜 := ∑' n : ℤ, Q ^ (n ^ 2) * x ^ n

/-- For `‖Q‖ < 1`, `Q ≠ 0` and `x ≠ 0` the quadratic theta family is unconditionally summable,
with sum `quadTheta Q x`. -/
theorem hasSum_quadTheta {Q : 𝕜} (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) {x : 𝕜} (hx : x ≠ 0) :
    HasSum (fun n : ℤ => Q ^ (n ^ 2) * x ^ n) (quadTheta Q x) :=
  ((summable_norm_quadThetaTerm hQ hQ0 hx).of_norm).hasSum

/-- **The crosswalk to the bilateral Jacobi series**: `Θ(x; Q) = θ(Qx; Q²)`.  The monograph
displays this under the hypothesis `|Q| < 1` alone; `Q ≠ 0` is what makes the right-hand side the
object whose zero set and quasi-periodicity were established, and it is supplied here. -/
theorem quadTheta_eq_bilateralTheta {Q : 𝕜} (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) {x : 𝕜} (hx : x ≠ 0) :
    quadTheta Q x = bilateralTheta (Q ^ 2) (Q * x) := by
  have hQ2 : ‖(Q : 𝕜) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg Q) hQ (by norm_num)
  have h2 : HasSum (fun n : ℤ => Q ^ (n ^ 2) * x ^ n) (bilateralTheta (Q ^ 2) (Q * x)) :=
    (hasSum_bilateralTheta hQ2 (mul_ne_zero hQ0 hx)).congr_fun fun n => quadThetaTerm_eq hQ0 x n
  exact (hasSum_quadTheta hQ hQ0 hx).unique h2

/-- **Jacobi's triple product in the quadratic normalisation**:
`Θ(x; Q) = (-Qx; Q²)_∞ (-Q/x; Q²)_∞ (Q²; Q²)_∞`.  The monograph uses this shape implicitly in its
`ϑ₃` and `ϑ₄` product formulas. -/
theorem quadTheta_eq_prod {Q : 𝕜} (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) {x : 𝕜} (hx : x ≠ 0) :
    quadTheta Q x = qPochhammerInfIn (-(Q * x)) (Q ^ 2) * qPochhammerInfIn (-(Q / x)) (Q ^ 2) *
      qPochhammerInfIn (Q ^ 2) (Q ^ 2) := by
  have hQ2 : ‖(Q : 𝕜) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg Q) hQ (by norm_num)
  have hdiv : (Q : 𝕜) ^ 2 / (Q * x) = Q / x := by
    rw [div_eq_div_iff (mul_ne_zero hQ0 hx) hx]
    ring
  rw [quadTheta_eq_bilateralTheta hQ hQ0 hx, bilateralTheta_eq_prod hQ2 (mul_ne_zero hQ0 hx),
    hdiv]

/-! ## Powers of a common base

The two factors of Schröter's formula have bases `q^a` and `q^b`, and the two factors of each
fibre have bases `q^{a+b}` and `q^{ab(a+b)}`.  The next three lemmas package a quadratic theta
series at base `q^c` as a family with exponent `q^{C n²}`, where `C` is any integer equal to `c`;
this is what lets all the exponent bookkeeping below stay inside `ℤ`. -/

/-- `(u^c)^n = u^{cn}` for a natural power raised to an integer power. -/
theorem natPow_zpow_eq (u : 𝕜) (c : ℕ) (n : ℤ) : (u ^ c) ^ n = u ^ ((c : ℤ) * n) := by
  rw [zpow_mul, zpow_natCast]

/-- The quadratic theta series at base `q^c`, written with an integer exponent coefficient. -/
theorem hasSum_quadTheta_pow {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {c : ℕ} (hc : c ≠ 0) {C : ℤ}
    (hC : (c : ℤ) = C) {x : 𝕜} (hx : x ≠ 0) :
    HasSum (fun n : ℤ => q ^ (C * n ^ 2) * x ^ n) (quadTheta (q ^ c) x) := by
  subst hC
  have hQ : ‖(q : 𝕜) ^ c‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hc
  refine (hasSum_quadTheta hQ (pow_ne_zero c hq0) hx).congr_fun fun n => ?_
  simp only [natPow_zpow_eq]

/-- Absolute summability of the quadratic theta family at base `q^c`. -/
theorem summable_norm_quadThetaTerm_pow {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {c : ℕ} (hc : c ≠ 0)
    {C : ℤ} (hC : (c : ℤ) = C) {x : 𝕜} (hx : x ≠ 0) :
    Summable fun n : ℤ => ‖q ^ (C * n ^ 2) * x ^ n‖ := by
  subst hC
  have hQ : ‖(q : 𝕜) ^ c‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hc
  refine (summable_norm_quadThetaTerm hQ (pow_ne_zero c hq0) hx).congr fun n => ?_
  simp only [natPow_zpow_eq]

set_option maxHeartbeats 2000000 in
/-- **The product of two quadratic theta series as a single unconditionally summable family over
`ℤ × ℤ`.**  This is the analytic content that the monograph compresses into "absolute convergence
justifies the partition and rearrangement". -/
theorem hasSum_quadTheta_mul {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {c d : ℕ} (hc : c ≠ 0)
    (hd : d ≠ 0) {C D : ℤ} (hC : (c : ℤ) = C) (hD : (d : ℤ) = D) {z w : 𝕜} (hz : z ≠ 0)
    (hw : w ≠ 0) :
    HasSum (fun p : ℤ × ℤ => q ^ (C * p.1 ^ 2) * z ^ p.1 * (q ^ (D * p.2 ^ 2) * w ^ p.2))
      (quadTheta (q ^ c) z * quadTheta (q ^ d) w) := by
  -- Name the two factors and the product family first.  `HasSum.mul` leaves `f` and `g`
  -- implicit, and letting it guess them from the fused lambda in the goal is what exhausted
  -- the elaborator here.
  have hf : HasSum (fun n : ℤ => q ^ (C * n ^ 2) * z ^ n) (quadTheta (q ^ c) z) :=
    hasSum_quadTheta_pow hq hq0 hc hC hz
  have hg : HasSum (fun m : ℤ => q ^ (D * m ^ 2) * w ^ m) (quadTheta (q ^ d) w) :=
    hasSum_quadTheta_pow hq hq0 hd hD hw
  have hs : Summable (fun p : ℤ × ℤ =>
      q ^ (C * p.1 ^ 2) * z ^ p.1 * (q ^ (D * p.2 ^ 2) * w ^ p.2)) :=
    summable_mul_of_summable_norm (summable_norm_quadThetaTerm_pow hq hq0 hc hC hz)
      (summable_norm_quadThetaTerm_pow hq hq0 hd hD hw)
  exact hf.mul hg hs

/-! ## The dissection of the lattice

The change of variables `(k, (r, s)) ↦ (r - b s, k + r + a s)` is built from
`Int.divModEquiv (a+b)`, which splits `m - n` into its quotient `s` and its residue `k` modulo
`a + b`. -/

/-- The defining formula for the inverse of `Int.divModEquiv`. -/
theorem divModEquiv_symm_mk (N : ℕ) [NeZero N] (s : ℤ) (k : Fin N) :
    (Int.divModEquiv N).symm (s, k) = s * (N : ℤ) + ((k : ℕ) : ℤ) := rfl

/-- `Int.divModEquiv` inverts the parametrisation `(s, k) ↦ sN + k` of `ℤ`. -/
theorem divModEquiv_apply_mk (N : ℕ) [NeZero N] (s : ℤ) (k : Fin N) :
    Int.divModEquiv N (s * (N : ℤ) + ((k : ℕ) : ℤ)) = (s, k) := by
  rw [← divModEquiv_symm_mk N s k]
  exact (Int.divModEquiv N).apply_symm_apply _

/-- The division algorithm packaged by `Int.divModEquiv`: quotient times `N`, plus residue. -/
theorem divModEquiv_spec (N : ℕ) [NeZero N] (d : ℤ) :
    (Int.divModEquiv N d).1 * (N : ℤ) + (((Int.divModEquiv N d).2 : ℕ) : ℤ) = d := by
  rw [← divModEquiv_symm_mk N (Int.divModEquiv N d).1 (Int.divModEquiv N d).2]
  exact (Int.divModEquiv N).symm_apply_apply d

/-- **The Schröter dissection of `ℤ²`.**  A lattice point `(n, m)` is sent to the residue
`k ≡ m - n (mod a+b)` together with the coordinates `(r, s)` of the corresponding point of the
index-`(a+b)` sublattice; the inverse is the monograph's change of variables `n = r - b s`,
`m = k + r + a s`.  Its linear part `(r, s) ↦ (r - b s, r + a s)` has determinant `a + b`, which
is why the residues `k = 0, …, a+b-1` exhaust the cosets. -/
def schroeterEquiv (a b : ℕ) [NeZero (a + b)] : ℤ × ℤ ≃ Fin (a + b) × (ℤ × ℤ) where
  toFun p :=
    ((Int.divModEquiv (a + b) (p.2 - p.1)).2,
      (p.1 + (b : ℤ) * (Int.divModEquiv (a + b) (p.2 - p.1)).1,
        (Int.divModEquiv (a + b) (p.2 - p.1)).1))
  invFun p := (p.2.1 - (b : ℤ) * p.2.2, ((p.1 : ℕ) : ℤ) + p.2.1 + (a : ℤ) * p.2.2)
  left_inv := by
    rintro ⟨n, m⟩
    have hN : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := Nat.cast_add a b
    have hspec := divModEquiv_spec (a + b) (m - n)
    rw [hN] at hspec
    refine Prod.ext ?_ ?_
    · show n + (b : ℤ) * (Int.divModEquiv (a + b) (m - n)).1
          - (b : ℤ) * (Int.divModEquiv (a + b) (m - n)).1 = n
      ring
    · show (((Int.divModEquiv (a + b) (m - n)).2 : ℕ) : ℤ)
          + (n + (b : ℤ) * (Int.divModEquiv (a + b) (m - n)).1)
          + (a : ℤ) * (Int.divModEquiv (a + b) (m - n)).1 = m
      linear_combination hspec
  right_inv := by
    rintro ⟨k, r, s⟩
    have hd : ((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s)
        = s * ((a + b : ℕ) : ℤ) + ((k : ℕ) : ℤ) := by
      push_cast
      ring
    have hdm : Int.divModEquiv (a + b)
        (((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s)) = (s, k) := by
      rw [hd]
      exact divModEquiv_apply_mk (a + b) s k
    have hdm1 : (Int.divModEquiv (a + b)
        (((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s))).1 = s := by rw [hdm]
    have hdm2 : (Int.divModEquiv (a + b)
        (((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s))).2 = k := by rw [hdm]
    refine Prod.ext ?_ ?_
    · show (Int.divModEquiv (a + b)
          (((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s))).2 = k
      exact hdm2
    · refine Prod.ext ?_ ?_
      · show r - (b : ℤ) * s + (b : ℤ) * (Int.divModEquiv (a + b)
            (((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s))).1 = r
        rw [hdm1]
        ring
      · show (Int.divModEquiv (a + b)
            (((k : ℕ) : ℤ) + r + (a : ℤ) * s - (r - (b : ℤ) * s))).1 = s
        exact hdm1

/-- The inverse of `schroeterEquiv` is the monograph's change of variables `n = r - b s`,
`m = k + r + a s`. -/
theorem schroeterEquiv_symm_apply (a b : ℕ) [NeZero (a + b)] (p : Fin (a + b) × (ℤ × ℤ)) :
    (schroeterEquiv a b).symm p
      = (p.2.1 - (b : ℤ) * p.2.2, ((p.1 : ℕ) : ℤ) + p.2.1 + (a : ℤ) * p.2.2) := rfl

/-! ## The exponent identity and the reindexed summand -/

/-- **The diagonalisation of the quadratic form.**  With `n = r - Bs` and `m = k + r + As`,

`A n² + B m² = (A+B) r² + 2Bkr + Bk² + AB(A+B) s² + 2ABks`;

the mixed `rs` term cancels.  This is the second displayed substitution formula of the
monograph's proof; it holds over `ℤ` for all integers, positive or not. -/
theorem schroeterExponent (A B k r s : ℤ) :
    A * (r - B * s) ^ 2 + B * (k + r + A * s) ^ 2
      = (A + B) * r ^ 2 + 2 * B * k * r + B * k ^ 2 + A * B * (A + B) * s ^ 2
        + 2 * A * B * k * s := by
  ring

/-- The `(n, m)` term of the product of the two quadratic theta series at bases `q^A`, `q^B`. -/
def schroeterTerm (q x y : 𝕜) (A B : ℤ) (p : ℤ × ℤ) : 𝕜 :=
  q ^ (A * p.1 ^ 2) * x ^ p.1 * (q ^ (B * p.2 ^ 2) * y ^ p.2)

/-- The defining formula for `schroeterTerm`. -/
theorem schroeterTerm_def (q x y : 𝕜) (A B n m : ℤ) :
    schroeterTerm q x y A B (n, m) = q ^ (A * n ^ 2) * x ^ n * (q ^ (B * m ^ 2) * y ^ m) := rfl

/-- **The substituted summand**: both displayed substitution formulas of the monograph's proof at
once.  With `n = r - Bs` and `m = k + r + As`,

`q^{A n² + B m²} x^n y^m
  = y^k q^{Bk²} · q^{(A+B) r²} (x y q^{2Bk})^r · q^{AB(A+B) s²} (y^A x^{-B} q^{2ABk})^s`. -/
theorem schroeterTerm_reindex {q : 𝕜} (hq0 : q ≠ 0) {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0)
    (A B k r s : ℤ) :
    schroeterTerm q x y A B (r - B * s, k + r + A * s)
      = y ^ k * q ^ (B * k ^ 2) *
        (q ^ ((A + B) * r ^ 2) * (x * y * q ^ (2 * B * k)) ^ r *
          (q ^ (A * B * (A + B) * s ^ 2) * (y ^ A * x ^ (-B) * q ^ (2 * A * B * k)) ^ s)) := by
  have e1 : ((x * y * q ^ (2 * B * k)) ^ r : 𝕜) = x ^ r * y ^ r * q ^ (2 * B * k * r) := by
    rw [mul_zpow, mul_zpow, ← zpow_mul]
  have e2 : ((y ^ A * x ^ (-B) * q ^ (2 * A * B * k)) ^ s : 𝕜)
      = y ^ (A * s) * x ^ (-B * s) * q ^ (2 * A * B * k * s) := by
    rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  have hqL : (q : 𝕜) ^ (A * (r - B * s) ^ 2 + B * (k + r + A * s) ^ 2)
      = q ^ ((A + B) * r ^ 2) * q ^ (2 * B * k * r) * q ^ (B * k ^ 2) *
        q ^ (A * B * (A + B) * s ^ 2) * q ^ (2 * A * B * k * s) := by
    rw [schroeterExponent A B k r s, zpow_add₀ hq0, zpow_add₀ hq0, zpow_add₀ hq0, zpow_add₀ hq0]
  have hxx : (x : 𝕜) ^ (r - B * s) = x ^ r * x ^ (-B * s) := by
    rw [show r - B * s = r + -B * s by ring, zpow_add₀ hx]
  have hyy : (y : 𝕜) ^ (k + r + A * s) = y ^ k * y ^ r * y ^ (A * s) := by
    rw [zpow_add₀ hy, zpow_add₀ hy]
  have hL : schroeterTerm q x y A B (r - B * s, k + r + A * s)
      = q ^ (A * (r - B * s) ^ 2 + B * (k + r + A * s) ^ 2) * x ^ (r - B * s) *
        y ^ (k + r + A * s) := by
    rw [schroeterTerm_def, zpow_add₀ hq0]
    ring
  have hR : y ^ k * q ^ (B * k ^ 2) *
      (q ^ ((A + B) * r ^ 2) * (x * y * q ^ (2 * B * k)) ^ r *
        (q ^ (A * B * (A + B) * s ^ 2) * (y ^ A * x ^ (-B) * q ^ (2 * A * B * k)) ^ s))
      = q ^ (A * (r - B * s) ^ 2 + B * (k + r + A * s) ^ 2) * x ^ (r - B * s) *
        y ^ (k + r + A * s) := by
    rw [e1, e2, hqL, hxx, hyy]
    ring
  exact hL.trans hR.symm

/-- The `k`-th summand of the right-hand side of Schröter's formula:
`y^k q^{bk²} Θ(x y q^{2bk}; q^{a+b}) Θ(y^a x^{-b} q^{2abk}; q^{ab(a+b)})`. -/
def schroeterSummand (q x y : 𝕜) (a b k : ℕ) : 𝕜 :=
  y ^ k * q ^ (b * k ^ 2) *
    (quadTheta (q ^ (a + b)) (x * y * q ^ (2 * b * k)) *
      quadTheta (q ^ (a * b * (a + b))) (y ^ a / x ^ b * q ^ (2 * a * b * k)))

/-- The defining formula for `schroeterSummand`. -/
theorem schroeterSummand_def (q x y : 𝕜) (a b k : ℕ) :
    schroeterSummand q x y a b k
      = y ^ k * q ^ (b * k ^ 2) *
        (quadTheta (q ^ (a + b)) (x * y * q ^ (2 * b * k)) *
          quadTheta (q ^ (a * b * (a + b))) (y ^ a / x ^ b * q ^ (2 * a * b * k))) := rfl

/-! ## Schröter's formula -/

/-- **The fibre sum.**  For each residue `k`, the `(r, s)` fibre of the reindexed lattice family
sums to the `k`-th summand of Schröter's formula. -/
theorem hasSum_schroeterFibre {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {x y : 𝕜} (hx : x ≠ 0)
    (hy : y ≠ 0) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    HasSum (fun p : ℤ × ℤ =>
        schroeterTerm q x y (a : ℤ) (b : ℤ)
          (p.1 - (b : ℤ) * p.2, (k : ℤ) + p.1 + (a : ℤ) * p.2))
      (schroeterSummand q x y a b k) := by
  have hab : 0 < a + b := by omega
  have habb : 0 < a * b * (a + b) := mul_pos (mul_pos ha hb) hab
  have hzarg : x * y * q ^ (2 * (b : ℤ) * (k : ℤ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx hy) (zpow_ne_zero _ hq0)
  have hwarg : y ^ (a : ℤ) * x ^ (-(b : ℤ)) * q ^ (2 * (a : ℤ) * (b : ℤ) * (k : ℤ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hy) (zpow_ne_zero _ hx)) (zpow_ne_zero _ hq0)
  have hC : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := Nat.cast_add a b
  have hD : ((a * b * (a + b) : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) * ((a : ℤ) + (b : ℤ)) := by
    push_cast
    try ring
  have hinner := hasSum_quadTheta_mul hq hq0 hab.ne' habb.ne' hC hD hzarg hwarg
  have hcast1 : (b : ℤ) * (k : ℤ) ^ 2 = ((b * k ^ 2 : ℕ) : ℤ) := by
    push_cast
    try ring
  have hcast2 : 2 * (b : ℤ) * (k : ℤ) = ((2 * b * k : ℕ) : ℤ) := by
    push_cast
    try ring
  have hcast3 : 2 * (a : ℤ) * (b : ℤ) * (k : ℤ) = ((2 * a * b * k : ℕ) : ℤ) := by
    push_cast
    try ring
  have hq1 : (q : 𝕜) ^ ((b : ℤ) * (k : ℤ) ^ 2) = q ^ (b * k ^ 2) := by
    rw [hcast1, zpow_natCast]
  have hq2 : (q : 𝕜) ^ (2 * (b : ℤ) * (k : ℤ)) = q ^ (2 * b * k) := by
    rw [hcast2, zpow_natCast]
  have hq3 : (q : 𝕜) ^ (2 * (a : ℤ) * (b : ℤ) * (k : ℤ)) = q ^ (2 * a * b * k) := by
    rw [hcast3, zpow_natCast]
  have hyx : (y : 𝕜) ^ (a : ℤ) * x ^ (-(b : ℤ)) = y ^ a / x ^ b := by
    rw [zpow_natCast y a, zpow_neg x (b : ℤ), zpow_natCast x b, div_eq_mul_inv]
  have hval : y ^ (k : ℤ) * q ^ ((b : ℤ) * (k : ℤ) ^ 2) *
      (quadTheta (q ^ (a + b)) (x * y * q ^ (2 * (b : ℤ) * (k : ℤ))) *
        quadTheta (q ^ (a * b * (a + b)))
          (y ^ (a : ℤ) * x ^ (-(b : ℤ)) * q ^ (2 * (a : ℤ) * (b : ℤ) * (k : ℤ))))
      = schroeterSummand q x y a b k := by
    rw [schroeterSummand_def, zpow_natCast y k, hq1, hyx, hq2, hq3]
  rw [← hval]
  exact (hinner.mul_left (y ^ (k : ℤ) * q ^ ((b : ℤ) * (k : ℤ) ^ 2))).congr_fun fun p =>
    schroeterTerm_reindex hq0 hx hy (a : ℤ) (b : ℤ) (k : ℤ) p.1 p.2

/-- **Schröter's lattice dissection**, in `HasSum` form: the `a + b` summands of the right-hand
side form an unconditionally summable family over `Fin (a+b)`, with sum
`Θ(x; q^a) Θ(y; q^b)`. -/
theorem hasSum_schroeter {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun k : Fin (a + b) => schroeterSummand q x y a b (k : ℕ))
      (quadTheta (q ^ a) x * quadTheta (q ^ b) y) := by
  haveI : NeZero (a + b) := ⟨by omega⟩
  have hLHS : HasSum (schroeterTerm q x y (a : ℤ) (b : ℤ))
      (quadTheta (q ^ a) x * quadTheta (q ^ b) y) :=
    (hasSum_quadTheta_mul hq hq0 ha.ne' hb.ne' rfl rfl hx hy).congr_fun fun _ => rfl
  have hcomp : HasSum (fun p : Fin (a + b) × (ℤ × ℤ) =>
      schroeterTerm q x y (a : ℤ) (b : ℤ)
        (p.2.1 - (b : ℤ) * p.2.2, ((p.1 : ℕ) : ℤ) + p.2.1 + (a : ℤ) * p.2.2))
      (quadTheta (q ^ a) x * quadTheta (q ^ b) y) := by
    refine (((schroeterEquiv a b).symm.hasSum_iff).mpr hLHS).congr_fun fun p => ?_
    show schroeterTerm q x y (a : ℤ) (b : ℤ)
        (p.2.1 - (b : ℤ) * p.2.2, ((p.1 : ℕ) : ℤ) + p.2.1 + (a : ℤ) * p.2.2)
      = schroeterTerm q x y (a : ℤ) (b : ℤ) ((schroeterEquiv a b).symm p)
    rw [schroeterEquiv_symm_apply]
  exact hcomp.prod_fiberwise fun k => hasSum_schroeterFibre hq hq0 hx hy ha hb (k : ℕ)

/-- **Schröter's lattice dissection** (`qg:thm-schroeter`).  For positive integers `a`, `b`, for
`‖q‖ < 1`, `q ≠ 0` and `x, y ≠ 0` in a complete normed field,

`Θ(x; q^a) Θ(y; q^b)
  = ∑_{k=0}^{a+b-1} y^k q^{bk²} Θ(x y q^{2bk}; q^{a+b}) Θ(y^a x^{-b} q^{2abk}; q^{ab(a+b)})`.

Every exponent on the right is a natural number; the only negative power of the monograph's
statement is its `x^{-b}`, written here as `y^a / x^b`. -/
theorem schroeter_formula {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    quadTheta (q ^ a) x * quadTheta (q ^ b) y
      = ∑ k ∈ Finset.range (a + b),
          y ^ k * q ^ (b * k ^ 2) *
            (quadTheta (q ^ (a + b)) (x * y * q ^ (2 * b * k)) *
              quadTheta (q ^ (a * b * (a + b))) (y ^ a / x ^ b * q ^ (2 * a * b * k))) := by
  have hfin : (∑ k : Fin (a + b), schroeterSummand q x y a b (k : ℕ))
      = ∑ k ∈ Finset.range (a + b),
          y ^ k * q ^ (b * k ^ 2) *
            (quadTheta (q ^ (a + b)) (x * y * q ^ (2 * b * k)) *
              quadTheta (q ^ (a * b * (a + b))) (y ^ a / x ^ b * q ^ (2 * a * b * k))) :=
    Fin.sum_univ_eq_sum_range (fun k => schroeterSummand q x y a b k) (a + b)
  rw [← hfin]
  exact (hasSum_schroeter hq hq0 hx hy ha hb).unique (hasSum_fintype _)

end

end Fabius
