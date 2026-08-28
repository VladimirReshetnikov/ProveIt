import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Euler log transform of an absolutely summable family

The single analytic mechanism behind every "logarithm of an Euler
product = zeta-type series" identity in the Fabius corpus: for a family
`a : ι → ℝ` or `ι → ℂ` with `‖a i‖ < 1` for every `i` and `∑ ‖a i‖ < ∞`,

`∑' i, log (1 - a i) = -∑'_{r ≥ 1} (∑' i, (a i)^r) / r`,

together with the branch-free multiplicative form

`∏' i, (1 - a i) = exp (-∑'_{r ≥ 1} (∑' i, (a i)^r) / r)`.

The inner sums `∑' i, (a i)^r` are the *power sums* of the family; the
transform trades one logarithm per factor for one zeta-type value per
order.  The frontier drafts use the case `ι = ℕ`, `a n = z²/(π²(n+1)²)`
(Euler–zeta expansion of `log sinc`, `lem:logsinc`) and its dyadic-shell
refinement over `ι = ℕ × ℕ`; the statement here is for an **arbitrary**
index type, with the sharp hypotheses (no uniform bound `q < 1` is
needed — summability forces the norms to cluster at `0`, and the
per-index bound `‖a i‖ < 1` is exactly what makes each logarithm's
Taylor series converge).

The proof is one absolutely convergent double series, swapped along its
two fiberings: over `i` first it collapses fiberwise to the Taylor
series of `-log (1 - a i)`; over `r` first each fiber is a power sum.
`HasSum.prod_fiberwise` does both interchanges.

* `summable_pow_div_succ_of_lt_one` — the absolute double family
  `b i ^ (r+1) / (r+1)` is summable over `ι × ℕ` when `0 ≤ b i < 1`
  and `∑ b i < ∞`.
* `hasSum_powerSum_log_one_sub` / `hasSum_powerSum_log_one_sub_real` —
  the transform, as a `HasSum` over the order `r`.
* `tsum_log_one_sub` / `tsum_log_one_sub_real` — the `tsum` form.
* `tprod_one_sub_eq_cexp_powerSum` / `tprod_one_sub_eq_rexp_powerSum` —
  the exponential form for the infinite product, with no branch choice.
* `tsum_log_one_sub_geom`, `tprod_one_sub_geom_eq_cexp` (and `_real`
  versions) — the geometric instance `a k = w·cᵏ`: the classical
  Lambert-series logarithm of the infinite `q`-Pochhammer product,
  `log ∏ (1 - w cᵏ) = -∑_{r≥1} wʳ / (r (1 - cʳ))` for `‖w‖ < 1`,
  `‖c‖ < 1`.  This is the kernel behind the `q = 1/4` Lambert
  coefficient array of the sinc-tail calculus (`eq:Q-Lambert`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {ι : Type*}

/-- **Absolute summability of the double family** `b i ^ (r+1) / (r+1)`
over `ι × ℕ`, for a nonnegative summable family with every entry
strictly below `1`.  The fiber over `i` sums to `-log (1 - b i)`, and
those logs are summable because `b` is; no uniform gap below `1` is
required. -/
theorem summable_pow_div_succ_of_lt_one {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hb1 : ∀ i, b i < 1) (hsum : Summable b) :
    Summable fun p : ι × ℕ => b p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1) := by
  have habs : ∀ i, |b i| < 1 := fun i => by
    rw [abs_of_nonneg (hb0 i)]
    exact hb1 i
  have hfiber : ∀ i, HasSum (fun n : ℕ => b i ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - b i)) := fun i =>
    Real.hasSum_pow_div_log_of_abs_lt_one (habs i)
  have hlog : Summable fun i => Real.log (1 - b i) := by
    have h := Real.summable_log_one_add_of_summable hsum.neg
    simpa [sub_eq_add_neg] using h
  have hf0 : (0 : ι × ℕ → ℝ) ≤ fun p => b p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1) :=
    fun p => div_nonneg (pow_nonneg (hb0 p.1) _) (by positivity)
  refine (summable_prod_of_nonneg hf0).mpr
    ⟨fun i => (hfiber i).summable, ?_⟩
  refine hlog.neg.congr fun i => ?_
  exact (hfiber i).tsum_eq.symm

section ComplexEngine

variable {a : ι → ℂ}

/-- **The Euler log transform** (complex): for an absolutely summable
family with `‖a i‖ < 1`, the power sums `∑' i, (a i)^(r+1)`, weighted by
`1/(r+1)`, sum over the order `r` to `-∑' i, log (1 - a i)`.

This is the double-series interchange
`∑_i log (1 - a i) = -∑_i ∑_{r≥1} (a i)^r / r = -∑_{r≥1} (∑_i (a i)^r) / r`,
performed by fiberwise summation of one absolutely convergent family
over `ι × ℕ`. -/
theorem hasSum_powerSum_log_one_sub (hlt : ∀ i, ‖a i‖ < 1)
    (hsum : Summable fun i => ‖a i‖) :
    HasSum (fun r : ℕ => (∑' i, a i ^ (r + 1)) / ((r : ℂ) + 1))
      (-∑' i, Complex.log (1 - a i)) := by
  have habs : Summable fun p : ι × ℕ => ‖a p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1)‖ := by
    refine (summable_pow_div_succ_of_lt_one (fun i => norm_nonneg _) hlt hsum).congr
      fun p => ?_
    rw [norm_div, norm_pow,
      show ((p.2 : ℂ) + 1) = ((p.2 + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast
    ring
  have hF : Summable fun p : ι × ℕ => a p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) :=
    habs.of_norm
  have hfiber : ∀ i, HasSum (fun r : ℕ => a i ^ (r + 1) / ((r : ℂ) + 1))
      (-Complex.log (1 - a i)) := by
    intro i
    have h' := (hasSum_nat_add_iff' 1).mpr
      (Complex.hasSum_taylorSeries_neg_log (hlt i))
    simpa [Finset.range_one] using h'
  have htotal : HasSum (fun i => -Complex.log (1 - a i))
      (∑' p : ι × ℕ, a p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1)) :=
    hF.hasSum.prod_fiberwise hfiber
  have hswap : Summable fun q : ℕ × ι => a q.2 ^ (q.1 + 1) / ((q.1 : ℂ) + 1) :=
    hF.prod_symm
  have hfiber2 : ∀ r : ℕ, HasSum (fun i => a i ^ (r + 1) / ((r : ℂ) + 1))
      ((∑' i, a i ^ (r + 1)) / ((r : ℂ) + 1)) := by
    intro r
    have hpow : Summable fun i => a i ^ (r + 1) := by
      refine ((hswap.prod_factor r).mul_right ((r : ℂ) + 1)).congr fun i => ?_
      exact div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero r)
    exact hpow.hasSum.div_const _
  have htotal2 : HasSum (fun r : ℕ => (∑' i, a i ^ (r + 1)) / ((r : ℂ) + 1))
      (∑' q : ℕ × ι, a q.2 ^ (q.1 + 1) / ((q.1 : ℂ) + 1)) :=
    hswap.hasSum.prod_fiberwise hfiber2
  have hval : (∑' q : ℕ × ι, a q.2 ^ (q.1 + 1) / ((q.1 : ℂ) + 1))
      = -∑' i, Complex.log (1 - a i) := by
    calc ∑' q : ℕ × ι, a q.2 ^ (q.1 + 1) / ((q.1 : ℂ) + 1)
        = ∑' p : ι × ℕ, a p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) := by
          simpa using (Equiv.prodComm ℕ ι).tsum_eq
            (fun p : ι × ℕ => a p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1))
      _ = ∑' i, -Complex.log (1 - a i) := htotal.tsum_eq.symm
      _ = -∑' i, Complex.log (1 - a i) := tsum_neg
  rwa [hval] at htotal2

/-- The `tsum` form of the complex Euler log transform:
`∑' i, log (1 - a i) = -∑'_{r} (∑' i, (a i)^(r+1)) / (r+1)`. -/
theorem tsum_log_one_sub (hlt : ∀ i, ‖a i‖ < 1)
    (hsum : Summable fun i => ‖a i‖) :
    ∑' i, Complex.log (1 - a i) =
      -∑' r : ℕ, (∑' i, a i ^ (r + 1)) / ((r : ℂ) + 1) := by
  rw [(hasSum_powerSum_log_one_sub hlt hsum).tsum_eq, neg_neg]

/-- **The exponential Euler product formula** (complex, branch-free):
`∏' i, (1 - a i) = exp (-∑'_{r} (∑' i, (a i)^(r+1)) / (r+1))`.
No choice of logarithm branch enters the statement. -/
theorem tprod_one_sub_eq_cexp_powerSum (hlt : ∀ i, ‖a i‖ < 1)
    (hsum : Summable fun i => ‖a i‖) :
    ∏' i, (1 - a i) =
      Complex.exp (-∑' r : ℕ, (∑' i, a i ^ (r + 1)) / ((r : ℂ) + 1)) := by
  have hne : ∀ i, (1 : ℂ) - a i ≠ 0 := by
    intro i h
    have h1 : a i = 1 := (sub_eq_zero.mp h).symm
    have h2 := hlt i
    rw [h1, norm_one] at h2
    exact lt_irrefl 1 h2
  have hlog : Summable fun i => Complex.log (1 - a i) := by
    have h := Complex.summable_log_one_add_of_summable hsum.of_norm.neg
    simpa [sub_eq_add_neg] using h
  rw [← Complex.cexp_tsum_eq_tprod hne hlog, tsum_log_one_sub hlt hsum]

end ComplexEngine

section RealEngine

variable {a : ι → ℝ}

/-- **The Euler log transform** (real): for a summable real family with
`|a i| < 1`, the power sums `∑' i, (a i)^(r+1)`, weighted by `1/(r+1)`,
sum over the order `r` to `-∑' i, log (1 - a i)`. -/
theorem hasSum_powerSum_log_one_sub_real (hlt : ∀ i, |a i| < 1)
    (hsum : Summable a) :
    HasSum (fun r : ℕ => (∑' i, a i ^ (r + 1)) / ((r : ℝ) + 1))
      (-∑' i, Real.log (1 - a i)) := by
  have habs : Summable fun p : ι × ℕ => |a p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1)| := by
    refine (summable_pow_div_succ_of_lt_one (fun i => abs_nonneg _) hlt
      hsum.abs).congr fun p => ?_
    rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ (p.2 : ℝ) + 1)]
  have hF : Summable fun p : ι × ℕ => a p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1) :=
    summable_abs_iff.mp habs
  have hfiber : ∀ i, HasSum (fun r : ℕ => a i ^ (r + 1) / ((r : ℝ) + 1))
      (-Real.log (1 - a i)) := fun i =>
    Real.hasSum_pow_div_log_of_abs_lt_one (hlt i)
  have htotal : HasSum (fun i => -Real.log (1 - a i))
      (∑' p : ι × ℕ, a p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1)) :=
    hF.hasSum.prod_fiberwise hfiber
  have hswap : Summable fun q : ℕ × ι => a q.2 ^ (q.1 + 1) / ((q.1 : ℝ) + 1) :=
    hF.prod_symm
  have hfiber2 : ∀ r : ℕ, HasSum (fun i => a i ^ (r + 1) / ((r : ℝ) + 1))
      ((∑' i, a i ^ (r + 1)) / ((r : ℝ) + 1)) := by
    intro r
    have hpow : Summable fun i => a i ^ (r + 1) := by
      refine ((hswap.prod_factor r).mul_right ((r : ℝ) + 1)).congr fun i => ?_
      exact div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero r)
    exact hpow.hasSum.div_const _
  have htotal2 : HasSum (fun r : ℕ => (∑' i, a i ^ (r + 1)) / ((r : ℝ) + 1))
      (∑' q : ℕ × ι, a q.2 ^ (q.1 + 1) / ((q.1 : ℝ) + 1)) :=
    hswap.hasSum.prod_fiberwise hfiber2
  have hval : (∑' q : ℕ × ι, a q.2 ^ (q.1 + 1) / ((q.1 : ℝ) + 1))
      = -∑' i, Real.log (1 - a i) := by
    calc ∑' q : ℕ × ι, a q.2 ^ (q.1 + 1) / ((q.1 : ℝ) + 1)
        = ∑' p : ι × ℕ, a p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1) := by
          simpa using (Equiv.prodComm ℕ ι).tsum_eq
            (fun p : ι × ℕ => a p.1 ^ (p.2 + 1) / ((p.2 : ℝ) + 1))
      _ = ∑' i, -Real.log (1 - a i) := htotal.tsum_eq.symm
      _ = -∑' i, Real.log (1 - a i) := tsum_neg
  rwa [hval] at htotal2

/-- The `tsum` form of the real Euler log transform. -/
theorem tsum_log_one_sub_real (hlt : ∀ i, |a i| < 1) (hsum : Summable a) :
    ∑' i, Real.log (1 - a i) =
      -∑' r : ℕ, (∑' i, a i ^ (r + 1)) / ((r : ℝ) + 1) := by
  rw [(hasSum_powerSum_log_one_sub_real hlt hsum).tsum_eq, neg_neg]

/-- **The exponential Euler product formula** (real):
`∏' i, (1 - a i) = exp (-∑'_{r} (∑' i, (a i)^(r+1)) / (r+1))` for a
summable family with `|a i| < 1` — every factor is strictly positive,
and the product is the exponential of the transform. -/
theorem tprod_one_sub_eq_rexp_powerSum (hlt : ∀ i, |a i| < 1)
    (hsum : Summable a) :
    ∏' i, (1 - a i) =
      Real.exp (-∑' r : ℕ, (∑' i, a i ^ (r + 1)) / ((r : ℝ) + 1)) := by
  have hpos : ∀ i, (0:ℝ) < 1 - a i := fun i => by
    have := (abs_lt.mp (hlt i)).2
    linarith
  have hlog : Summable fun i => Real.log (1 - a i) := by
    have h := Real.summable_log_one_add_of_summable hsum.neg
    simpa [sub_eq_add_neg] using h
  rw [← Real.rexp_tsum_eq_tprod hpos hlog, tsum_log_one_sub_real hlt hsum]

end RealEngine

section GeometricInstance

/-- Norms of the geometric family `k ↦ w·cᵏ` stay below `1` when
`‖w‖ < 1` and `‖c‖ < 1`. -/
private theorem geom_norm_lt_one {w c : ℂ} (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (k : ℕ) : ‖w * c ^ k‖ < 1 := by
  rw [norm_mul, norm_pow]
  calc ‖w‖ * ‖c‖ ^ k ≤ ‖w‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg c) hc.le)
          (norm_nonneg w)
    _ = ‖w‖ := mul_one _
    _ < 1 := hw

/-- The geometric family `k ↦ w·cᵏ` is absolutely summable for `‖c‖ < 1`. -/
private theorem geom_norm_summable (w : ℂ) {c : ℂ} (hc : ‖c‖ < 1) :
    Summable fun k : ℕ => ‖w * c ^ k‖ := by
  simp_rw [norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg c) hc).mul_left ‖w‖

/-- **The Lambert-series logarithm of the geometric Euler product**
(complex): for `‖w‖ < 1` and `‖c‖ < 1`,

`∑' k, log (1 - w·cᵏ) = -∑'_{r ≥ 1} wʳ / (r (1 - cʳ))`.

The power sums of the geometric family collapse to geometric series,
producing the classical Lambert kernel `1/(1 - cʳ)`.  At `w = c = q`
this is the logarithm of the Euler function `(q; q)_∞`. -/
theorem tsum_log_one_sub_geom {w c : ℂ} (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) :
    ∑' k : ℕ, Complex.log (1 - w * c ^ k) =
      -∑' r : ℕ, w ^ (r + 1) / (((r : ℂ) + 1) * (1 - c ^ (r + 1))) := by
  rw [tsum_log_one_sub (geom_norm_lt_one hw hc) (geom_norm_summable w hc)]
  congr 1
  refine tsum_congr fun r => ?_
  have hcr : ‖c ^ (r + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg c) hc r.succ_ne_zero
  have hgeo : ∑' k : ℕ, (w * c ^ k) ^ (r + 1) =
      w ^ (r + 1) * (1 - c ^ (r + 1))⁻¹ := by
    have hterm : ∀ k : ℕ, (w * c ^ k) ^ (r + 1) =
        w ^ (r + 1) * (c ^ (r + 1)) ^ k := by
      intro k
      rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hcr]
  rw [hgeo, ← div_eq_mul_inv, div_right_comm, div_div]

/-- **The infinite `q`-Pochhammer product in exponential form**
(complex): for `‖w‖ < 1` and `‖c‖ < 1`,

`∏' k, (1 - w·cᵏ) = exp (-∑'_{r ≥ 1} wʳ / (r (1 - cʳ)))`.

This packages `(w; c)_∞` as the exponential of a Lambert series; the
`q = 1/4` case is the coefficient kernel of the dyadic sinc-tail
calculus. -/
theorem tprod_one_sub_geom_eq_cexp {w c : ℂ} (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) :
    ∏' k : ℕ, (1 - w * c ^ k) =
      Complex.exp (-∑' r : ℕ, w ^ (r + 1) / (((r : ℂ) + 1) * (1 - c ^ (r + 1)))) := by
  have hne : ∀ k : ℕ, (1 : ℂ) - w * c ^ k ≠ 0 := by
    intro k h
    have h1 : w * c ^ k = 1 := (sub_eq_zero.mp h).symm
    have h2 := geom_norm_lt_one hw hc k
    rw [h1, norm_one] at h2
    exact lt_irrefl 1 h2
  have hlog : Summable fun k : ℕ => Complex.log (1 - w * c ^ k) := by
    have h := Complex.summable_log_one_add_of_summable
      ((geom_norm_summable w hc).of_norm.neg)
    simpa [sub_eq_add_neg] using h
  rw [← Complex.cexp_tsum_eq_tprod hne hlog, tsum_log_one_sub_geom hw hc]

/-- **The Lambert-series logarithm of the geometric Euler product**
(real): for `|w| < 1` and `|c| < 1`,
`∑' k, log (1 - w·cᵏ) = -∑'_{r ≥ 1} wʳ / (r (1 - cʳ))`. -/
theorem tsum_log_one_sub_geom_real {w c : ℝ} (hw : |w| < 1) (hc : |c| < 1) :
    ∑' k : ℕ, Real.log (1 - w * c ^ k) =
      -∑' r : ℕ, w ^ (r + 1) / (((r : ℝ) + 1) * (1 - c ^ (r + 1))) := by
  have hlt : ∀ k : ℕ, |w * c ^ k| < 1 := by
    intro k
    rw [abs_mul, abs_pow]
    calc |w| * |c| ^ k ≤ |w| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg c) hc.le)
            (abs_nonneg w)
      _ = |w| := mul_one _
      _ < 1 := hw
  have hsum : Summable fun k : ℕ => w * c ^ k :=
    (summable_geometric_of_abs_lt_one hc).mul_left w
  rw [tsum_log_one_sub_real hlt hsum]
  congr 1
  refine tsum_congr fun r => ?_
  have hcr : |c ^ (r + 1)| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg c) hc r.succ_ne_zero
  have hgeo : ∑' k : ℕ, (w * c ^ k) ^ (r + 1) =
      w ^ (r + 1) * (1 - c ^ (r + 1))⁻¹ := by
    have hterm : ∀ k : ℕ, (w * c ^ k) ^ (r + 1) =
        w ^ (r + 1) * (c ^ (r + 1)) ^ k := by
      intro k
      rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    rw [tsum_congr hterm, tsum_mul_left,
      tsum_geometric_of_abs_lt_one hcr]
  rw [hgeo, ← div_eq_mul_inv, div_right_comm, div_div]

/-- **The infinite `q`-Pochhammer product in exponential form** (real):
for `|w| < 1` and `|c| < 1`,
`∏' k, (1 - w·cᵏ) = exp (-∑'_{r ≥ 1} wʳ / (r (1 - cʳ)))`. -/
theorem tprod_one_sub_geom_eq_rexp {w c : ℝ} (hw : |w| < 1) (hc : |c| < 1) :
    ∏' k : ℕ, (1 - w * c ^ k) =
      Real.exp (-∑' r : ℕ, w ^ (r + 1) / (((r : ℝ) + 1) * (1 - c ^ (r + 1)))) := by
  have hlt : ∀ k : ℕ, |w * c ^ k| < 1 := by
    intro k
    rw [abs_mul, abs_pow]
    calc |w| * |c| ^ k ≤ |w| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg c) hc.le)
            (abs_nonneg w)
      _ = |w| := mul_one _
      _ < 1 := hw
  have hsum : Summable fun k : ℕ => w * c ^ k :=
    (summable_geometric_of_abs_lt_one hc).mul_left w
  have hpos : ∀ k : ℕ, (0:ℝ) < 1 - w * c ^ k := fun k => by
    have := (abs_lt.mp (hlt k)).2
    linarith
  have hlog : Summable fun k : ℕ => Real.log (1 - w * c ^ k) := by
    have h := Real.summable_log_one_add_of_summable hsum.neg
    simpa [sub_eq_add_neg] using h
  rw [← Real.rexp_tsum_eq_tprod hpos hlog, tsum_log_one_sub_geom_real hw hc]

end GeometricInstance

end Fabius
