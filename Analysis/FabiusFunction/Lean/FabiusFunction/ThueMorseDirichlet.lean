import FabiusFunction.ThueMorseEulerTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The shifted Thue–Morse Dirichlet series, real regime

The series `D(σ,a) = ∑_{n≥0} ε(n)/(n+a)^σ` converges for every `σ > 0`
by Dirichlet's test — the sign prefix sums are bounded by one and the
shifted powers decrease to zero — even though it never converges
absolutely for `σ ≤ 1`.  Splitting even and odd indices and using
`ε(2n) = ε(n)`, `ε(2n+1) = -ε(n)` yields the atlas's dyadic parameter
equation.

* `dirichletPartial` / `thueMorseDirichlet` — the partial sums and the
  limit function.
* `dirichletPartial_cauchy` / `tendsto_thueMorseDirichlet` —
  **conditional convergence** (`prop:Dirichlet-convergence`, real
  case), via `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`
  and the prefix bound `|∑_{n<N} ε(n)| ≤ 1`.
* `thueMorseDirichlet_dyadic` — **the dyadic Dirichlet equation**
  (`thm:Dirichlet-dyadic`):
  `D(σ,a) = 2^(-σ)·(D(σ,a/2) - D(σ,(a+1)/2))`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- The partial sums of the shifted Dirichlet series. -/
noncomputable def dirichletPartial (σ a : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, ((n : ℝ) + a) ^ (-σ) * (thueMorseSign n : ℝ)

/-- The shifted powers decrease. -/
theorem antitone_shift_rpow (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) :
    Antitone (fun n : ℕ => ((n : ℝ) + a) ^ (-σ)) := by
  intro m n hmn
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
    (by have h := (Nat.cast_le (α := ℝ)).mpr hmn; linarith)
    (by linarith)

/-- The shifted powers tend to zero. -/
theorem tendsto_shift_rpow (a σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + a) ^ (-σ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + a) atTop atTop :=
    tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop hσ).comp h1

/-- The real-cast sign prefix sums are bounded by one. -/
theorem norm_sum_thueMorseSign_le_one (N : ℕ) :
    ‖∑ n ∈ range N, (thueMorseSign n : ℝ)‖ ≤ 1 := by
  have h := abs_sum_thueMorseSign_range_le_one N
  have hcast : ∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℝ) =
      ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [Real.norm_eq_abs, hcast, ← Int.cast_abs]
  exact_mod_cast h

/-- **Dirichlet's test**: the partial sums form a Cauchy sequence for
every `σ > 0` and `a > 0`. -/
theorem dirichletPartial_cauchy (σ a : ℝ) (hσ : 0 < σ) (ha : 0 < a) :
    CauchySeq (dirichletPartial σ a) := by
  have h := (antitone_shift_rpow a σ ha hσ).cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (tendsto_shift_rpow a σ hσ)
    (b := 1) (z := fun n => (thueMorseSign n : ℝ))
    norm_sum_thueMorseSign_le_one
  exact h

/-- The limit function `D(σ,a)`. -/
noncomputable def thueMorseDirichlet (σ a : ℝ) : ℝ :=
  limUnder atTop (dirichletPartial σ a)

/-- **Conditional convergence** of the shifted Dirichlet series in the
real regime (`prop:Dirichlet-convergence`). -/
theorem tendsto_thueMorseDirichlet (σ a : ℝ) (hσ : 0 < σ) (ha : 0 < a) :
    Tendsto (dirichletPartial σ a) atTop
      (𝓝 (thueMorseDirichlet σ a)) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (dirichletPartial_cauchy σ a hσ ha)
  rwa [thueMorseDirichlet, hL.limUnder_eq]

/-- Interleaving: the even-length partial sums split dyadically, for
every shift `a ≥ 0`.  The even/odd sign split is the shared
`sum_thueMorseSign_mul_two_mul`; what remains is the rpow identity
`(2n + a)^(-σ) = 2^(-σ)·(n + a/2)^(-σ)`. -/
theorem dirichletPartial_two_mul_of_nonneg (σ a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    dirichletPartial σ a (2 * N) =
      (2 : ℝ) ^ (-σ) *
        (dirichletPartial σ (a / 2) N -
          dirichletPartial σ ((a + 1) / 2) N) := by
  have hswap : dirichletPartial σ a (2 * N) =
      ∑ k ∈ range (2 * N),
        (thueMorseSign k : ℝ) * (((k : ℝ) + a) ^ (-σ)) := by
    rw [dirichletPartial]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hswap, sum_thueMorseSign_mul_two_mul N
    (fun n : ℕ => ((n : ℝ) + a) ^ (-σ)), dirichletPartial, dirichletPartial,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : ((2 * n : ℕ) : ℝ) + a = 2 * ((n : ℝ) + a / 2) := by
    push_cast
    ring
  have h2 : ((2 * n + 1 : ℕ) : ℝ) + a = 2 * ((n : ℝ) + (a + 1) / 2) := by
    push_cast
    ring
  rw [h1, h2, Real.mul_rpow (by norm_num) (by positivity),
    Real.mul_rpow (by norm_num) (by positivity)]
  ring

/-- Interleaving: the even-length partial sums split dyadically. -/
theorem dirichletPartial_two_mul (σ a : ℝ) (ha : 0 < a) (N : ℕ) :
    dirichletPartial σ a (2 * N) =
      (2 : ℝ) ^ (-σ) *
        (dirichletPartial σ (a / 2) N -
          dirichletPartial σ ((a + 1) / 2) N) :=
  dirichletPartial_two_mul_of_nonneg σ a ha.le N

/-- **The dyadic Dirichlet equation** (`thm:Dirichlet-dyadic`), real
regime: `D(σ,a) = 2^(-σ)·(D(σ,a/2) - D(σ,(a+1)/2))`. -/
theorem thueMorseDirichlet_dyadic (σ a : ℝ) (hσ : 0 < σ) (ha : 0 < a) :
    thueMorseDirichlet σ a =
      (2 : ℝ) ^ (-σ) *
        (thueMorseDirichlet σ (a / 2) -
          thueMorseDirichlet σ ((a + 1) / 2)) := by
  have h1 := tendsto_thueMorseDirichlet σ a hσ ha
  have h2 := tendsto_thueMorseDirichlet σ (a / 2) hσ (by linarith)
  have h3 := tendsto_thueMorseDirichlet σ ((a + 1) / 2) hσ (by linarith)
  have h1' : Tendsto (fun N => dirichletPartial σ a (2 * N)) atTop
      (𝓝 (thueMorseDirichlet σ a)) := h1.comp tendsto_two_mul_atTop
  have hrw : (fun N => dirichletPartial σ a (2 * N)) =
      fun N => (2 : ℝ) ^ (-σ) *
        (dirichletPartial σ (a / 2) N -
          dirichletPartial σ ((a + 1) / 2) N) :=
    funext fun N => dirichletPartial_two_mul σ a ha N
  rw [hrw] at h1'
  have hlim : Tendsto (fun N => (2 : ℝ) ^ (-σ) *
      (dirichletPartial σ (a / 2) N -
        dirichletPartial σ ((a + 1) / 2) N)) atTop
      (𝓝 ((2 : ℝ) ^ (-σ) *
        (thueMorseDirichlet σ (a / 2) -
          thueMorseDirichlet σ ((a + 1) / 2)))) :=
    ((h2.sub h3).const_mul _)
  exact tendsto_nhds_unique h1' hlim

end Fabius
