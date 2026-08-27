import FabiusFunction.ThueMorseMellin
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The entire continuation of the shifted Dirichlet series

The last analytic layer of the atlas's Dirichlet–Mellin section: the
function

`s ↦ Γ(s)⁻¹ · ∫₀^∞ t^(s-1)·e^(-at)·E(t) dt`

(with `E = lacunaryExpProduct`) is **entire** — the super-polynomial
boundary flatness of `E` kills every Mellin singularity at `0`, the
exponential factor handles infinity, and `1/Γ` is entire — and it
agrees with `D(σ,a)` on the real ray `σ > 1` by the Mellin
representation.  This is the atlas's entire continuation of `D(s,a)`,
realized through Mathlib's Mellin-transform calculus.

* `mellinKernel` — the kernel `e^(-at)·E(t)` as a complex-valued map.
* `mellinKernel_isBigO_exp` / `mellinKernel_isBigO_rpow` — decay at
  infinity and flatness of every order at `0` (from the effective
  bound `E(t) ≤ 2^(m(m-1)/2)·t^m`).
* `dirichletMellinContinuation_differentiable` — **entirety**.
* `dirichletMellinContinuation_eq` — agreement with `D(σ,a)` for
  `σ > 1`.
-/

set_option autoImplicit false

open Finset Filter MeasureTheory Set Complex Asymptotics Topology

namespace Fabius

/-- The Mellin kernel `e^(-at)·E(t)`, complex-valued. -/
noncomputable def mellinKernel (a : ℝ) : ℝ → ℂ :=
  fun t => ((Real.exp (-(a * t)) * lacunaryExpProduct t : ℝ) : ℂ)

/-- Exponential decay of the kernel at infinity. -/
theorem mellinKernel_isBigO_exp (a : ℝ) :
    (mellinKernel a) =O[atTop] fun t => Real.exp (-a * t) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h1 : 0 < lacunaryExpProduct t := lacunaryExpProduct_pos t ht
  have h2 : lacunaryExpProduct t ≤ 1 := lacunaryExpProduct_le_one t ht
  rw [mellinKernel, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity), abs_of_pos (Real.exp_pos _), one_mul,
    show -a * t = -(a * t) by ring]
  nlinarith [Real.exp_pos (-(a * t))]

/-- Flatness of every order at `0`: the kernel is `O(t^(-b))` as
`t → 0⁺` for every `b`. -/
theorem mellinKernel_isBigO_rpow (a b : ℝ) (ha : 0 < a) :
    (mellinKernel a) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-b) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -b ≤ (m : ℝ) := exists_nat_ge (-b)
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 ^ (m * (m - 1) / 2), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hE0 : 0 < lacunaryExpProduct t := lacunaryExpProduct_pos t ht0
  have hEflat : lacunaryExpProduct t ≤
      2 ^ (m * (m - 1) / 2) * t ^ m := lacunaryExpProduct_le t ht0 m
  have hexp1 : Real.exp (-(a * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hexp0 : (0 : ℝ) < Real.exp (-(a * t)) := Real.exp_pos _
  rw [mellinKernel, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity),
    abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hpow : t ^ m ≤ t ^ (-b) := by
    rw [← Real.rpow_natCast t m]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le hm
  have hmid : Real.exp (-(a * t)) * lacunaryExpProduct t ≤
      2 ^ (m * (m - 1) / 2) * t ^ m := by
    nlinarith
  have hlast : (2 : ℝ) ^ (m * (m - 1) / 2) * t ^ m ≤
      2 ^ (m * (m - 1) / 2) * t ^ (-b) := by
    have hc : (0 : ℝ) < 2 ^ (m * (m - 1) / 2) := by positivity
    nlinarith
  linarith

/-- The kernel is locally integrable on `(0,∞)`: the product of a
continuous factor and a monotone factor. -/
theorem mellinKernel_locallyIntegrable (a : ℝ) :
    LocallyIntegrableOn (mellinKernel a) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ⟨Icc (x - x / 2) (x + x / 2), ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds
      (Icc_mem_nhds (by linarith) (by linarith))
  · have hsub : Icc (x - x / 2) (x + x / 2) ⊆ Ioi 0 := by
      intro t ht
      obtain ⟨h1, _⟩ := ht
      simp only [Set.mem_Ioi]
      linarith
    have hmono : MonotoneOn (fun t => lacunaryExpProduct t)
        (Icc (x - x / 2) (x + x / 2)) := by
      intro s hs t ht hst
      exact lacunaryExpProduct_mono (hsub hs) hst
    have h1 : IntegrableOn (fun t => lacunaryExpProduct t)
        (Icc (x - x / 2) (x + x / 2)) :=
      hmono.integrableOn_isCompact isCompact_Icc
    have hcont : ContinuousOn (fun t : ℝ => Real.exp (-(a * t)))
        (Icc (x - x / 2) (x + x / 2)) :=
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn
    have h2 : IntegrableOn
        (fun t => Real.exp (-(a * t)) * lacunaryExpProduct t)
        (Icc (x - x / 2) (x + x / 2)) :=
      h1.continuousOn_mul hcont isCompact_Icc
    exact h2.ofReal

/-- **Entirety of the Mellin continuation**: the function
`s ↦ Γ(s)⁻¹·∫₀^∞ t^(s-1)·e^(-at)·E(t) dt` is differentiable on all
of `ℂ`. -/
theorem dirichletMellinContinuation_differentiable (a : ℝ) (ha : 0 < a) :
    Differentiable ℂ (fun s : ℂ =>
      (Complex.Gamma s)⁻¹ * mellin (mellinKernel a) s) := by
  intro s
  refine DifferentiableAt.mul ?_ ?_
  · exact Complex.differentiable_one_div_Gamma s
  · exact mellin_differentiableAt_of_isBigO_rpow_exp ha
      (mellinKernel_locallyIntegrable a) (mellinKernel_isBigO_exp a)
      (mellinKernel_isBigO_rpow a (s.re - 1) ha)
      (by linarith [sub_lt_self s.re one_pos] : s.re - 1 < s.re)

/-- **Agreement on the real ray**: for `σ > 1` and `a > 0` the entire
continuation equals `D(σ,a)`. -/
theorem dirichletMellinContinuation_eq (σ a : ℝ) (hσ : 1 < σ)
    (ha : 0 < a) :
    (Complex.Gamma (σ : ℂ))⁻¹ * mellin (mellinKernel a) (σ : ℂ) =
      ((thueMorseDirichlet σ a : ℝ) : ℂ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hmell : mellin (mellinKernel a) (σ : ℂ) =
      (((∫ t in Ioi (0 : ℝ),
        t ^ (σ - 1) * (Real.exp (-(a * t)) * lacunaryExpProduct t) : ℝ)) : ℂ) := by
    rw [mellin]
    have hcongr : ∀ t ∈ Ioi (0 : ℝ),
        ((t : ℂ)) ^ ((σ : ℂ) - 1) • mellinKernel a t =
        (((t ^ (σ - 1) *
          (Real.exp (-(a * t)) * lacunaryExpProduct t) : ℝ)) : ℂ) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [mellinKernel, smul_eq_mul, Complex.ofReal_mul,
        show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht0.le]
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    exact integral_ofReal
  rw [hmell]
  have hint : (∫ t in Ioi (0 : ℝ),
      t ^ (σ - 1) * (Real.exp (-(a * t)) * lacunaryExpProduct t)) =
      Real.Gamma σ * thueMorseDirichlet σ a := by
    calc (∫ t in Ioi (0 : ℝ),
        t ^ (σ - 1) * (Real.exp (-(a * t)) * lacunaryExpProduct t))
        = ∫ t in Ioi (0 : ℝ),
            t ^ (σ - 1) * Real.exp (-(a * t)) * lacunaryExpProduct t :=
          setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
      _ = Real.Gamma σ * thueMorseDirichlet σ a :=
          (thueMorseDirichlet_mellin σ a hσ ha).symm
  rw [hint, Complex.Gamma_ofReal]
  have hne : Real.Gamma σ ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m hcon
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hcon] at hσ
    linarith
  have hneC : ((Real.Gamma σ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hne
  push_cast
  field_simp

end Fabius
