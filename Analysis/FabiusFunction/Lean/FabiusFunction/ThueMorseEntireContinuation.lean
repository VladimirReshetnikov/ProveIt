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

Once entirety is available the **dyadic parameter equation** propagates
off the real ray by the identity theorem: both sides of

`D(s,a) = 2^(-s)·(D(s,a/2) - D(s,(a+1)/2))`

are entire in `s`, and they agree on the ray `(1,∞) ⊆ ℝ ⊆ ℂ`, which
accumulates at every one of its points.

* `mellinKernel` — the kernel `e^(-at)·E(t)` as a complex-valued map.
* `mellinKernel_isBigO_exp` / `mellinKernel_isBigO_rpow` — decay at
  infinity and flatness of every order at `0` (from the effective
  bound `E(t) ≤ 2^(m(m-1)/2)·t^m`).
* `mellin_mellinKernel_differentiable` — the *undamped* Mellin
  transform is already entire; this is what flatness buys.
* `dirichletMellinContinuation` — the continuation itself, as a named
  function.
* `dirichletMellinContinuation_differentiable` — **entirety**.
* `dirichletMellinContinuation_neg_natCast` / `_zero` — **the trivial
  zeros** `D(-r,a) = 0` for every `r ≥ 0` (`cor:Dirichlet-trivial-zeros`).
* `mellin_mellinKernel_ofReal` — the Mellin value at a real exponent as
  a real integral.
* `dirichletMellinContinuation_eq` — agreement with `D(σ,a)` for
  `σ > 1`.
* `dirichletMellinContinuation_dyadic_ofReal` — the dyadic parameter
  equation on the real ray `σ > 1`, transported from
  `thueMorseDirichlet_dyadic`.
* `dirichletMellinContinuation_dyadic` — **the dyadic parameter
  equation at every `s ∈ ℂ`** (`thm:Dirichlet-dyadic`, complex form),
  by the identity theorem for entire functions.
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

/-- **The Mellin transform of the kernel is itself entire.**  This is the real
content of the boundary-flatness estimate: `E` vanishes at `0` faster than every
power, so the Mellin integral `M(s) = ∫₀^∞ t^(s-1)e^(-at)E(t) dt` has no
singularity anywhere, undamped by any `Γ`-factor. -/
theorem mellin_mellinKernel_differentiable (a : ℝ) (ha : 0 < a) :
    Differentiable ℂ (mellin (mellinKernel a)) := fun s =>
  mellin_differentiableAt_of_isBigO_rpow_exp ha
    (mellinKernel_locallyIntegrable a) (mellinKernel_isBigO_exp a)
    (mellinKernel_isBigO_rpow a (s.re - 1) ha)
    (by linarith [sub_lt_self s.re one_pos] : s.re - 1 < s.re)

/-- The entire continuation of the shifted Dirichlet series,
`D(s,a) = Γ(s)⁻¹·∫₀^∞ t^(s-1)·e^(-at)·E(t) dt`. -/
noncomputable def dirichletMellinContinuation (a : ℝ) : ℂ → ℂ :=
  fun s => (Complex.Gamma s)⁻¹ * mellin (mellinKernel a) s

theorem dirichletMellinContinuation_apply (a : ℝ) (s : ℂ) :
    dirichletMellinContinuation a s =
      (Complex.Gamma s)⁻¹ * mellin (mellinKernel a) s :=
  rfl

/-- **Entirety of the Mellin continuation**: the function
`s ↦ Γ(s)⁻¹·∫₀^∞ t^(s-1)·e^(-at)·E(t) dt` is differentiable on all
of `ℂ`. -/
theorem dirichletMellinContinuation_differentiable (a : ℝ) (ha : 0 < a) :
    Differentiable ℂ (dirichletMellinContinuation a) := fun s =>
  (Complex.differentiable_one_div_Gamma s).mul
    (mellin_mellinKernel_differentiable a ha s)

/-- **Zeros at the nonpositive integers** (`cor:Dirichlet-trivial-zeros`):
the entire continuation vanishes at `s = 0, -1, -2, …`.

The mathematical content is that the Mellin factor has *no pole* at `-r`, so
nothing cancels the zero of `1/Γ` there; that is
`mellin_mellinKernel_differentiable`, i.e. the super-polynomial boundary
flatness of `E`.  No positivity of `a` is needed for the identity itself. -/
@[simp] theorem dirichletMellinContinuation_neg_natCast (a : ℝ) (r : ℕ) :
    dirichletMellinContinuation a (-(r : ℂ)) = 0 := by
  rw [dirichletMellinContinuation, Complex.Gamma_neg_nat_eq_zero, inv_zero,
    zero_mul]

/-- The value at the origin: `D(0,a) = 0`, the `r = 0` case of
`dirichletMellinContinuation_neg_natCast`.  (Its *derivative* at `0` is the
Mellin value `M(0)`; see `ThueMorseGDirichlet`.) -/
@[simp] theorem dirichletMellinContinuation_zero (a : ℝ) :
    dirichletMellinContinuation a 0 = 0 := by
  simpa using dirichletMellinContinuation_neg_natCast a 0

/-- The Mellin transform of the kernel at a **real** exponent is the
corresponding real integral.  Stated for every real `σ`, not just the range of
absolute convergence: flatness makes the integrand real-integrable throughout,
and the two callers use `σ > 1` and `σ = 0` respectively. -/
theorem mellin_mellinKernel_ofReal (a σ : ℝ) :
    mellin (mellinKernel a) (σ : ℂ) =
      (((∫ t in Ioi (0 : ℝ),
        t ^ (σ - 1) *
          (Real.exp (-(a * t)) * lacunaryExpProduct t) : ℝ)) : ℂ) := by
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

/-- **Agreement on the real ray**: for `σ > 1` and `a > 0` the entire
continuation equals `D(σ,a)`. -/
theorem dirichletMellinContinuation_eq (σ a : ℝ) (hσ : 1 < σ)
    (ha : 0 < a) :
    dirichletMellinContinuation a (σ : ℂ) =
      ((thueMorseDirichlet σ a : ℝ) : ℂ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  rw [dirichletMellinContinuation, mellin_mellinKernel_ofReal]
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

/-- The cast bridge for the dyadic factor: for real `σ` the complex power
`2^(-s)` evaluated at `s = σ` is the real power `2^(-σ)`. -/
theorem two_cpow_neg_ofReal (σ : ℝ) :
    (2 : ℂ) ^ (-(σ : ℂ)) = (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_neg,
    Complex.ofReal_ofNat]

/-- **The dyadic parameter equation on the real ray**
(`thm:Dirichlet-dyadic`, Mellin form).  For `σ > 1` and `a > 0`,

`D(σ,a) = 2^(-σ)·(D(σ,a/2) - D(σ,(a+1)/2))`

for the *entire continuation*; this is the real dyadic equation
`thueMorseDirichlet_dyadic` transported through
`dirichletMellinContinuation_eq`.  The upgrade to all of `ℂ` is
`dirichletMellinContinuation_dyadic`. -/
theorem dirichletMellinContinuation_dyadic_ofReal (σ a : ℝ) (hσ : 1 < σ)
    (ha : 0 < a) :
    dirichletMellinContinuation a (σ : ℂ) =
      (2 : ℂ) ^ (-(σ : ℂ)) *
        (dirichletMellinContinuation (a / 2) (σ : ℂ) -
          dirichletMellinContinuation ((a + 1) / 2) (σ : ℂ)) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  have ha3 : (0 : ℝ) < (a + 1) / 2 := by linarith
  rw [dirichletMellinContinuation_eq σ a hσ ha,
    dirichletMellinContinuation_eq σ (a / 2) hσ ha2,
    dirichletMellinContinuation_eq σ ((a + 1) / 2) hσ ha3,
    thueMorseDirichlet_dyadic σ a hσ0 ha, two_cpow_neg_ofReal σ]
  push_cast
  ring

/-- **The dyadic parameter equation for the entire continuation**
(`thm:Dirichlet-dyadic`, complex form): for every `a > 0` and **every**
`s ∈ ℂ`,

`D(s,a) = 2^(-s)·(D(s,a/2) - D(s,(a+1)/2))`.

Proof by the identity theorem.  Both sides are entire — the left by
`dirichletMellinContinuation_differentiable` at `a`, the right by the
same at `a/2` and `(a+1)/2` multiplied by the entire `s ↦ 2^(-s)` — and
by `dirichletMellinContinuation_dyadic_ofReal` they agree on the real
ray `(1,∞) ⊆ ℝ ⊆ ℂ`, whose image accumulates at `s = 2`.  Hence they
agree on the connected space `ℂ`. -/
theorem dirichletMellinContinuation_dyadic (a : ℝ) (ha : 0 < a) (s : ℂ) :
    dirichletMellinContinuation a s =
      (2 : ℂ) ^ (-s) * (dirichletMellinContinuation (a / 2) s -
        dirichletMellinContinuation ((a + 1) / 2) s) := by
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  have ha3 : (0 : ℝ) < (a + 1) / 2 := by linarith
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : Differentiable ℂ (fun z : ℂ => (2 : ℂ) ^ (-z)) :=
    differentiable_neg.const_cpow (Or.inl h2ne)
  have hL : Differentiable ℂ (dirichletMellinContinuation a) :=
    dirichletMellinContinuation_differentiable a ha
  have hR : Differentiable ℂ (fun z : ℂ => (2 : ℂ) ^ (-z) *
      (dirichletMellinContinuation (a / 2) z -
        dirichletMellinContinuation ((a + 1) / 2) z)) :=
    hpow.fun_mul
      ((dirichletMellinContinuation_differentiable (a / 2) ha2).fun_sub
        (dirichletMellinContinuation_differentiable ((a + 1) / 2) ha3))
  have hLan : AnalyticOnNhd ℂ (dirichletMellinContinuation a) Set.univ :=
    fun z _ => hL.analyticAt z
  have hRan : AnalyticOnNhd ℂ (fun z : ℂ => (2 : ℂ) ^ (-z) *
      (dirichletMellinContinuation (a / 2) z -
        dirichletMellinContinuation ((a + 1) / 2) z)) Set.univ :=
    fun z _ => hR.analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      dirichletMellinContinuation a z =
        (2 : ℂ) ^ (-z) * (dirichletMellinContinuation (a / 2) z -
          dirichletMellinContinuation ((a + 1) / 2) z) := by
    have htend : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (2 : ℝ))
        (𝓝[≠] (2 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (2 : ℝ))
            (𝓝 (2 : ℂ)) :=
          Complex.continuous_ofReal.tendsto' 2 2 (by norm_num)
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        have hσ' : (2 : ℝ) < σ := hσ
        have hne : (σ : ℂ) ≠ (2 : ℂ) := by
          intro hcon
          exact hσ'.ne' (by exact_mod_cast hcon)
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact hne
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (2 : ℝ) < σ := hσ
    exact dirichletMellinContinuation_dyadic_ofReal σ a (by linarith) ha
  exact congrFun (hLan.eq_of_frequently_eq hRan hfreq) s

end Fabius
