import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The transfer identity of the doubling map

The analytic seed of the transfer-operator layer of the Fourier-decay
audit: integrating an observable against a function of the doubled
angle is the same as integrating the observable's Perron average
against the function itself,

`∫₀^½ f·(g∘2t) + ∫_½^1 f·(g∘(2t-1)) = ∫₀¹ ½(f(t/2) + f((t+1)/2))·g(t)`.

The left side is `∫₀¹ f·(g ∘ T)` for the doubling map `T t = 2t mod 1`
written without a fractional part; the right side is `∫₀¹ (𝒫f)·g` for
the unweighted Perron operator
`(𝒫f)(t) = ½(f(t/2) + f((t+1)/2))`.  Iterated, this identity is what
turns Birkhoff products over `T` into powers of transfer operators
(`∫ h·Pₙ = ∫ (𝓛ⁿh)` in the audit), and combined with the halving law
`𝒫ψ = ψ/2` of `DoublingCocycleIdentities` it forces the geometric
decay of the covariances of the doubling cocycle — the mechanism
behind the exact variance `π²/4`.

* `integral_mul_comp_doubling` — the adjoint identity, for continuous
  `f, g`.
* `integral_comp_doubling` — the case `f = 1`: the doubling map
  preserves Lebesgue measure on the circle.
-/

set_option autoImplicit false

open intervalIntegral

namespace Fabius

/-- **The transfer identity of the doubling map**: for continuous
`f, g`, `∫₀¹ f·(g∘T) = ∫₀¹ (𝒫f)·g` with `T` the doubling map (written
branchwise) and `𝒫` the unweighted Perron operator. -/
theorem integral_mul_comp_doubling (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) :
    ((∫ t in (0:ℝ)..(1/2:ℝ), f t * g (2 * t)) +
      ∫ t in (1/2:ℝ)..1, f t * g (2 * t - 1)) =
    ∫ t in (0:ℝ)..1, (f (t / 2) + f ((t + 1) / 2)) / 2 * g t := by
  have h1 : ∀ t : ℝ, f t * g (2 * t) =
      (fun u => f (u / 2) * g u) (2 * t) := by
    intro t
    simp only
    congr 2
    ring
  have e1 : (∫ t in (0:ℝ)..(1/2:ℝ), f t * g (2 * t)) =
      (2:ℝ)⁻¹ • ∫ u in (0:ℝ)..1, f (u / 2) * g u := by
    rw [intervalIntegral.integral_congr
      (g := fun t => (fun u => f (u / 2) * g u) (2 * t)) (fun t _ => h1 t)]
    have h := intervalIntegral.integral_comp_mul_left
      (a := (0:ℝ)) (b := (1/2:ℝ)) (f := fun u => f (u / 2) * g u)
      (c := (2:ℝ)) (by norm_num)
    simpa using h
  have h2 : ∀ t : ℝ, f t * g (2 * t - 1) =
      (fun u => f ((u + 1) / 2) * g u) (2 * t + (-1)) := by
    intro t
    simp only
    rw [show 2 * t + (-1) = 2 * t - 1 by ring]
    congr 2
    ring
  have e2 : (∫ t in (1/2:ℝ)..1, f t * g (2 * t - 1)) =
      (2:ℝ)⁻¹ • ∫ u in (0:ℝ)..1, f ((u + 1) / 2) * g u := by
    rw [intervalIntegral.integral_congr
      (g := fun t => (fun u => f ((u + 1) / 2) * g u) (2 * t + (-1)))
      (fun t _ => h2 t)]
    have h := intervalIntegral.integral_comp_mul_add
      (a := (1/2:ℝ)) (b := (1:ℝ)) (f := fun u => f ((u + 1) / 2) * g u)
      (c := (2:ℝ)) (by norm_num) (-1)
    norm_num at h
    simpa using h
  have hint1 : IntervalIntegrable (fun u => f (u / 2) * g u)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint2 : IntervalIntegrable (fun u => f ((u + 1) / 2) * g u)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [e1, e2, ← smul_add, ← intervalIntegral.integral_add hint1 hint2,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [smul_eq_mul]
  ring

/-- **The doubling map preserves Lebesgue measure**: the case `f = 1`
of the transfer identity. -/
theorem integral_comp_doubling (g : ℝ → ℝ) (hg : Continuous g) :
    ((∫ t in (0:ℝ)..(1/2:ℝ), g (2 * t)) +
      ∫ t in (1/2:ℝ)..1, g (2 * t - 1)) =
    ∫ t in (0:ℝ)..1, g t := by
  calc ((∫ t in (0:ℝ)..(1/2:ℝ), g (2 * t)) +
        ∫ t in (1/2:ℝ)..1, g (2 * t - 1))
      = ∫ t in (0:ℝ)..1, ((1:ℝ) + 1) / 2 * g t := by
        simpa only [one_mul] using
          integral_mul_comp_doubling (fun _ => 1) g continuous_const hg
    _ = ∫ t in (0:ℝ)..1, g t := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        norm_num

/-- **The covariance-halving mechanism**: if the observable satisfies
the Perron halving law `f(x/2) + f((x+1)/2) = f(x)` — as the doubling
cocycle `ψ = log (2 sin π·)` does, by
`DoublingCocycleIdentities.log_two_sin_half_add` — then pairing it with
any function of the doubled angle halves the pairing:
`∫₀¹ f·(g∘T) = ½ ∫₀¹ f·g`.  Iterating over `r` doubling steps, this is
the exact geometric decay `c_r = c_0/2^r` of the doubling covariances
behind the audit's variance `π²/4` (here in its continuous-observable
form; the cocycle itself requires the `L²` extension). -/
theorem integral_mul_comp_doubling_of_halving {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hhalf : ∀ x, f (x / 2) + f ((x + 1) / 2) = f x) :
    ((∫ t in (0:ℝ)..(1/2:ℝ), f t * g (2 * t)) +
      ∫ t in (1/2:ℝ)..1, f t * g (2 * t - 1)) =
    (1 / 2) * ∫ t in (0:ℝ)..1, f t * g t := by
  rw [integral_mul_comp_doubling f g hf hg,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [hhalf t]
  ring

end Fabius
