import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Geometrically self-similar convolution tails

The Thue–Morse volume's roadmap asks for a *reusable geometric-tail
API*: the identity "tail equals a scaled copy of the whole object"
occurs simultaneously for products, convolutions, random series, and
cumulant generating functions, and each face deserves an abstract
library with the dyadic case as a specialization.  The product face is
`GeometricScaleProducts.lean`; this module is the **convolution
face**.

The abstract data is a *digit measure* `ν` on an additive monoid and a
*scale endomorphism* `T` (an additive monoid homomorphism).  Out of
them we build the **prefix system**

`digitPrefix ν T 0 = δ_0`,   `digitPrefix ν T (m+1) = ν ∗ (T_* (digitPrefix ν T m))`

— the law of `D₁ + T D₂ + ⋯ + T^{m-1} Dₘ` for independent digits
`Dᵢ ∼ ν`.  The two structural theorems are purely convolution-algebraic
(no characteristic functions, no topology):

* `digitPrefix_add` — the **cocycle law**
  `P_{m+n} = P_m ∗ (T^m)_* P_n`: a long prefix splits into a short
  prefix convolved with a rescaled copy of the remaining prefix.
* `self_similar_conv_iterate` — the **tail law**: from the one-step
  refinement `μ = ν ∗ T_* μ` alone, `μ = P_m ∗ (T^m)_* μ` for every
  `m`.  A measure whose tail is a scaled copy of the whole splits off
  arbitrarily many digits.

Both proofs share one step, `conv_map_conv_map_pow`, which pushes the
scale through a convolution (`Measure.map_conv_addMonoidHom`) and
reassociates.  Scales enter as function iterates `(⇑T)^[m]` — the
correct generality, with no `AddMonoid.End` power plumbing.

On the real line with the scale `x ↦ c·x` the system specializes to
`mulPrefix ν c`, iterates become powers (`mul_left_iterate`), and the
characteristic function of the prefix is the finite product
`∏_{k<m} charFun ν (c^k t)` (`charFun_mulPrefix`) — the abstract form
of the finite sinc products of the dyadic theory.
`MeasureRefinement.lean` re-derives the up-measure's random-tail law
`μ_up = P_m ∗ (2^{-m})_* μ_up` from the refinement equation through
this API.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

section AddMonoid

variable {M : Type*} [AddMonoid M] {mM : MeasurableSpace M} [MeasurableAdd₂ M]

/-- The convolution prefix system of a digit measure `ν` under the
scale endomorphism `T`: the law of `D₁ + T D₂ + ⋯ + T^{m-1} Dₘ` for
independent digits `Dᵢ ∼ ν`, defined by the digit recursion
`P₀ = δ₀`, `P_{m+1} = ν ∗ T_* P_m`. -/
noncomputable def digitPrefix (ν : Measure M) (T : M →+ M) : ℕ → Measure M
  | 0 => Measure.dirac 0
  | m + 1 => ν ∗ (digitPrefix ν T m).map T

/-- Every prefix of a probability digit measure is a probability
measure (the scale must be measurable for the pushforward to keep
mass). -/
theorem isProbabilityMeasure_digitPrefix {ν : Measure M} {T : M →+ M}
    [IsProbabilityMeasure ν] (hT : Measurable T) (m : ℕ) :
    IsProbabilityMeasure (digitPrefix ν T m) := by
  induction m with
  | zero =>
      rw [digitPrefix]
      infer_instance
  | succ m ih =>
      rw [digitPrefix]
      haveI := ih
      haveI : IsProbabilityMeasure ((digitPrefix ν T m).map T) :=
        Measure.isProbabilityMeasure_map hT.aemeasurable
      infer_instance

/-- A single digit: `P₁ = ν`. -/
theorem digitPrefix_one (ν : Measure M) [SFinite ν] {T : M →+ M}
    (hT : Measurable T) : digitPrefix ν T 1 = ν := by
  rw [digitPrefix, digitPrefix, map_dirac' hT, map_zero,
    Measure.conv_dirac_zero]

/-- The shared inductive step of the cocycle and tail laws: push the
scale through a convolution whose right factor is already an iterated
rescaling, and reassociate.  -/
theorem conv_map_conv_map_pow (ν : Measure M) {ρ σ : Measure M}
    {T : M →+ M} (hT : Measurable T) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure σ] (m : ℕ) :
    ν ∗ ((ρ ∗ σ.map ((⇑T)^[m])).map T) =
      (ν ∗ ρ.map T) ∗ σ.map ((⇑T)^[m + 1]) := by
  haveI : IsProbabilityMeasure (σ.map ((⇑T)^[m])) :=
    Measure.isProbabilityMeasure_map (hT.iterate m).aemeasurable
  haveI : IsProbabilityMeasure (ρ.map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  haveI : IsProbabilityMeasure (σ.map ((⇑T)^[m + 1])) :=
    Measure.isProbabilityMeasure_map (hT.iterate (m + 1)).aemeasurable
  rw [Measure.map_conv_addMonoidHom T hT,
    Measure.map_map hT (hT.iterate m), ← Function.iterate_succ',
    ← Measure.conv_assoc]

/-- **The cocycle law of the prefix system**: a long prefix is a short
prefix convolved with a rescaled copy of the remaining prefix,
`P_{m+n} = P_m ∗ (T^m)_* P_n`. -/
theorem digitPrefix_add (ν : Measure M) {T : M →+ M}
    [IsProbabilityMeasure ν] (hT : Measurable T) (m n : ℕ) :
    digitPrefix ν T (m + n) =
      digitPrefix ν T m ∗ (digitPrefix ν T n).map ((⇑T)^[m]) := by
  haveI := isProbabilityMeasure_digitPrefix (ν := ν) hT
  induction m with
  | zero =>
      rw [Nat.zero_add, Function.iterate_zero, Measure.map_id, digitPrefix,
        Measure.dirac_zero_conv]
  | succ m ih =>
      rw [Nat.succ_add, digitPrefix, ih,
        conv_map_conv_map_pow ν hT m, ← digitPrefix]

/-- **The geometric tail law**: a measure satisfying the one-step
refinement `μ = ν ∗ T_* μ` — its tail beyond one digit is a scaled
copy of the whole — splits off arbitrarily many digits:
`μ = digitPrefix ν T m ∗ (T^m)_* μ` for every `m`. -/
theorem self_similar_conv_iterate {μ ν : Measure M} {T : M →+ M}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hT : Measurable T)
    (h : μ = ν ∗ μ.map T) (m : ℕ) :
    μ = digitPrefix ν T m ∗ μ.map ((⇑T)^[m]) := by
  haveI := isProbabilityMeasure_digitPrefix (ν := ν) hT
  induction m with
  | zero =>
      rw [Function.iterate_zero, Measure.map_id, digitPrefix,
        Measure.dirac_zero_conv]
  | succ m ih =>
      calc μ = ν ∗ μ.map T := h
        _ = ν ∗ ((digitPrefix ν T m ∗ μ.map ((⇑T)^[m])).map T) := by
            rw [← ih]
        _ = (ν ∗ (digitPrefix ν T m).map T) ∗ μ.map ((⇑T)^[m + 1]) :=
            conv_map_conv_map_pow ν hT m
        _ = digitPrefix ν T (m + 1) ∗ μ.map ((⇑T)^[m + 1]) := by
            rw [digitPrefix]

end AddMonoid

section Real

/-- The prefix system on the real line with the scale `x ↦ c·x`: the
law of `D₁ + c D₂ + ⋯ + c^{m-1} Dₘ` for independent digits `Dᵢ ∼ ν`.
The dyadic case `c = ½` with a uniform digit is the up-function's
digit system. -/
noncomputable def mulPrefix (ν : Measure ℝ) (c : ℝ) : ℕ → Measure ℝ :=
  digitPrefix ν (AddMonoidHom.mulLeft c)

@[simp] theorem mulPrefix_zero (ν : Measure ℝ) (c : ℝ) :
    mulPrefix ν c 0 = Measure.dirac 0 := rfl

theorem mulPrefix_succ (ν : Measure ℝ) (c : ℝ) (m : ℕ) :
    mulPrefix ν c (m + 1) = ν ∗ (mulPrefix ν c m).map (c * ·) := rfl

/-- Every real prefix of a probability digit measure is a probability
measure. -/
theorem isProbabilityMeasure_mulPrefix {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (c : ℝ) (m : ℕ) :
    IsProbabilityMeasure (mulPrefix ν c m) :=
  isProbabilityMeasure_digitPrefix (measurable_const_mul c) m

/-- **The real geometric tail law**: from the one-step refinement
`μ = ν ∗ (c·)_* μ`, the measure splits off `m` digits with the
geometric scales, `μ = mulPrefix ν c m ∗ (c^m·)_* μ`. -/
theorem self_similar_conv_iterate_mul {μ ν : Measure ℝ} {c : ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν ∗ μ.map (c * ·)) (m : ℕ) :
    μ = mulPrefix ν c m ∗ μ.map (c ^ m * ·) := by
  have h' := self_similar_conv_iterate (T := AddMonoidHom.mulLeft c)
    (measurable_const_mul c) h m
  rwa [AddMonoidHom.coe_mulLeft, mul_left_iterate] at h'

/-- **The real cocycle law**: `P_{m+n} = P_m ∗ (c^m·)_* P_n`. -/
theorem mulPrefix_add (ν : Measure ℝ) [IsProbabilityMeasure ν] (c : ℝ)
    (m n : ℕ) :
    mulPrefix ν c (m + n) =
      mulPrefix ν c m ∗ (mulPrefix ν c n).map (c ^ m * ·) := by
  have h' := digitPrefix_add ν (T := AddMonoidHom.mulLeft c)
    (measurable_const_mul c) m n
  rwa [AddMonoidHom.coe_mulLeft, mul_left_iterate] at h'

/-- **The characteristic function of the prefix** is the finite
product of rescaled digit characteristic functions,
`charFun (mulPrefix ν c m) t = ∏_{k<m} charFun ν (c^k t)` — the
abstract form of the dyadic theory's finite sinc products. -/
theorem charFun_mulPrefix (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (m : ℕ) (t : ℝ) :
    charFun (mulPrefix ν c m) t =
      ∏ k ∈ Finset.range m, charFun ν (c ^ k * t) := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
      haveI := isProbabilityMeasure_mulPrefix (ν := ν) c m
      haveI : IsProbabilityMeasure ((mulPrefix ν c m).map (c * ·)) :=
        Measure.isProbabilityMeasure_map
          (measurable_const_mul c).aemeasurable
      rw [mulPrefix_succ, charFun_conv, charFun_map_mul, ih,
        Finset.prod_range_succ', pow_zero, one_mul, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k _ => by
        rw [← mul_assoc, ← pow_succ]

end Real

end Fabius
