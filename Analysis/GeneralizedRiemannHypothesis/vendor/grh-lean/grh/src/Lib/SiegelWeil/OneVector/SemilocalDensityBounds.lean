import Lib.SiegelWeil.OneVector.ClassGaussSums

/-!
# Bounds for local densities at finitely many finite places

Let `A` be a finite place in the sense of `New.Floors.IntegralPlace`, which may be a product of
several completions, with ring of integers `R` and modulus `modulus`. Let `L` be the lattice of
integral vectors, let the character `ψ` be trivial on traces, and let `ζ_R(μ) = New.idealZeta R μ`
be at most `2`. No uniformizer is assumed: the Gauss sums are summed over the ideals of `R`.

* `New.Floors.IntegralPlace.measure_residueClass_le_idealZeta`: for a unimodular hermitian form of
  rank at least `2 μ + 1`, a class modulo `g L` has mass at most `ζ_R(μ) (modulus g)⁻¹` times its
  volume on each quadric.
* `New.Floors.IntegralPlace.one_add_enorm_measure_intVectors_sub_one_le`: on an integral quadric the
  mass of `L` differs from `1` by at most `ζ_R(μ) - 1`.

Notions from other files:
* `IntegralPlace A`: the data `integers`, `ψ`, `element`, `skewUnit`, `skewMeasure` and `modulus` of
  the place; `element` has trace `1`, and `skewMeasure` is a measure on the skew elements `b`, those
  with `b̄ = -b`. `skewUnit` is a unit of `A` with integral inverse, and
  `(a, b) ↦ element skewUnit⁻¹ a + b` carries `skewMeasure ⊗ skewMeasure` to Haar measure.
* `IsUnimodular R J`: the matrix `J` is hermitian and lies in `GL_n(R)`.
* `IsDisintegration volume J l`: the measures `l t`, on the quadrics `x* J x = skewUnit⁻¹ t`,
  disintegrate the Haar measure.
* `classGaussSum J g x₀ α b`: the integral of `ψ (element b (x* J x - α))` over the class
  `x₀ + g L`.

## Relation to the literature

Known result: bounds for local densities of hermitian forms by Gauss sums, part of Siegel's formula
for representing a number by a hermitian form. See `Lib.SiegelWeil.OneVector.SiegelClassSum`.
-/

namespace New.Floors.IntegralPlace

open Matrix MeasureTheory ENNReal Fintype FloorGroups Place Set Function SemilocalField

variable {A κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] {μ : ℕ}

/-- At a finite place `A` with ring of integers `R`, let `u` be a unit of `A`, and let `skewMeasure`
be the measure of the place on the skew `b` (those with `b̄ = -b`). Then the square of the measure
of the set of the skew `b` with `u b ∈ R` is at most `(modulus u)⁻¹`, where `modulus x` is the
factor by which multiplication by `x` scales Haar measure. -/
lemma skewMeasure_setOf_mul_mem_sq_le (u : Aˣ) :
    P.skewMeasure {b : skewAdjoint A | u.val * b.val ∈ P.integers} ^ 2 ≤ (P.modulus u)⁻¹ := by
  -- With `τ = element` and `δ = skewUnit`, the map `(a, b) ↦ τ δ⁻¹ a + b` preserves measure and
  -- sends `S × S` into `u⁻¹ R`.
  let S : Set (skewAdjoint A) := {b : skewAdjoint A | u.val * b.val ∈ P.integers}
  have h_sub : S ×ˢ S ⊆ (fun p : skewAdjoint A × skewAdjoint A ↦
      P.element * P.skewUnit⁻¹ * p.1.val + p.2.val) ⁻¹' {x : A | u.val * x ∈ P.integers} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    -- the goal is membership in the preimage
    change u.val * (P.element * P.skewUnit⁻¹ * a.val + b.val) ∈ P.integers
    rw [mul_add, mul_left_comm]
    exact add_mem (mul_mem (mul_mem P.element_mem P.skewUnit_inv_mem) ha) hb
  calc P.skewMeasure S ^ 2
    _ = (P.skewMeasure.prod P.skewMeasure) (S ×ˢ S) := by rw [Measure.prod_prod, sq]
    _ ≤ volume {x : A | u.val * x ∈ P.integers} :=
      (measure_mono h_sub).trans (P.measurePreserving_split.measure_preimage_le _)
    _ = (P.modulus u)⁻¹ := volume_setOf_mul_mem u

/-- A generator of `R + ν R`. For every `ν` there is a unit `η` of `A` that is congruent to `ν`
modulo the ring of integers `R` and such that `η c` is integral exactly when `c` and `ν c` are. So
`η⁻¹` generates the ideal of the `c ∈ R` with `ν c ∈ R`. -/
lemma exists_unit_sub_mem (ν : A) :
    ∃ η : Aˣ, η.val - ν ∈ P.integers ∧ ∀ c : A,
      η.val * c ∈ P.integers ↔ c ∈ P.integers ∧ ν * c ∈ P.integers := by
  -- Cut `A` by an idempotent `e`. Take `η = ν` on the part of `e`, where `ν⁻¹` is integral, and
  -- `η = 1` on the part of `1 - e`, where `ν` is integral.
  obtain ⟨e, he, h_le⟩ : ∃ e : P.integers, e.val * e = e ∧
      P.integers ∙ (1 : A) ⊔ P.integers ∙ ν ≤ P.integers ∙ (1 - e * (1 - ν)) :=
        P.isAdelic.isValuationPair 1 ν
  have h_dvd : (∃ r : P.integers, r.val * (1 - e * (1 - ν)) = 1) ∧
      ∃ s : P.integers, s.val * (1 - e * (1 - ν)) = ν := by
    simpa [Submodule.mem_span_singleton, Subring.smul_def] using h_le
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := h_dvd
  obtain ⟨η, hη⟩ : IsUnit (1 - e.val * (1 - ν)) := .of_mul_eq_one_right _ hr
  rw [← hη] at hr hs
  have h_sub : η.val - ν ∈ P.integers := by
    have h_eq : η.val - ν = ((1 - e) * (1 - s) : P.integers) := by
      push_cast
      -- from `η = 1 - e (1 - ν)`, `s η = ν` and `e e = e`
      linear_combination (1 - s * (1 - e.val)) * hη + (1 - e.val) * hs - s * (1 - ν) * he
    rw [h_eq]
    exact SetLike.coe_mem _
  refine ⟨η, h_sub, fun c : A ↦ ⟨fun hc ↦ ?_, fun ⟨hc, hνc⟩ ↦ ?_⟩⟩
  · -- Multiply `η c ∈ R` by `r`, where `r η = 1`, and by `s`, where `s η = ν`.
    constructor
    · simpa [← mul_assoc, hr] using mul_mem r.property hc
    · simpa [← mul_assoc, hs] using mul_mem s.property hc
  · -- `η c = (η - ν) c + ν c`
    simpa [sub_mul] using add_mem (mul_mem h_sub hc) hνc

variable [Fintype κ] [DecidableEq κ] {J : Matrix κ κ A} {l : skewAdjoint A → Measure (κ → A)}

/-- Let `ζ_R(μ) ≤ 2`, where `ζ_R(μ) = idealZeta R μ` is the sum of `[R : I] ^ (-μ)` over the ideals
of finite index. Let `J` be unimodular of rank at least `2 μ + 1` and let `ψ` be trivial on traces.
The Gauss sum `classGaussSum J g x₀ α b` is the integral of `ψ (τ b (x* J x - α))` over the class
`x₀ + g L`, where `τ = element` is the place's fixed integral element with `τ + τ̄ = 1` (independent
of `b`) and `L` is the lattice of integral vectors. Over the skew frequencies `b`, its absolute
value has integral at most `ζ_R(μ) (modulus g)⁻¹` times the volume `modulus g ^ card κ` of the
class, where `modulus g` is the factor by which multiplication by `g` scales Haar measure. -/
lemma lintegral_enorm_classGaussSum_le_idealZeta (hJ : IsUnimodular P.integers J)
    (hψ : ∀ x : A, P.ψ (x + star x) = 1) (hμ : idealZeta P.integers μ ≤ 2)
    (h_rank : 2 * μ + 1 ≤ card κ) (g : Aˣ) (x₀ : κ → A) (α : A) :
    ∫⁻ b : skewAdjoint A, ‖classGaussSum J g x₀ α b‖ₑ ∂P.skewMeasure ≤
      idealZeta P.integers μ * ((P.modulus g)⁻¹ * P.modulus g ^ card κ) := by
  -- Sort the `b` by the ideal `I = w R` of the `c ∈ R` with `g ḡ b c ∈ R`. In squares, the Gauss
  -- sum saves `[R : I] ^ card κ`, and the set `S I` of the `b` costs `[R : I] (modulus g)⁻¹ ^ 2`.
  let S (I : Ideal P.integers) : Set (skewAdjoint A) :=
    {b : skewAdjoint A | ∀ c ∈ P.integers.subtype '' I, (g * star g).val * b.val * c ∈ P.integers}
  rw [← setLIntegral_univ]
  refine lintegral_le_idealZeta_mul hμ S (.of_forall fun b _ ↦ ?_)
  show ∃ I : Ideal P.integers, I.cardQuot ≠ 0 ∧ b ∈ S I ∧
    (I.cardQuot : ℝ≥0∞) ^ μ * (‖classGaussSum J g x₀ α b‖ₑ * P.skewMeasure (S I)) ≤
      (P.modulus g)⁻¹ * P.modulus g ^ card κ
  obtain ⟨w, hw⟩ : ∃ w : Aˣ, ∀ c : A,
      w⁻¹.val * c ∈ P.integers ↔ c ∈ P.integers ∧ (g * star g).val * b.val * c ∈ P.integers := by
    obtain ⟨η, -, hη⟩ : ∃ η : Aˣ, η.val - (g * star g).val * b.val ∈ P.integers ∧
        ∀ c : A, η.val * c ∈ P.integers ↔ c ∈ P.integers ∧ (g * star g).val * b.val * c ∈
          P.integers :=
      exists_unit_sub_mem ((g * star g).val * b.val)
    exact ⟨η⁻¹, by simpa only [inv_inv] using hη⟩
  have h_one_mem : w⁻¹.val * w.val ∈ P.integers := by simp
  have hw_int : w.val ∈ P.integers := ((hw w).1 h_one_mem).left
  obtain ⟨I, hI_ne, hI_eq, hI_card⟩ : ∃ I : Ideal P.integers, I.cardQuot ≠ 0 ∧
      P.integers.subtype '' I = {x : A | w⁻¹.val * x ∈ P.integers} ∧ I.cardQuot = (P.modulus w)⁻¹ :=
    exists_ideal_cardQuot_eq w hw_int
  have hb_mem : b ∈ S I := fun c hc ↦ ((hw c).1 (hI_eq.subset hc)).right
  have h_gauss : ‖classGaussSum J g x₀ α b‖ₑ ^ 2 ≤
      P.modulus g ^ card κ * (P.modulus g * P.modulus w) ^ card κ :=
    enorm_classGaussSum_sq_le hJ hψ g x₀ α skewAdjoint.star_val_eq fun c hc hc' ↦
      (hw c).2 ⟨hc, hc'⟩
  have h_set : P.skewMeasure (S I) ^ 2 ≤ (P.modulus g)⁻¹ ^ 2 * (P.modulus w)⁻¹ := by
    have h_sub : S I ⊆ {b' : skewAdjoint A | (g * star g * w).val * b'.val ∈ P.integers} := by
      intro b' hb'
      have hw_mem : w.val ∈ P.integers.subtype '' I := hI_eq.superset (by simp)
      simpa [mul_right_comm] using hb' w hw_mem
    calc P.skewMeasure (S I) ^ 2
      _ ≤ (P.modulus (g * star g * w).val)⁻¹ := by
        grw [measure_mono h_sub, skewMeasure_setOf_mul_mem_sq_le]
      _ = (P.modulus g)⁻¹ ^ 2 * (P.modulus w)⁻¹ := by simp [ENNReal.mul_inv, sq]
  refine ⟨I, hI_ne, hb_mem, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, card κ = 2 * μ + 1 + k := Nat.exists_eq_add_of_le h_rank
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, hI_card]
  calc ((P.modulus w)⁻¹ ^ μ * (‖classGaussSum J g x₀ α b‖ₑ * P.skewMeasure (S I))) ^ 2
    _ ≤ ((P.modulus w)⁻¹ ^ μ) ^ 2 * (P.modulus g ^ card κ * (P.modulus g * P.modulus w) ^ card κ *
        ((P.modulus g)⁻¹ ^ 2 * (P.modulus w)⁻¹)) := by
      grw [mul_pow, mul_pow, h_gauss, h_set]
    _ = ((P.modulus g)⁻¹ * P.modulus g ^ card κ) ^ 2 *
        (P.modulus w * (P.modulus w)⁻¹) ^ (2 * μ + 1) * P.modulus w ^ k := by
      rw [hk]
      ring
    _ ≤ ((P.modulus g)⁻¹ * P.modulus g ^ card κ) ^ 2 := by
      have hw_mul : P.modulus w * (P.modulus w)⁻¹ ≤ 1 := (P.modulus w).mul_inv_le_one
      have hw_le : P.modulus w ≤ 1 := modulus_le_one w hw_int
      grw [hw_mul, hw_le, one_pow, one_pow, mul_one, mul_one]

/-- The mass of a class `x₀ + g L` on a quadric, for any unit `g`, where `L` is the lattice of
integral vectors and `modulus g` is the factor by which multiplication by `g` scales Haar measure.
Let `ζ_R(μ) ≤ 2`, where `ζ_R(μ) = idealZeta R μ` is the sum of `[R : I] ^ (-μ)` over the ideals of
finite index. Let `J` be unimodular of rank at least `2 μ + 1`, let the measures `l t`, on the
quadrics `x* J x = skewUnit⁻¹ t` for skew `t`, disintegrate Haar measure, and let `ψ` be trivial on
traces. Then the class has mass at most `ζ_R(μ) (modulus g)⁻¹` times its volume for every `l t`. -/
theorem measure_residueClass_le_idealZeta (h : P.IsDisintegration volume J l)
    (hJ : IsUnimodular P.integers J) (hψ : ∀ x : A, P.ψ (x + star x) = 1)
      (hμ : idealZeta P.integers μ ≤ 2)
    (h_rank : 2 * μ + 1 ≤ card κ) (g : Aˣ) (x₀ : κ → A) (t : skewAdjoint A) :
    l t (residueClass g x₀) ≤ idealZeta P.integers μ * (P.modulus g)⁻¹ * volume
      (residueClass g x₀) := by
  have hJ_herm : Jᴴ = J := hJ.left
  grw [measure_residueClass_le_lintegral h hJ_herm hψ,
    lintegral_enorm_classGaussSum_le_idealZeta hJ hψ hμ h_rank, volume_residueClass, mul_assoc]

/-- At the unit class, the Gauss sum at an integral frequency is `1`: let `J` be unimodular, let `α`
and `b` be integral, and recall that `classGaussSum J 1 0 α b` is the integral of
`ψ (element b (x* J x - α))` over the integral vectors `x`. Then this integral is `1`. -/
lemma classGaussSum_one_zero_eq_one (hJ : IsUnimodular P.integers J) {α b : A} (hα : α ∈ P.integers)
    (hb : b ∈ P.integers) : classGaussSum J 1 0 α b = 1 := by
  obtain ⟨-, V, hV : V ∈ intGL κ P.integers, rfl⟩ := hJ
  have h_phase (y : κ → A) (hy : y ∈ latticeMultiple κ (1 : Aˣ)) :
      P.ψ (P.element * b * (star (0 + y) ⬝ᵥ V.val *ᵥ (0 + y) - α)) = 1 := by
    have hy_int : y ∈ intVectors P.integers κ := fun i ↦ by simpa using mem_latticeMultiple.1 hy i
    have h_norm : star y ⬝ᵥ V.val *ᵥ y ∈ P.integers :=
      sum_mem fun i _ ↦ mul_mem (P.isAdelic.star_mem (hy_int i)) (hV.isIntMatrix.mulVec hy_int i)
    rw [zero_add]
    exact (P.self_dual _).2 (sub_mem h_norm hα) (P.element * b) (mul_mem P.element_mem hb)
  rw [classGaussSum, setIntegral_congr_fun (isOpen_latticeMultiple 1).measurableSet h_phase]
  simp [Measure.real, volume_latticeMultiple]

/-- The mass of the lattice on an integral quadric. Let `ζ_R(μ) ≤ 2`, where
`ζ_R(μ) = idealZeta R μ` is the sum of `[R : I] ^ (-μ)` over the ideals of finite index. Let `J` be
unimodular of rank at least `2 μ + 1`, let the measures `l t`, on the quadrics
`x* J x = skewUnit⁻¹ t` for skew `t`, disintegrate Haar measure, and let `ψ` be trivial on traces.
For integral `t`, the mass of the lattice `intVectors R κ` of integral vectors for `l t` differs
from `1` by at most `ζ_R(μ) - 1`. -/
theorem one_add_enorm_measure_intVectors_sub_one_le (h : P.IsDisintegration volume J l)
    (hJ : IsUnimodular P.integers J) (hψ : ∀ x : A, P.ψ (x + star x) = 1)
      (hμ : idealZeta P.integers μ ≤ 2)
    (h_rank : 2 * μ + 1 ≤ card κ) {t : skewAdjoint A} (ht : t.val ∈ P.integers) :
    1 + ‖(l t (intVectors P.integers κ : Set (κ → A))).toReal - 1‖ₑ ≤ idealZeta P.integers μ := by
  -- The mass of the lattice is the integral of its Gauss sums `G b` over all skew `b`. The integral
  -- `b` contribute exactly `1`, both to the mass and to the bound.
  have hJ_herm : Jᴴ = J := hJ.left
  let α : A := P.skewUnit⁻¹.val * t
  let G (b : skewAdjoint A) : ℂ := classGaussSum J 1 0 α b
  let S : Set (skewAdjoint A) := {b : skewAdjoint A | b.val ∈ P.integers}
  have hS : MeasurableSet S := isOpen_O.measurableSet.preimage (by fun_prop)
  have h_total : ∫⁻ b : skewAdjoint A, ‖G b‖ₑ ∂P.skewMeasure ≤ idealZeta P.integers μ := by
    simpa using lintegral_enorm_classGaussSum_le_idealZeta hJ hψ hμ h_rank 1 0 α
  have hG_int : Integrable G P.skewMeasure :=
    integrable_classGaussSum (h_total.trans_lt (hμ.trans_lt ofNat_lt_top))
  have hG_one (b : skewAdjoint A) (hb : b ∈ S) : G b = 1 :=
    classGaussSum_one_zero_eq_one hJ (mul_mem P.skewUnit_inv_mem ht) hb
  have h_head : ∫ b : skewAdjoint A in S, G b ∂P.skewMeasure = 1 := by
    rw [setIntegral_congr_fun hS hG_one]
    simp [Measure.real, S, P.skewMeasure_setOf_mem]
  have h_class : (intVectors P.integers κ : Set (κ → A)) = residueClass 1 0 := by
    simp [residueClass, mem_latticeMultiple, intVectors]
  have h_tail : (((l t (intVectors P.integers κ : Set (κ → A))).toReal - 1 : ℝ) : ℂ) =
      ∫ b : skewAdjoint A in Sᶜ, G b ∂P.skewMeasure := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, h_class,
      ← integral_classGaussSum h hJ_herm hψ 1 0 t hG_int, ← integral_add_compl hS hG_int, h_head,
      add_sub_cancel_left]
  have h_norm_tail : ‖(l t (intVectors P.integers κ : Set (κ → A))).toReal - 1‖ₑ =
      ‖∫ b : skewAdjoint A in Sᶜ, G b ∂P.skewMeasure‖ₑ := by
    rw [← h_tail, ← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  calc 1 + ‖(l t (intVectors P.integers κ : Set (κ → A))).toReal - 1‖ₑ
    _ = ‖∫ b : skewAdjoint A in S, G b ∂P.skewMeasure‖ₑ +
        ‖∫ b : skewAdjoint A in Sᶜ, G b ∂P.skewMeasure‖ₑ := by
      rw [h_head, enorm_one, h_norm_tail]
    _ ≤ ∫⁻ b : skewAdjoint A, ‖G b‖ₑ ∂P.skewMeasure := by
      grw [enorm_integral_le_lintegral_enorm, enorm_integral_le_lintegral_enorm,
        lintegral_add_compl _ hS]
    _ ≤ idealZeta P.integers μ := h_total

end New.Floors.IntegralPlace
