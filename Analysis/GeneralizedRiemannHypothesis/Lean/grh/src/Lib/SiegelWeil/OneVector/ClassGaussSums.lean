import Lib.SiegelWeil.OneVector.ResidueClasses

/-!
# Gauss sums of classes modulo a lattice at a finite place

Let `A` be a finite place (`New.Floors.IntegralPlace`) with ring of integers `R`, modulus `modulus`
and a character `ψ` that is trivial on traces. Let `L` be the lattice of integral vectors and `g` a
unit of `A`.

Notions from other files:

* `New.Floors.IntegralPlace`: a semilocal field with conjugation, a compact open subring `R` of
  volume `1` that is self-dual for `ψ`, an integral `τ` with `τ + τ̄ = 1`, a skew unit
  `δ = skewUnit`, a modulus and a measure `skewMeasure` on the skew elements, those with `b̄ = -b`.
* `New.Floors.IntegralPlace.latticeMultiple κ g`: the lattice `g L` in `κ → A`.
* `New.IsUnimodular R J`: the matrix `J` is hermitian and invertible over `R`.
* `New.Floors.Place.IsDisintegration`: the measures `l t`, indexed by skew `t`, disintegrate a
  measure along `x ↦ x* J x`, with `l t` living over the value `δ⁻¹ t`.

Main definition and results:

* `New.Floors.IntegralPlace.classGaussSum`: the Gauss sum of a hermitian form on a class modulo
  `g L`.
* `New.Floors.IntegralPlace.enorm_classGaussSum_sq_le`: Weyl differencing bounds it, for a
  unimodular form, in terms of the denominator of the frequency.
* `New.Floors.IntegralPlace.integral_classGaussSum`,
  `New.Floors.IntegralPlace.measure_residueClass_le_lintegral`: by Fourier inversion, the mass of a
  class on a quadric is the integral of its Gauss sums over the skew frequencies if they are
  integrable, and it is always at most the integral of their modulus.

## Relation to the literature

Known result: bounds for local densities of hermitian forms by Gauss sums, part of Siegel's formula
for representing a number by a hermitian form. See `Lib.SiegelWeil.OneVector.SiegelClassSum`.
-/

namespace New.Floors.IntegralPlace

open Matrix MeasureTheory ENNReal Fintype Place Set Function SemilocalField ComplexConjugate
open scoped NNReal

variable {A κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype κ]

/-- The Gauss sum of the class `x₀ + g L` at the frequency `b`: the integral over the class of
`ψ (τ b (x* J x - α))`, where `τ + τ̄ = 1`. -/
noncomputable def classGaussSum (J : Matrix κ κ A) (g : Aˣ) (x₀ : κ → A) (α b : A) : ℂ :=
  ∫ y : κ → A in latticeMultiple κ g, P.ψ (P.element * b * (star (x₀ + y) ⬝ᵥ J *ᵥ (x₀ + y) - α))

/-- If `ψ` is trivial on traces and `b` is skew, then `ψ (τ b (s + s̄)) = ψ (b s)`, where
`τ + τ̄ = 1`. -/
lemma psi_mul_trace (hψ : ∀ x : A, P.ψ (x + star x) = 1) {b : A} (hb : star b = -b) (s : A) :
    P.ψ (P.element * b * (s + star s)) = P.ψ (b * s) := by
  have h_split : P.element * b * (s + star s) =
      b * s + (-(star P.element * b * s) + star (-(star P.element * b * s))) := by
    rw [star_neg, star_mul', star_mul', star_star, hb]
    linear_combination (b * s) * P.element_add_star
  rw [h_split, P.ψ.map_add_eq_mul, hψ, mul_one]

/-- The phase of Weyl differencing. For hermitian `J`, skew `b` and `ψ` trivial on traces, the
quotient of the values of `x ↦ ψ (τ b (x* J x - α))` at `x + d` and `x` is
`ψ (τ b d* J d) ψ (b x* J d)`. -/
lemma conj_psi_mul_psi_add {J : Matrix κ κ A} (hJ : Jᴴ = J) (hψ : ∀ x : A, P.ψ (x + star x) = 1)
    {b : A} (hb : star b = -b) (α : A) (x d : κ → A) :
    conj (P.ψ (P.element * b * (star x ⬝ᵥ J *ᵥ x - α))) *
        P.ψ (P.element * b * (star (x + d) ⬝ᵥ J *ᵥ (x + d) - α)) =
      P.ψ (P.element * b * (star d ⬝ᵥ J *ᵥ d)) * P.ψ (b * (star x ⬝ᵥ J *ᵥ d)) := by
  classical
  have h_expand : P.element * b * (star (x + d) ⬝ᵥ J *ᵥ (x + d) - α) =
      P.element * b * (star x ⬝ᵥ J *ᵥ x - α) + (P.element * b * (star d ⬝ᵥ J *ᵥ d) +
        P.element * b * (star x ⬝ᵥ J *ᵥ d + star (star x ⬝ᵥ J *ᵥ d))) := by
    rw [star_dotProduct_mulVec_comm hJ, star_add, mulVec_add, add_dotProduct, dotProduct_add,
      dotProduct_add]
    ring
  have h_unit (a : A) : conj (P.ψ a) * P.ψ a = 1 := by simp [Complex.conj_mul', P.norm_psi]
  rw [h_expand, P.ψ.map_add_eq_mul, ← mul_assoc, h_unit, one_mul, P.ψ.map_add_eq_mul,
    psi_mul_trace hψ hb]

section Weyl

variable [DecidableEq κ] {J : Matrix κ κ A}

/-- Duality for a unimodular form `J`: if the character `y ↦ ψ (b y* J d)` is trivial on the lattice
`g L`, where `L` is the lattice of integral vectors, then `b ḡ d` is an integral vector. -/
lemma smul_mem_intVectors_of_psi_eq_one (hJ : IsUnimodular P.integers J) {g : Aˣ} {b : A}
    {d : κ → A} (h_triv : ∀ y ∈ latticeMultiple κ g, P.ψ (b * (star y ⬝ᵥ J *ᵥ d)) = 1) :
    (b * star g.val) • d ∈ intVectors P.integers κ := by
  -- As `J` is invertible over `R`, it suffices that `J (b ḡ d)` is integral. By self-duality of
  -- `R`, test this against `r ∈ R`, using the vector of `g L` with `i`-th entry `g r̄`.
  obtain ⟨-, V, hV, rfl⟩ := hJ
  refine (mulVec_mem_intVectors_iff hV).1 ?_
  intro i
  show (V.val *ᵥ ((b * star g.val) • d)) i ∈ P.integers
  refine (P.self_dual _).1 fun (r : A) (hr : r ∈ P.integers) ↦ ?_
  have h_mem : Pi.single i (g.val * star r) ∈ latticeMultiple κ g := by
    refine mem_latticeMultiple.2 fun j ↦ ?_
    simp [Pi.single_apply, apply_ite (· ∈ P.integers), P.isAdelic.star_mem hr]
  have h_eq : r * (V.val *ᵥ ((b * star g.val) • d)) i =
      b * (star (Pi.single i (g.val * star r) : κ → A) ⬝ᵥ V.val *ᵥ d) := by
    simp [mulVec_smul, mul_assoc, mul_left_comm]
  rw [h_eq]
  exact h_triv _ h_mem
/-- Let `J` be unimodular over the ring of integers `R` and let `w` be a unit such that `w R`
contains every integral `c` for which `g ḡ b c` is integral. If the character `y ↦ ψ (b y* J d)` is
trivial on `g L`, where `L` is the lattice of integral vectors and `d ∈ g L`, then `d ∈ g w L`. -/
lemma mem_latticeMultiple_mul_of_psi_eq_one (hJ : IsUnimodular P.integers J) {g w : Aˣ} {b : A}
    {d : κ → A} (hw : ∀ c ∈ P.integers, (g * star g).val * b * c ∈ P.integers → w⁻¹.val * c ∈
      P.integers)
    (hd : d ∈ latticeMultiple κ g)
    (h_triv : ∀ y ∈ latticeMultiple κ g, P.ψ (b * (star y ⬝ᵥ J *ᵥ d)) = 1) :
    d ∈ latticeMultiple κ (g * w) := by
  refine mem_latticeMultiple.2 fun i ↦ ?_
  have h_mem : (b * star g.val) • d ∈ intVectors P.integers κ :=
    smul_mem_intVectors_of_psi_eq_one hJ h_triv
  have h_eq : (g * star g).val * b * (g⁻¹.val * d i) = b * star g.val * d i := by
    rw [Units.val_mul, Units.coe_star]
    linear_combination (b * star g.val * d i) * g.mul_inv
  have h_int : (g * star g).val * b * (g⁻¹.val * d i) ∈ P.integers := by
    rw [h_eq]
    exact h_mem i
  have h_div : w⁻¹.val * (g⁻¹.val * d i) ∈ P.integers := hw _ (mem_latticeMultiple.1 hd i) h_int
  simpa [mul_assoc] using h_div
/-- Weyl differencing, with the volumes expressed by the modulus `P.modulus`: the lattice `g L` of
vectors has volume `P.modulus g ^ card κ`. Let `J` be unimodular over the ring of integers `R`, `b`
skew and `ψ` trivial on traces. Let `w` be a unit such that `w R` contains every integral `c` for
which `g ḡ b c` is integral. Then the squared modulus of `classGaussSum J g x₀ α b` is at most the
volume of `g L` times the volume of `g w L`, where `L` is the lattice of integral vectors.
`classGaussSum J g x₀ α b` is the integral over the class `x₀ + g L` of `ψ (τ b (x* J x - α))`, with
`τ` the fixed integral element satisfying `τ + τ̄ = 1`. -/
lemma enorm_classGaussSum_sq_le (hJ : IsUnimodular P.integers J)
    (hψ : ∀ x : A, P.ψ (x + star x) = 1)
    (g : Aˣ) (x₀ : κ → A) (α : A) {b : A} (hb : star b = -b) {w : Aˣ}
    (hw : ∀ c ∈ P.integers, (g * star g).val * b * c ∈ P.integers → w⁻¹.val * c ∈ P.integers) :
    ‖classGaussSum J g x₀ α b‖ₑ ^ 2 ≤
      P.modulus g ^ card κ * (P.modulus g * P.modulus w) ^ card κ := by
  -- The square is the integral over `d ∈ M = g L` of the autocorrelation `corr d`. Up to a phase
  -- this is the integral of a character of `M`, which is trivial only for `d ∈ N = g w L`.
  let M : AddSubgroup (κ → A) := latticeMultiple κ g
  let N : Set (κ → A) := latticeMultiple κ (g * w)
  have M_open : IsOpen (M : Set (κ → A)) := isOpen_latticeMultiple g
  have M_compact : IsCompact (M : Set (κ → A)) := isCompact_latticeMultiple g
  let F (y : κ → A) : ℂ := P.ψ (P.element * b * (star (x₀ + y) ⬝ᵥ J *ᵥ (x₀ + y) - α))
  have hψ_cont : Continuous P.ψ := P.continuous_psi
  have F_cont : Continuous F := by fun_prop
  let corr (d : κ → A) : ℂ := ∫ y in M, conj (F y) * F (y + d)
  have h_char (d y y' : κ → A) : P.ψ (b * (star (y + y') ⬝ᵥ J *ᵥ d)) =
      P.ψ (b * (star y ⬝ᵥ J *ᵥ d)) * P.ψ (b * (star y' ⬝ᵥ J *ᵥ d)) := by
    rw [star_add, add_dotProduct, mul_add, P.ψ.map_add_eq_mul]
  have h_phase (y d : κ → A) : conj (F y) * F (y + d) =
      P.ψ (P.element * b * (star d ⬝ᵥ J *ᵥ d)) *
        (P.ψ (b * (star x₀ ⬝ᵥ J *ᵥ d)) * P.ψ (b * (star y ⬝ᵥ J *ᵥ d))) := by
    simp only [F, ← add_assoc x₀]
    rw [conj_psi_mul_psi_add hJ.left hψ hb, h_char]
  have h_corr (d : κ → A) (hd : d ∈ M) :
      ‖corr d‖ₑ ≤ N.indicator (fun _ ↦ volume (M : Set (κ → A))) d := by
    simp only [corr, h_phase, integral_const_mul]
    rw [setIntegral_char M_open (χ := fun y : κ → A ↦ P.ψ (b * (star y ⬝ᵥ J *ᵥ d))) (h_char d)]
    split_ifs with h_triv
    · have h_mem : d ∈ N := mem_latticeMultiple_mul_of_psi_eq_one hJ hw hd h_triv
      have h_norm (a : A) : ‖P.ψ a‖ₑ = 1 := by simp [← ofReal_norm, P.norm_psi]
      rw [indicator_of_mem h_mem]
      simpa [h_norm, ← ofReal_norm, Measure.real] using ofReal_toReal_le
    · simp
  have h_sq : conj (∫ y in M, F y) * ∫ y in M, F y = ∫ d in M, corr d := by
    have h_integrable : Integrable (uncurry fun (y d : κ → A) ↦ conj (F y) * F (y + d))
        ((volume.restrict M).prod (volume.restrict M)) := by
      rw [Measure.prod_restrict]
      exact ContinuousOn.integrableOn_compact (M_compact.prod M_compact) (by fun_prop)
    rw [← integral_conj, ← integral_mul_const, ← integral_integral_swap h_integrable]
    refine setIntegral_congr_fun M_open.measurableSet fun y hy ↦ ?_
    rw [integral_const_mul, setIntegral_add_left_eq_self_of_mem F hy]
  calc ‖classGaussSum J g x₀ α b‖ₑ ^ 2
    _ = ‖∫ d in M, corr d‖ₑ := by rw [← h_sq, enorm_mul, RCLike.enorm_conj, sq, classGaussSum]
    _ ≤ ∫⁻ d in M, ‖corr d‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ d in M, N.indicator (fun _ ↦ volume (M : Set (κ → A))) d :=
      setLIntegral_mono' M_open.measurableSet h_corr
    _ ≤ ∫⁻ d, N.indicator (fun _ ↦ volume (M : Set (κ → A))) d := setLIntegral_le_lintegral _ _
    _ = P.modulus g ^ card κ * (P.modulus g * P.modulus w) ^ card κ := by
      rw [lintegral_indicator_const (isOpen_latticeMultiple _).measurableSet,
        volume_latticeMultiple, volume_latticeMultiple, Units.val_mul, map_mul]

end Weyl

variable {J : Matrix κ κ A} {l : skewAdjoint A → Measure (κ → A)}

/-- For a unit `g`, a vector `x₀` and `α : A`, the Gauss sums of the class `x₀ + g L` at level `α`
are integrable in the skew frequency `b` for the measure `P.skewMeasure` as soon as their modulus
has a finite integral. -/
lemma integrable_classGaussSum {g : Aˣ} {x₀ : κ → A} {α : A}
    (h_lt : ∫⁻ b : skewAdjoint A, ‖classGaussSum J g x₀ α b‖ₑ ∂P.skewMeasure < ∞) :
    Integrable (fun b : skewAdjoint A ↦ classGaussSum J g x₀ α b) P.skewMeasure := by
  have hψ_cont : Continuous P.ψ := P.continuous_psi
  have h_cont : Continuous (uncurry fun (b : skewAdjoint A) (y : κ → A) ↦
      P.ψ (P.element * b * (star (x₀ + y) ⬝ᵥ J *ᵥ (x₀ + y) - α))) := by
    fun_prop
  have h_meas : AEStronglyMeasurable (fun b : skewAdjoint A ↦ classGaussSum J g x₀ α b)
      P.skewMeasure := by
    simp only [classGaussSum]
    exact h_cont.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  exact ⟨h_meas, h_lt⟩

/-- Fourier inversion for a class. Let the measures `l t` disintegrate Haar measure along the
hermitian form of `J`, and let `ψ` be trivial on traces. If the Gauss sums of the class
`residueClass g x₀ = x₀ + g L` are integrable over the skew frequencies for the measure
`P.skewMeasure`, their integral is the mass of the class on the quadric `x* J x = δ⁻¹ t`, where
`δ = P.skewUnit`. -/
lemma integral_classGaussSum (h : P.IsDisintegration volume J l) (hJ : Jᴴ = J)
    (hψ : ∀ x : A, P.ψ (x + star x) = 1) (g : Aˣ) (x₀ : κ → A) (t : skewAdjoint A)
    (h_int : Integrable (fun b : skewAdjoint A ↦ classGaussSum J g x₀ (P.skewUnit⁻¹.val * t) b)
      P.skewMeasure) :
    ∫ b : skewAdjoint A, classGaussSum J g x₀ (P.skewUnit⁻¹.val * t) b ∂P.skewMeasure =
      (l t (residueClass g x₀)).toReal := by
  classical
  let f : (κ → A) → ℝ≥0 := (residueClass g x₀).indicator 1
  have h_clopen : IsClopen (residueClass g x₀) :=
    ⟨(isCompact_residueClass g x₀).isClosed, isOpen_residueClass g x₀⟩
  have hf : Continuous f := h_clopen.continuous_indicator continuous_one
  have h_supp : HasCompactSupport f :=
    .intro (isCompact_residueClass g x₀) fun x hx ↦ indicator_of_notMem hx 1
  have h_sum (b : skewAdjoint A) :
      ∫ x : κ → A, f x * P.ψ (P.element * b.val * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.val * t)) =
        classGaussSum J g x₀ (P.skewUnit⁻¹.val * t) b := by
    rw [classGaussSum, ← integral_indicator (isOpen_latticeMultiple g).measurableSet,
      ← integral_add_left_eq_self _ x₀]
    refine integral_congr_ae (.of_forall fun y : κ → A ↦ ?_)
    simp [f, residueClass, indicator_apply, apply_ite NNReal.toReal, apply_ite Complex.ofReal]
  have h_mass : ∫⁻ x, f x ∂l t = l t (residueClass g x₀) := by
    rw [← lintegral_indicator_one h_clopen.isOpen.measurableSet]
    simp [f, ENNReal.coe_indicator, Pi.one_def]
  rw [← h_mass]
  simp only [← h_sum] at h_int ⊢
  exact integral_skewMeasure_eq_toReal_lintegral h hJ hψ hf h_supp t h_int

/-- Let the measures `l t` disintegrate Haar measure along the hermitian form of `J`, and let `ψ` be
trivial on traces. The mass of the class `residueClass g x₀ = x₀ + g L` on the quadric
`x* J x = δ⁻¹ t`, where `δ = P.skewUnit`, is at most the integral of the modulus of its Gauss sums
over the skew frequencies, for the measure `P.skewMeasure`. -/
lemma measure_residueClass_le_lintegral (h : P.IsDisintegration volume J l) (hJ : Jᴴ = J)
    (hψ : ∀ x : A, P.ψ (x + star x) = 1) (g : Aˣ) (x₀ : κ → A) (t : skewAdjoint A) :
    l t (residueClass g x₀) ≤
      ∫⁻ b : skewAdjoint A, ‖classGaussSum J g x₀ (P.skewUnit⁻¹.val * t) b‖ₑ ∂P.skewMeasure := by
  classical
  let α : A := P.skewUnit⁻¹.val * t
  obtain h_top | h_lt :=
    eq_top_or_lt_top (∫⁻ b : skewAdjoint A, ‖classGaussSum J g x₀ α b‖ₑ ∂P.skewMeasure)
  · exact le_top.trans h_top.ge
  have h_int : Integrable (fun b : skewAdjoint A ↦ classGaussSum J g x₀ α b) P.skewMeasure :=
    integrable_classGaussSum h_lt
  have : IsFiniteMeasureOnCompacts (l t) := h.isFiniteMeasureOnCompacts t
  have h_fin : l t (residueClass g x₀) ≠ ∞ := (isCompact_residueClass g x₀).measure_ne_top
  calc l t (residueClass g x₀)
    _ = ‖∫ b : skewAdjoint A, classGaussSum J g x₀ α b ∂P.skewMeasure‖ₑ := by
      rw [integral_classGaussSum h hJ hψ g x₀ t h_int]
      simp [← ofReal_norm, h_fin]
    _ ≤ _ := enorm_integral_le_lintegral_enorm _

end New.Floors.IntegralPlace
