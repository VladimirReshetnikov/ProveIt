import Lib.SiegelWeil.OneVector.SiegelClassSum
import New.Spanning.Frames.TopFloor
import New.Spanning.MainTerm.GlobalToLocal
import New.Spanning.Unfolding.ReducedGroups

/-!
# Siegel's formula as an upper bound, and domination of class sums by the density at the last entry

Finite-place estimate of the filling theorem: global sums are bounded by integrals over the product
of the completions at a finite set `T` of places, stable under conjugation.

* `New.Filling.adelicFrequency`, `New.Filling.localFrequency`: passage between skew-adjoint
  frequencies at `T` and self-adjoint finite adeles, through multiplication by `-ϖ⁻¹` and `-ϖ`,
  where `ϖ = S.deltaE` generates the different.
* `New.Filling.normDensity_indicator_eq_mul`: the density of a test function that is `Ψ` at `T` and
  the indicator of the lattice off `T` splits into an integral of Gauss sums of the lattice and the
  density of `Ψ` at `T`.
* `New.Filling.IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure`: this density is
  at most `1 + b⁻⁶` times the volume of the lattice times the integral of `Ψ` over the sphere of `β`
  at `T`.
* `New.Filling.IsFillingData.siegel_sum_le_lintegral_sphere`: Siegel's formula bounds the sum of a
  step function over rational points with last entry `t` by a constant times its integral over the
  sphere of `t`.
* `New.Filling.IsFillingData.exists_step_sum_fiberPairing`: for any matrix `R`, the positive part of
  the real part of the sum of the fiber pairings against `R` is, on the top quadric, the restriction
  of a compactly supported invariant step function.
* `New.Filling.IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity`: the squared
  norms of class sums with one last entry `t` are bounded by `(1 + b⁻⁶) * S.scaledSiegelConst` times
  archimedean densities and densities at `T`, divided by the normalized mass.

The `IsFillingData` results assume `S` admissible, `S.ideleM⁻¹` integral off `T` and `F` filling
data. Conventions: `Φ v` is the embedding of the CM type at `v`. The last entry of `γ` is the
product of the last frame vector with its image under `γ`.

Notions from other files:
* `New.Floors.IntegralPlace`: A structure on `LocProd T`, the product of the completions at `T`: an
  open compact self-dual subring `R` of volume one, a character `ψ`, a trace-one element `τ`, a skew
  unit and the modulus `modulus`.
* `New.Filling.IsAdmissible`: The standing hypotheses: `sourceLevel` is the preimage of K(M),
  `reduction` is onto, and size inequalities hold between b and ϖ, κ_v, N, `besselDegree`, the
  second moments, the number of Bessel coordinates, an index and the mass.
* `New.Filling.latticeStabilizer`: The group `K` of integral points of the finite adelic unitary
  group; `New.Floors.PlaceData.congruenceSubgroup` is the group `K(M)` at `T`, the kernel of
  reduction modulo `M`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Filling


open NumberField MeasureTheory Matrix ENNReal NNReal Fintype Filter Topology Floors FloorGroups Set
  OpenAddSubgroup Finset Complex IntegralPlace CoordChange IsLargeLatticeData ComplexOrder

section

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [T.StarStable]

section Factorisation

variable (S T) in
/-- A skew frequency `b` at the places of `T`, as a self-adjoint finite adele: extend by zero and
multiply by `-ϖ⁻¹`, where `ϖ = S.deltaE` generates the different. -/
noncomputable def adelicFrequency (b : skewAdjoint (LocProd T)) : selfAdjoint (𝔸f E) :=
  ⟨(-S.deltaE.val⁻¹ : E) * adeleOfLocal T b.1, by
    simp [selfAdjoint.mem_iff, ← adeleOfLocal_star, skewAdjoint.star_val_eq,
      ← coe_star_ringOfIntegers, S.star_deltaE]⟩

variable (S T) in
/-- The part at the places of `T` of a self-adjoint finite adele, multiplied by `-ϖ`, where `ϖ =
S.deltaE` generates the different. -/
noncomputable def localFrequency (z : selfAdjoint (𝔸f E)) : skewAdjoint (LocProd T) :=
  ⟨evalPlaces T ((-S.deltaE.val : E) * z.1), by
    simp [skewAdjoint.mem_iff, star_evalPlaces, ← coe_star_ringOfIntegers, S.star_deltaE]⟩

@[fun_prop] lemma continuous_adelicFrequency : Continuous (S.adelicFrequency T) :=
  .subtype_mk (by fun_prop) _

@[fun_prop] lemma continuous_localFrequency : Continuous (S.localFrequency T) :=
  .subtype_mk (by fun_prop) _

lemma adelicFrequency_add (b b' : skewAdjoint (LocProd T)) :
    S.adelicFrequency T (b + b') = S.adelicFrequency T b + S.adelicFrequency T b' :=
  Subtype.ext (by simp [adelicFrequency, mul_add])

/-- `adelicFrequency` is a section of `localFrequency`, compatibly with translations. -/
lemma localFrequency_adelicFrequency_add (b : skewAdjoint (LocProd T)) (z : selfAdjoint (𝔸f E)) :
    S.localFrequency T (S.adelicFrequency T b + z) = b + S.localFrequency T z := by
  ext1
  simp [localFrequency, adelicFrequency, mul_add, ← mul_assoc, ← map_mul (algebraMap E (𝔸f E))]

/-- The difference of a self-adjoint adele `z` and `adelicFrequency (localFrequency z)` vanishes at
`T`, so it kills the adeles that vanish off `T`. -/
lemma sub_adelicFrequency_mul_adeleOfLocal (z : selfAdjoint (𝔸f E)) (a : LocProd T) :
    (z.1 - S.adelicFrequency T (S.localFrequency T z)) * adeleOfLocal T a = 0 := by
  have h_inv : ((-S.deltaE.val⁻¹ : E) : 𝔸f E) * (-S.deltaE.val : E) = 1 := by simp [← map_mul]
  have h_eval : evalPlaces T (z.1 - S.adelicFrequency T (S.localFrequency T z)) = 0 := by
    simp only [adelicFrequency, localFrequency, map_sub, map_mul (evalPlaces T),
      evalPlaces_adeleOfLocal, ← mul_assoc]
    rw [← map_mul, h_inv, map_one, one_mul, sub_self]
  rw [← adeleOfLocal_evalPlaces_mul, h_eval, zero_mul, map_zero]

variable [P : IntegralPlace (LocProd T)]

/-- Let `b` be skew in `LocProd T`, let `b̃ = S.adelicFrequency T b` be `-ϖ⁻¹ b` extended by zero,
and let `y` be a self-adjoint finite adele. Then `ψf E (b̃ y / 2) = P.ψ (τ b y_T)`, where `y_T` is
the part of `y` at `T` and `τ = P.element` has `τ + τ̄ = 1`. `P` is a place structure on `LocProd T`
whose character `P.ψ` is `x ↦ ψf E (-x / ϖ)` (`S.charOnPlaces T`). -/
lemma ψf_adelicFrequency_mul (hψ : P.ψ = S.charOnPlaces T) (b : skewAdjoint (LocProd T)) {y : 𝔸f E}
    (hy : star y = y) :
    (ψf E ((2⁻¹ : E) * (S.adelicFrequency T b * y)) : ℂ) = P.ψ
      (P.element * b * evalPlaces T y) := by
  let x : 𝔸f E := (-S.deltaE.val⁻¹ : E) * adeleOfLocal T (P.element * b * evalPlaces T y)
  have h_local : P.element * b * evalPlaces T y - star (P.element * b * evalPlaces T y) =
      evalPlaces T y * b := by
    rw [star_mul', star_mul', star_evalPlaces, hy, skewAdjoint.star_val_eq]
    linear_combination (evalPlaces T y * b) * P.element_add_star
  have h_trace : x + star x = S.adelicFrequency T b * y := by
    rw [star_mul', star_neg_inv_deltaE, ← adeleOfLocal_star, neg_mul, ← sub_eq_add_neg, ← mul_sub,
      ← map_sub, h_local, adeleOfLocal_evalPlaces_mul, adelicFrequency, mul_assoc, mul_comm y]
  rw [← h_trace, ψf_inv_two_mul_add_star, hψ, charOnPlaces_apply_eq_ψf]

/-- The phase `ψf E (ζ (x* x - β) / 2)` that detects the quadric `x* x = β` is a product of a phase
off `T` and a phase at `T`. The frequency `ζ` is the sum of `S.adelicFrequency T b` and of a
self-adjoint adele `z` for which `S.localFrequency T z` is integral. The vector `x` is the sum of a
vector `y` at `T`, extended by zero (`adeleOfLocal`), and of an adelic vector `w` integral at `T`.
`P` is a place structure on `LocProd T` whose character `P.ψ` is `x ↦ ψf E (-x / ϖ)`
(`S.charOnPlaces T`). -/
lemma ψf_quadric_eq_mul (hψ : P.ψ = S.charOnPlaces T) {κ : Type} [Fintype κ] {β : 𝔸f E}
    (hβ : star β = β) (b : skewAdjoint (LocProd T)) {z : selfAdjoint (𝔸f E)}
    (hz : (S.localFrequency T z : LocProd T) ∈ P.integers) (y : κ → LocProd T) {w : κ → 𝔸f E}
    (hw : evalPlaces T ∘ w ∈ intVectors P.integers κ) :
    let x : κ → 𝔸f E := adeleOfLocal T ∘ y + w
    let y' : κ → LocProd T := y + evalPlaces T ∘ w
    (ψf E ((2⁻¹ : E) * ((S.adelicFrequency T b + z).val * (star x ⬝ᵥ x - β))) : ℂ) =
      ψf E ((2⁻¹ : E) * ((z : 𝔸f E) * (star w ⬝ᵥ w - (β - adeleOfLocal T (evalPlaces T β))))) *
        P.ψ (P.element * (b + S.localFrequency T z).val * (star y' ⬝ᵥ y' - evalPlaces T β)) := by
  intro x y'
  set β' : 𝔸f E := β - adeleOfLocal T (evalPlaces T β)
  set b' : skewAdjoint (LocProd T) := S.localFrequency T z
  have hβ' : star β' = β' := by simp [β', ← adeleOfLocal_star, hβ]
  have norm_star (v : κ → 𝔸f E) : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := (star_dotProduct v v).symm
  have eval_x : evalPlaces T (star x ⬝ᵥ x - β) = star y' ⬝ᵥ y' - evalPlaces T β := by
    simp [x, y', dotProduct, ← star_evalPlaces]
  -- the values of the form at `x` and `w` differ only at `T`
  have h_diff : star x ⬝ᵥ x - β - (star w ⬝ᵥ w - β') = adeleOfLocal T
      (star y ⬝ᵥ y' + star (evalPlaces T ∘ w) ⬝ᵥ y - evalPlaces T β) := by
    simp [x, y', β', dotProduct, Finset.sum_add_distrib, mul_add, add_mul, adeleOfLocal_star,
      adeleOfLocal_evalPlaces_mul, mul_comm _ (evalPlaces T _), mul_comm (w _)]
    ring
  have h_arg : (S.adelicFrequency T b + z).1 * (star x ⬝ᵥ x - β) =
      z * (star w ⬝ᵥ w - β') + S.adelicFrequency T (b + b') * (star x ⬝ᵥ x - β) -
        S.adelicFrequency T b' * (star w ⬝ᵥ w - β') := by
    rw [adelicFrequency_add, AddSubgroup.coe_add, AddSubgroup.coe_add]
    linear_combination (z.1 - S.adelicFrequency T b') * h_diff +
      S.sub_adelicFrequency_mul_adeleOfLocal (T := T) z _
  -- the last term is integral at `T`, so its phase is one
  have h_int : P.ψ (P.element * b' * evalPlaces T (star w ⬝ᵥ w - β')) = 1 := by
    have h_norm : evalPlaces T (star w ⬝ᵥ w - β') ∈ P.integers := by
      simpa [β', dotProduct, ← star_evalPlaces] using
        sum_mem fun i _ ↦ mul_mem (P.isAdelic.star_mem (hw i)) (hw i)
    obtain ⟨tau_mem : P.element ∈ P.integers, -⟩ := P.data_normalised
    exact (P.self_dual _).2 h_norm _ (mul_mem tau_mem hz)
  rw [h_arg, mul_sub, mul_add, AddChar.map_sub_eq_div, AddChar.map_add_eq_mul, Circle.coe_div,
    Circle.coe_mul, ψf_adelicFrequency_mul hψ _ (by simp [norm_star, hβ]),
    ψf_adelicFrequency_mul hψ _ (by simp [norm_star, hβ']), h_int, div_one, eval_x]

/-- Let `f` be the function on adelic vectors that is `Ψ` at `T` times the indicator of the vectors
integral off `T`, and let `β` be hermitian. The density `normDensity f β = ∫ z, ∫ x, f x * ψf E (z
(x* x - β) / 2)` is a product of two factors. The first is the integral of the Gauss sums of the
standard lattice over the self-adjoint `z` for which `S.localFrequency T z`, the part of `-ϖ z` at
`T`, is integral. The second is the density of `Ψ` at `T`, with `P.skewMeasure` the measure on skew
elements and `P.element` of trace `1`. `P` is a place structure on `LocProd T` whose character `P.ψ`
is `x ↦ ψf E (-x / ϖ)` (`S.charOnPlaces T`).

This is a two-factor form of the factorization of the finite adelic density into local densities,
as in Siegel–Weil theory: the density at `T` and one integral of Gauss sums, not split over the
remaining places. -/
lemma normDensity_indicator_eq_mul [WeilData E] (hψ : P.ψ = S.charOnPlaces T) {κ : Type} [Fintype κ]
    {Ψ : (κ → LocProd T) → ℝ≥0} (hΨ : Continuous Ψ) {β : 𝔸f E} (hβ : star β = β) :
    normDensity ((intVectors (integralOff T) κ : Set (κ → 𝔸f E)).indicator
        fun x : κ → 𝔸f E ↦ Ψ (evalPlaces T ∘ x)) β =
      (∫ z : selfAdjoint (𝔸f E) in
          {z : selfAdjoint (𝔸f E) | (S.localFrequency T z : LocProd T) ∈ P.integers},
        ∫ w : κ → 𝔸f E in (stdLattice E κ : Set (κ → 𝔸f E)),
          (ψf E ((2⁻¹ : E) *
            ((z : 𝔸f E) * (star w ⬝ᵥ w - (β - adeleOfLocal T (evalPlaces T β))))) : ℂ)) *
      ∫ b : skewAdjoint (LocProd T), ∫ y : κ → LocProd T,
        Ψ y * P.ψ (P.element * (b : LocProd T) * (star y ⬝ᵥ y - evalPlaces T β))
        ∂volume ∂P.skewMeasure := by
  classical
  -- Split first the frequency and then the vector into their parts at `T` and off `T`.
  let L : Set (κ → 𝔸f E) := intVectors (integralOff T) κ
  have L_meas : MeasurableSet L := (isOpen_intVectors (isOpen_integralOff T)).measurableSet
  obtain ⟨lat_open, -, lat_vol⟩ := P.isOpen_isCompact_volume_intVectors (ι := κ)
  obtain ⟨-, -, -, -, skew_vol⟩ := P.data_normalised
  have lattice_eq : (stdLattice E κ : Set (κ → 𝔸f E)) =
      (evalPlaces T ∘ ·) ⁻¹' intVectors P.integers κ ∩ L := by
    ext
    simp [coe_stdLattice, L, intVectors, mem_Ô_iff T, forall_and]
  -- the frequency: `adelicFrequency` is a section of `localFrequency`
  rw [normDensity]
  refine integral_eq_mul_of_section P.skewMeasure (by fun_prop) (by fun_prop)
    localFrequency_adelicFrequency_add
    (SemilocalField.isOpen_O.preimage continuous_subtype_val).measurableSet skew_vol fun b z hz ↦ ?_
  rw [integral_withDensity_eq_integral_smul (.indicator (by fun_prop) L_meas), lattice_eq,
    ← setIntegral_indicator L_meas]
  -- the vector: `adeleOfLocal T` is a section of `evalPlaces T`
  have h_section (y : κ → LocProd T) (x : κ → 𝔸f E) :
      evalPlaces T ∘ (adeleOfLocal T ∘ y + x) = y + evalPlaces T ∘ x := by simp [funext_iff]
  refine integral_eq_mul_of_section volume (ι := (adeleOfLocal T ∘ ·)) (by fun_prop) (by fun_prop)
    h_section lat_open.measurableSet lat_vol fun y w hw ↦ ?_
  have mem_L : adeleOfLocal T ∘ y + w ∈ L ↔ w ∈ L :=
    forall_congr' fun i ↦ add_mem_cancel_left (adeleOfLocal_mem_integralOff T (y i))
  rw [ψf_quadric_eq_mul hψ hβ b hz y hw]
  by_cases hw' : w ∈ L
  · rw [Set.indicator_of_mem (mem_L.2 hw'), Set.indicator_of_mem hw', h_section, NNReal.smul_def,
      real_smul, mul_left_comm]
  · rw [Set.indicator_of_notMem (mem_L.not.2 hw'), Set.indicator_of_notMem hw', zero_smul, zero_mul]

end Factorisation

variable (S T) in
/-- The finite idele `π = S.piN`, with `π π̄ = N`, read at the places of `T`. -/
noncomputable abbrev piNAt : (LocProd T)ˣ := S.piN.map (evalPlaces T)

lemma piNAt_mul_star : S.piNAt T * star (S.piNAt T).1 = (S.N : LocProd T) := by
  simpa [star_evalPlaces] using congrArg (evalPlaces T) S.piN_mul_star

end

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [T.StarStable]

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose character is that of
`S`. Let `K(M) = F.congruenceSubgroup` be the group of integral isometries at `T` of the form
`S.latticeMiddle` congruent to `1` modulo `M`, let `Z` be a group between `K(M)` and the integral
isometries, and let `Z.Cosets` be the cosets of `K(M)` in `Z`. Write `μ = F.groupMeasure` for the
measure of the unitary group at `T` and `μ_H = F.measureH` for that of `H = besselH`, the fixer of
all basis vectors outside the definite part `X₀`. Then there is a real `D > 0` with two properties.
The constant `S.scaledSiegelConst` is `D` times the number of classes times the constant
`S.siegelConst` of Siegel's formula. The normalized mass
`Z.massRatio = μ Z * μ K(M) / F.unipotentMass ^ 2`, where `F.unipotentMass` is the product of the
floor volumes below `ϱ`, is at most `μ_H K(M) * (μ K(M) ^ 2 * card Z.Cosets) * D`. -/
lemma IsFillingData.exists_scaledSiegelConst_eq_and_massRatio_le
    [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) :
    ∃ D : ℝ,
      0 < D ∧
      S.scaledSiegelConst = D * Fintype.card S.Classes * S.siegelConst ∧
      Z.massRatio ≤ F.measureH F.congruenceSubgroup *
        (F.groupMeasure F.congruenceSubgroup ^ 2 * Fintype.card Z.Cosets) * ENNReal.ofReal D := by
  -- In `Z.massRatio = F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup / F.unipotentMass ^ 2`
  -- cover `Z` by the cosets of `F.congruenceSubgroup` and use
  -- `S.unipotentOrder * F.unipotentMass = 1`. Here `D = card (reducedImage besselS) *
  -- S.unipotentOrder = card (reducedImage besselH) * S.unipotentOrder ^ 2`.
  refine ⟨Nat.card (S.reducedImage besselS) * S.unipotentOrder, ?_, rfl, div_le_of_le_mul ?_⟩
  · have hM : 0 < S.M := two_pos.trans_le two_le_M
    have h_card : 0 < Nat.card (S.reducedImage besselS) := Nat.card_pos
    positivity
  -- for `F.measureH`, the group `F.congruenceSubgroup` has index `card (reducedImage besselH)` in
  -- the integral points
  obtain ⟨h_carried : ∀ᵐ z ∂F.measureH, z ∈ besselH,
      h_invariant : ∀ s ∈ besselH, F.measureH ∗ₘ .dirac s = F.measureH, -⟩ :=
        F.measureH_mem_and_invariant_and_le_one
  obtain ⟨-, h_box : F.boxSet = unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
      h_box_mass : F.measureH F.boxSet = 1, -⟩ := hF.volume_le_and_boxSet_closePairs_positions_eq
  have h_lift : ∀ᵐ z ∂F.measureH, ∃ x ∈ besselH, S.toPlaces T x = z ∧ S.IsIntegralOff T x := by
    filter_upwards [h_carried] with z hz
    obtain ⟨x, h_eq, h_off, -, h_mem⟩ := exists_isIntegralOff_toPlaces_eq z
    exact ⟨x, h_mem hz, h_eq, h_off⟩
  have index : Nat.card (S.reducedImage besselH) * F.measureH F.congruenceSubgroup = 1 := by
    rw [← h_box_mass, h_box]
    exact hF.card_reducedImage_mul_measure_congruenceSubgroup_eq h_lift fun x hx ↦
      h_invariant _ (hx.map_mem_agreeWithOneOn _)
  have cover : (Z.val : Set (U (S.latticeMiddle (LocProd T)).splitGram)) ⊆
      ⋃ d : Z.Cosets, (· * d.out.val⁻¹) ⁻¹' F.congruenceSubgroup :=
    fun y hy ↦ Set.mem_iUnion.2 ((Z.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq hy).imp
      fun d hd ↦ (hd d).2 rfl)
  have h_Z : F.groupMeasure Z ≤ Fintype.card Z.Cosets * F.groupMeasure F.congruenceSubgroup := by
    grw [cover, measure_iUnion_fintype_le]
    simp
  calc F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup
    _ ≤ Fintype.card Z.Cosets * F.groupMeasure F.congruenceSubgroup * F.groupMeasure
      F.congruenceSubgroup := by
      gcongr
    _ = Nat.card (S.reducedImage besselH) * F.measureH F.congruenceSubgroup *
        (F.groupMeasure F.congruenceSubgroup ^ 2 * Fintype.card Z.Cosets) *
        (S.unipotentOrder * F.unipotentMass) ^ 2 := by
      rw [index, hF.unipotentOrder_mul_unipotentMass_eq_one]
      ring
    _ = F.measureH F.congruenceSubgroup *
      (F.groupMeasure F.congruenceSubgroup ^ 2 * Fintype.card Z.Cosets) *
        ENNReal.ofReal (Nat.card (S.reducedImage besselS) * S.unipotentOrder) *
        F.unipotentMass ^ 2 := by
      rw [← Nat.cast_mul, ENNReal.ofReal_natCast, card_reducedImage_besselS]
      push_cast
      ring

variable [ok : S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)]

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- Let `N⁻¹` be integral off `T`, for the prime `N = S.N`. Let `β = (t t̄ - N²) / N` be positive
under the embeddings `Φ v` of the CM type, and let `C` be the constant of Siegel's formula in rank
`k = card 𝔰.κ` at `β`; its first factor `classSum stdRatPoints S.sourceLevel 1` is the mass of the
set `S.Classes` of double cosets of the level `S.sourceLevel` in the definite unitary group. Let `u`
be a unit at `T` with `u ū = N`, and `P.modulus u` its modulus. Then `‖C‖` times `1 + S.b⁻⁶`, the
volume `volÔ E ^ k` of the standard lattice and `P.modulus u` is
`(1 + S.b⁻⁶) * card S.Classes * S.siegelConst` times `(∏ v, (|t|_v² - N²)) ^ (k - 1)`. Here `S.b` is
the size parameter of `S` and `S.siegelConst = (π^k / ((k - 1)! N^k))^f |disc E|^(1/4) (volÔ E)^k`,
with `f` the number of infinite places. -/
lemma siegel_constant_eq (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    [P : IntegralPlace (LocProd T)] {t : E} {u : (LocProd T)ˣ} (hu : u * star u.1 = S.N)
    (hβ_pos : ∀ v : InfinitePlace E, 0 < (Φ v ((t * star t - S.N ^ 2) / S.N)).re) {C : ℂ}
    (hC : (classSum stdRatPoints S.sourceLevel 1 * √√|NumberField.discr E| *
      ∏ v : InfinitePlace E, Real.pi ^ card 𝔰.κ / (card 𝔰.κ - 1).factorial *
        (Φ v ((t * star t - S.N ^ 2) / S.N)).re ^ (card 𝔰.κ - 1) : ℝ) = C) :
    ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k) * P.modulus u =
      .ofReal ((1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst *
        (∏ v : InfinitePlace E, (‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) := by
  have hN₀ : 0 < S.N := S.N_prime.pos
  obtain ⟨d, h_rank : 1000 * (2 * 𝔰.ϱ + 2) + d = 𝔰.k⟩ := S.thousand_mul_le_k.dest
  -- The product formula for `N = u ū` gives `P.modulus u` as a power of `N⁻¹`.
  have h_formula : P.modulus (evalPlaces T ((S.N : E) : 𝔸f E)) ^ (2⁻¹ : ℝ) =
      (∏ v : InfinitePlace E, ‖Φ v (S.N : E)‖ₑ)⁻¹ :=
    P.modulus_evalPlaces_rpow_half (x := .mk0 _ (by simp [Nat.Prime.ne_zero])) ⟨by simp, hT_N⟩
  have h_md : P.modulus u.1 = (‖(S.N : ℂ)‖ₑ ^ card (InfinitePlace E))⁻¹ := by
    simpa [← hu, ← sq, ← ENNReal.rpow_natCast_mul] using h_formula
  -- both sides are finite, so they are compared as real numbers
  have h_finite : ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k) * P.modulus u ≠ ∞ := by
    simp [mul_eq_top]
  refine (ofReal_toReal h_finite).symm.trans (congrArg _ ?_)
  set β : E := (t * star t - S.N ^ 2) / S.N
  rw [h_md, ← hC]
  -- evaluate the class sum of `1`, then expand `S.siegelConst` and `β`
  simp (disch := positivity) [classSum_sourceLevel_eq_sum, abs_of_nonneg, abs_of_pos (hβ_pos _),
    prod_mul_distrib]
  simp [siegelConst, β, mul_conj', sq, div_pow, ← h_rank, mul_add, Finset.prod_pow]
  field

section Level

variable [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

omit [IntegralPlace (LocProd T)] in
/-- Let `Ψ` be a function of compact support on the vectors of the whole space over the product
`LocProd T` of the completions at `T`. For `x` in the definite part `X₀` (basis `𝔰.κ`) let
`vectorOfLastEntry π τ x` be `x - (π π̄)⁻¹ τ z` in the basis `besselLatticeBasis 𝔰 π`, with `z` the
last frame vector. Then the function on adelic vectors `y` of `X₀` that is
`Ψ (vectorOfLastEntry π τ y_T)`, with `y_T` the part of `y` at `T`, times the indicator of the
vectors integral off `T` has compact support. -/
lemma hasCompactSupport_testFunction {Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0}
    (hΨ : HasCompactSupport Ψ) (π : (LocProd T)ˣ) (τ : LocProd T) :
    HasCompactSupport ((intVectors (integralOff T) 𝔰.κ : Set (𝔰.κ → 𝔸f E)).indicator
      fun y : 𝔰.κ → 𝔸f E ↦ Ψ (vectorOfLastEntry π τ (evalPlaces T ∘ y))) := by
  -- A vector in the support is an integral vector plus the extension by zero of its part at
  -- `T`, and that part is read off a point of the support of `Ψ`.
  let part (e : 𝔰.BesselIndex → LocProd T) (i : 𝔰.κ) : 𝔸f E :=
    adeleOfLocal T (((besselLatticeBasis 𝔰 π).val *ᵥ e) (𝔰.indexX₀ i))
  refine .of_support_subset_isCompact
    ((hΨ.image (f := part) (by fun_prop)).add stdLattice.isCompact_stdLattice) ?_
  rw [support_indicator]
  rintro y ⟨hy_int, hy_supp⟩
  let e : 𝔰.BesselIndex → LocProd T := vectorOfLastEntry π τ (evalPlaces T ∘ y)
  have h_int : ∀ i : 𝔰.κ, (y - part e) i ∈ Ô E := fun i ↦ by
    simpa [e, part, vectorOfLastEntry, sub_adeleOfLocal_mem_iff] using hy_int i
  exact ⟨part e, ⟨e, subset_closure hy_supp, rfl⟩, y - part e, h_int, add_sub_cancel ..⟩

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose character is that of
`S`. Let `f` be the function on adelic vectors `x` of `X₀` that is `Ψ (x - N⁻¹ t z)` at `T`
(`vectorOfLastEntry`, for `N = π π̄`, `π = S.piN` and a rational `t`) times the indicator of the
vectors integral off `T`. If `Ψ` is invariant under `besselH ⊓ F.congruenceSubgroup`, then `f` is
invariant under the level `S.sourceLevel` of the finite adelic unitary group `Gf E 𝔰.κ` of `X₀`. -/
lemma IsFillingData.testFunction_mulVec (hF : S.IsFillingData T F)
    {Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0}
    (hΨ : ∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → LocProd T,
      Ψ (k.val.val *ᵥ x) = Ψ x)
    (t : E) {k : Gf E 𝔰.κ} (hk : k ∈ S.sourceLevel) (y : 𝔰.κ → 𝔸f E) :
    let f : (𝔰.κ → 𝔸f E) → ℝ≥0 := (intVectors (integralOff T) 𝔰.κ : Set (𝔰.κ → 𝔸f E)).indicator
      fun x : 𝔰.κ → 𝔸f E ↦ Ψ (vectorOfLastEntry (S.piN.map (evalPlaces T)) (evalPlaces T t)
        (evalPlaces T ∘ x))
    f ((k : Matrix 𝔰.κ 𝔰.κ (𝔸f E)) *ᵥ y) = f y := by
  classical
  have h_int : k.val ∈ intGL 𝔰.κ (integralOff T) := by
    have h_full : k.val ∈ intGL 𝔰.κ (Ô E) := S.isLevel_sourceLevel.le hk
    grind [mem_intGL, mem_Ô_iff T]
  -- at `T` the matrix `k` acts on the vectors with last entry `t` as an element `k'` of
  -- `F.congruenceSubgroup`
  let k' : U (S.latticeMiddle (LocProd T)).splitGram := S.toPlaces T (S.inclHFin k)
  have hk' : k' ∈ besselH ⊓ F.congruenceSubgroup :=
    ⟨(inclHFin_mem_besselH k).map_mem_agreeWithOneOn _,
      (hF.mem_principalLevel_iff.mp (ok.sourceLevel_eq.le hk)).2⟩
  let tail (x : 𝔰.κ → 𝔸f E) : 𝔰.BesselIndex → LocProd T :=
    vectorOfLastEntry (S.piN.map (evalPlaces T)) (evalPlaces T t) (evalPlaces T ∘ x)
  have h_tail : tail (k.val.val *ᵥ y) = k'.val.val *ᵥ tail y := by
    have h_map : k'.val.val = (S.inclHFin k).val.val.map (evalPlaces T) := rfl
    ext1
    simp only [tail, vectorOfLastEntry_evalPlaces, h_map, ← RingHom.map_mulVec]
    simp [vectorOfLastEntry, inclHFin, toLatticeBasis, ← mulVec_mulVec,
      mulVec_mulVec _ (besselLatticeBasis ..).val, toBesselH, fromBlocks_mulVec]
  exact if_congr (mulVec_mem_intVectors_iff h_int) ((congrArg Ψ h_tail).trans (hΨ k' hk' _)) rfl

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- Let `M = S.ideleM` be the level, and let `F` be a filling datum at `T`: a large lattice datum of
modulus `M` for the place structure `P`, whose character is that of `S`. Let `Ψ ≥ 0` be continuous
of compact support on the vectors of rank `k = card 𝔰.κ` over the product `LocProd T` of the
completions at `T`, and let `β` be hermitian. Let `f` be `Ψ` at `T` times the indicator of the
vectors integral off `T`. The density `normDensity f β = ∫ z, ∫ x, f x * ψf E (z (x* x - β) / 2)`
has norm at most `1 + S.b⁻⁶` times the volume `volÔ E ^ k` of the standard lattice times the
integral of `Ψ` over the sphere `y* y = β` at `T`. The sphere carries the fiber measure
`P.normFiberMeasure` with index `δβ`, the product of `δ = P.skewUnit` and the part of `β` at `T`.

This is an upper bound form of the factorization into local densities in Siegel–Weil theory: the
factor at `T` is kept, and the remaining factor is only bounded, by `(1 + S.b⁻⁶) volÔ E ^ k`. -/
lemma IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure [WeilData E]
    (hF : S.IsFillingData T F)
    {Ψ : (𝔰.κ → LocProd T) → ℝ≥0} (hΨ : Continuous Ψ) (h_supp : HasCompactSupport Ψ) {β : 𝔸f E}
    (hβ : star β = β) {δβ : skewAdjoint (LocProd T)}
    (hδβ : P.skewUnit⁻¹.1 * δβ = evalPlaces T β) :
    ‖normDensity ((intVectors (integralOff T) 𝔰.κ : Set (𝔰.κ → 𝔸f E)).indicator
        fun x : 𝔰.κ → 𝔸f E ↦ Ψ (evalPlaces T ∘ x)) β‖ₑ ≤
      .ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k *
        ∫⁻ y : 𝔰.κ → LocProd T, Ψ y ∂P.normFiberMeasure 𝔰.κ δβ := by
  have h_rank : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
  -- the exponent of the ideal zeta sum is `μ = 3ϱ + 4`, and `2 (μ + 1) ≤ k`
  have h_degree : 1 * Module.finrank ℚ E ≤ 2 ^ (2 * 𝔰.ϱ) :=
    S.mul_finrank_le_pow.trans' (by gcongr; lia)
  have h_zeta : idealZeta (Ô E) (𝔰.ϱ + 2 * 𝔰.ϱ + 4) ≤ .ofReal (1 + S.b⁻¹ ^ 6) := by
    grw [← S.half_pow_le_inv_pow_six]
    simpa using idealZeta_intAdeles_pow_le 𝔰.ϱ h_degree
  have h_card : 2 * (𝔰.ϱ + 2 * 𝔰.ϱ + 4 + 1) ≤ card 𝔰.κ := by
    simpa using show 2 * (𝔰.ϱ + 2 * 𝔰.ϱ + 4 + 1) ≤ 𝔰.k by omega
  rw [normDensity_indicator_eq_mul hF.psi_eq hΨ hβ, enorm_mul]
  gcongr
  · -- the integral of Gauss sums off `T`
    grw [enorm_integral_le_lintegral_enorm, setLIntegral_le_lintegral, ← h_zeta]
    exact lintegral_gauss_sum_le_idealZeta
      (le_two_of_pow_le_ofReal (idealZeta_intAdeles_pow_le 𝔰.ϱ h_degree)) h_card _
  · simpa only [one_mulVec, hδβ] using enorm_localDensity_le
      (P.isDisintegration_normFiberMeasure hF.two_le_card) conjTranspose_one hF.psi_add_star hΨ
        h_supp δβ

omit [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] ok in
/-- Let `t` be in `E`, read at `T` as `ratToPlaces T t`, and let `π = S.piNAt T` be the unit at `T`
with `π π̄ = N = S.N`. Then the index `lastEntrySphereIndex π t` of the sphere
`ω* ω = t t̄ / N - N`, divided by `P.skewUnit`, is the value at `T` of `β = (t t̄ - N²) / N`. -/
lemma skewUnit_inv_mul_lastEntrySphereIndex_piNAt (t : E) :
    P.skewUnit⁻¹.1 * lastEntrySphereIndex (S.piNAt T) (ratToPlaces T t) =
      evalPlaces T (((t * star t - S.N ^ 2) / S.N : E) : 𝔸f E) := by
  set π : (LocProd T)ˣ := S.piNAt T
  set β : E := (t * star t - S.N ^ 2) / S.N
  have hπ : π * star π.1 = S.N := piNAt_mul_star
  have h_rat : t * star t = S.N * (β + S.N) := by field [S.N_prime.ne_zero]
  have h_coe : (lastEntrySphereIndex π (ratToPlaces T t)).1 = P.skewUnit *
      ((π * star π)⁻¹.1 * ratToPlaces T t * star (ratToPlaces T t) - π * star π.1) := rfl
  rw [h_coe, Units.inv_mul_cancel_left, sub_eq_iff_eq_add, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
  simpa [hπ] using congrArg (ratToPlaces T) h_rat

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose character is that of
`S`. The space has the hyperbolic pairs `e_a, e*_a` (`a < ϱ`), a definite part `X₀` with basis `𝔰.κ`
and a vector `z`; `floorGroup 𝔰.ϱ` is the group of isometries that fix the hyperbolic pairs. Let
`γ₁`, `γ₂` be elements of this group over `E` with the same product `⟨z, γ z⟩`
(`S.frameProducts γ 𝔰.top 𝔰.top`) and the same `X₀`-part of `γ z`. Let `h_c` be the representative
of the double coset `c`, and let the left classes `c₁`, `c₂` be equal. If the translates
`h_c⁻¹ γ h_c'` (`S.translateByClassReps`) are integral off `T` and lie in one coset of
`F.congruenceSubgroup` at `T`, then `γ₁ = γ₂` and the right classes `c₁'`, `c₂'` are equal. -/
lemma IsFillingData.classes_eq_and_eq_of_inv_mul_mem_congruenceSubgroup (hF : S.IsFillingData T F)
    {c₁ c₂ c₁' c₂' : S.Classes} {γ₁ γ₂ : S.G E} (h_leftClass : c₁ = c₂)
    (hγ₁ : γ₁ ∈ floorGroup 𝔰.ϱ) (hγ₂ : γ₂ ∈ floorGroup 𝔰.ϱ)
    (h_tail : S.frameProducts γ₁ 𝔰.top 𝔰.top = S.frameProducts γ₂ 𝔰.top 𝔰.top)
    (h_col : ∀ l : 𝔰.κ, γ₁.val.val (𝔰.indexX₀ l) 𝔰.z = γ₂.val.val (𝔰.indexX₀ l) 𝔰.z)
    (h_off₁ : S.IsIntegralOff T (S.translateByClassReps c₁ c₁' γ₁))
    (h_off₂ : S.IsIntegralOff T (S.translateByClassReps c₂ c₂' γ₂))
    (h_coset : (S.toPlaces T (S.translateByClassReps c₁ c₁' γ₁))⁻¹ *
      S.toPlaces T (S.translateByClassReps c₂ c₂' γ₂) ∈ F.congruenceSubgroup) :
    c₁' = c₂' ∧ γ₁ = γ₂ := by
  -- `γ₁⁻¹` and `γ₂⁻¹` give the same point `FloorGroups.orbitPoint 𝔰.top`, so `γ₁⁻¹ γ₂` lies in
  -- `floorGroup 𝔰.n`; its `translateByClassReps` lies in `S.principalLevel`, which forces
  -- `c₁' = c₂'` and makes it unipotent, hence trivial.
  have same_z : FloorGroups.orbitPoint 𝔰.top γ₁⁻¹ = FloorGroups.orbitPoint 𝔰.top γ₂⁻¹ := by
    simpa [funext_iff, Unique.forall_iff, FloorGroups.orbitPoint,
      apply_eq_one_apply_of_mem_floorGroup hγ₁,
      apply_eq_one_apply_of_mem_floorGroup hγ₂, h_col, frameGram, splitGram, mul_apply, middleGram,
      Nat.Prime.ne_zero] using h_tail
  have fixes : γ₁⁻¹ * γ₂ ∈ floorGroup 𝔰.n :=
    partialUnitriangularGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq hγ₁ hγ₂ same_z)
  have level : S.translateByClassReps c₁' c₂' (γ₁⁻¹ * γ₂) ∈ S.principalLevel := by
    have h_quotient : S.translateByClassReps c₁' c₂' (γ₁⁻¹ * γ₂) =
        (S.translateByClassReps c₁ c₁' γ₁)⁻¹ * S.translateByClassReps c₂ c₂' γ₂ := by
      simp [translateByClassReps, h_leftClass, mul_assoc]
    rw [h_quotient]
    exact hF.mem_principalLevel_iff.mpr ⟨mul_mem (inv_mem h_off₁) h_off₂, by simpa using h_coset⟩
  obtain ⟨hc', hU : γ₁⁻¹ * γ₂ ∈ besselU, -⟩ :=
    eq_and_mem_classUnipotent_of_besselS (mem_partialUnitriangularGroup_of_mem_floorGroup fixes)
      level
  exact ⟨hc', inv_mul_eq_one.mp <|
    eq_one_of_mem_floorGroup_inf ⟨fixes, (unipotentBelow_eq_besselU le_rfl).ge hU⟩ (by simp)⟩

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- Let `Z` be a group between the congruence group `F.congruenceSubgroup` and the integral
isometries, `R` a matrix and `ω p` finitely many heads. The fiber pairing
`F.fiberPairing Z (ω p) (ω q)` is the pairing of the orbital integrals `F.scaledOrbitalIntegral Z`
of two heads, integrated over `besselH`, the fixer of all basis vectors outside the definite part
`X₀`. On the top quadric the positive part of the real part of their sum against `R` agrees with a
function `Ψ ≥ 0` of compact support, invariant under small translations and under
`besselH ⊓ F.congruenceSubgroup`. -/
lemma IsFillingData.exists_step_sum_fiberPairing (hF : S.IsFillingData T F)
    (Z : F.IntermediateGroup) {J : Type} [Fintype J] (R : Matrix J J ℂ) (ω : J → ℕ → (LocProd T)ˣ) :
    ∃ Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0,
      HasCompactSupport Ψ ∧
      (∀ᶠ v : 𝔰.BesselIndex → LocProd T in 𝓝 0, ∀ x : 𝔰.BesselIndex → LocProd T, Ψ (x + v) = Ψ x) ∧
      (∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → LocProd T,
        Ψ (k.val.val *ᵥ x) = Ψ x) ∧
      ∀ e ∈ lastVectorQuadric (S.latticeMiddle (LocProd T)),
        Ψ e = ENNReal.ofReal (∑ p : J, ∑ q : J, R p q * F.fiberPairing Z (ω p) (ω q) e).re := by
  choose Ψpair pair_supp pair_unif pair_inv pair_eq using
    fun p q : J ↦ exists_step_function_eqOn_fiberPairing Z (ω p) (ω q)
  refine ⟨fun e ↦ (∑ p, ∑ q, R p q * Ψpair p q e).re.toNNReal, ?_, ?_, fun k hk x ↦ ?_,
    fun e he ↦ ?_⟩
  · refine .intro (isCompact_iUnion fun p ↦ isCompact_iUnion fun q ↦ pair_supp p q) fun e he ↦ ?_
    simp only [mem_iUnion, not_exists] at he
    simp [fun p q ↦ image_eq_zero_of_notMem_tsupport (he p q)]
  · filter_upwards [eventually_all.2 fun p ↦ eventually_all.2 fun q ↦ pair_unif p q] with v hv x
    simp only [hv]
  · simp only [pair_inv _ _ k hk]
  · simp only [pair_eq _ _ e he, ENNReal.ofReal]

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`. Let `Z` be a group between the congruence group `F.congruenceSubgroup` and the integral
isometries at `T`. The heads `a p` (`p : J`) are sequences in `Eˣ`, with Weyl elements
`w_p = weylElem 𝔰.ϱ (a p)` and entries below `ϱ` that are units off `T`; `F.headDensity` is a
product of powers of the moduli of these entries at `T`. Let `W = S.besselFn side` be the Bessel
function at the infinite places or its cut, as `side` says, and let `R` be the Gram matrix of the
tensors `ρ p • ∫ W(y) ⊗ W((w_p γ)⁻¹ y)^* dy` (`besselOrbitalIntegral`). Let `ρ p` times the head
density be the same number `w` for all `p`. Let the integral elements `n i` (`i : ι`) lie in `Z` at
`T` and have distinct reductions `s i`. Then the squared norms of
`∑ p, S.cosetAmplitude side c (s i) c' (w_p γ)`, times `w ^ 2`, the number of cosets of
`F.congruenceSubgroup` in `Z` and the squared volume of `F.congruenceSubgroup`, add up to at most
`F.headSumNormSq` at `g⁻¹`, where `g = S.toPlaces T (S.translateByClassReps c c' γ)` for
`γ ∈ floorGroup 𝔰.ϱ` whose translate is integral off `T`: the pairings of the orbital integrals
`F.scaledOrbitalIntegral` at `T` of two heads, summed against `R`. -/
lemma IsFillingData.sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq [WeilData E]
    (hF : S.IsFillingData T F) {side : FullOrCut} {Z : F.IntermediateGroup}
    {ι J : Type} [Fintype ι] [Fintype J] {c c' : S.Classes} {γ : S.G E} (hγ : γ ∈ floorGroup 𝔰.ϱ)
    {n : ι → S.latticeStabilizer} (h_inj : (fun i : ι ↦ S.reduction (n i)).Injective)
    (hn : ∀ i : ι, S.toPlaces T (n i) ∈ Z.val) {a : J → ℕ → Eˣ} {ρ : J → ℝ} {w : ℝ}
    (h_weight : ∀ p : J,
      ρ p * (F.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ a p) 1).toReal = w)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' γ))
    (h_head : ∀ p : J, ∀ l < 𝔰.ϱ,
      (a p l : E) ∈ ratIntegralOff T ∧ ((a p l)⁻¹ : Eˣ).val ∈ ratIntegralOff T) :
    let R : Matrix J J ℂ := .gram ℂ fun p : J ↦ ρ p • besselOrbitalIntegral volume
      (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
      (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ))
    F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets *
        ∑ i : ι, ENNReal.ofReal (w ^ 2 * ‖∑ p : J, S.cosetAmplitude side c (S.reduction (n i)) c'
          (weylElem 𝔰.ϱ (a p) * γ)‖ ^ 2) ≤
      ENNReal.ofReal (F.headSumNormSq Z R (fun p : J ↦ Units.map (ratToPlaces T) ∘ a p)
        (S.toPlaces T (S.translateByClassReps c c' γ))⁻¹).re := by
  classical
  -- The entry `(b, A i b)` of the sum over the heads, with `A i b` the coset of `(n i)⁻¹ * b`, is,
  -- up to a constant, the squared norm of the class sum at the reduction of `n i`; these entries
  -- are distinct.
  intro R
  have h_coset (i : ι) (b : Z.Cosets) : ∃ b' : Z.Cosets,
      (S.toPlaces T (n i))⁻¹ * b.out.1 * b'.out.1⁻¹ ∈ F.congruenceSubgroup :=
    (Z.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq (mul_mem (inv_mem (hn i)) b.out.2)).imp
      fun b' hb' ↦ (hb' b').2 rfl
  choose A hA using h_coset
  let v (x : Z.Cosets × Z.Cosets) (p : J) : ℂ :=
    F.scaledOrbitalIntegral Z (Units.map (ratToPlaces T) ∘ a p)
    (S.toPlaces T (S.translateByClassReps c c' γ))⁻¹ x
  have h_nonneg (x : Z.Cosets × Z.Cosets) : 0 ≤ (star (v x) ⬝ᵥ R *ᵥ v x).re :=
    (Complex.nonneg_iff.1 (PosSemidef.dotProduct_mulVec_nonneg (posSemidef_gram ..) (v x))).1
  have h_entry (i : ι) (b : Z.Cosets) : .ofReal (star (v (b, A i b)) ⬝ᵥ R *ᵥ v (b, A i b)).re =
      F.groupMeasure F.congruenceSubgroup ^ 2 * .ofReal (w ^ 2 * ‖∑ p, S.cosetAmplitude side c
        (S.reduction (n i)) c' (weylElem 𝔰.ϱ (a p) * γ)‖ ^ 2) := by
    -- by unfolding, the tensor behind the entry is `w` times the mass of `K(M)` times the class sum
    have h_tensor : ∑ p, v (b, A i b) p • (ρ p • besselOrbitalIntegral volume
          (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
          (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ))) =
        w • F.groupMeasure.real F.congruenceSubgroup • ∑ p, S.cosetAmplitude side c
          (S.reduction (n i)) c' (weylElem 𝔰.ϱ (a p) * γ) := by
      simp only [v, smul_comm (M := ℂ) (N := ℝ),
        hF.scaledOrbitalIntegral_smul_eq_cosetAmplitude hγ (fun l ↦ (h_head _ l l.2).2)
          (isIntegralOff_weylElem_mul (h_head _) h_off) (hA i b),
        smul_smul (ρ _), h_weight, ← smul_sum]
    simp only [R, star_dotProduct_gram_mulVec, h_tensor]
    simp (disch := positivity) [norm_smul, ← Complex.ofReal_pow, mul_pow, Measure.real,
      ofReal_toReal (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)]
    ring
  have h_distinct : (fun θ : ι × Z.Cosets ↦ (θ.2, A θ.1 θ.2)).Injective := by
    rintro ⟨i, b⟩ ⟨k, _⟩ h_eq
    obtain ⟨rfl, hAb⟩ := Prod.mk.inj h_eq
    have h_red : S.reduction (n i) = S.reduction (n k) :=
      (hF.reduction_eq_iff ..).2 (by simpa [hAb] using div_mem (hA i b) (hA k b))
    rw [h_inj h_red]
  calc
    _ = ∑ θ : ι × Z.Cosets, .ofReal (star (v (θ.2, A θ.1 θ.2)) ⬝ᵥ R *ᵥ v (θ.2, A θ.1 θ.2)).re := by
      simp only [sum_prod_type, h_entry, sum_const, card_univ, nsmul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ ∑ x, .ofReal (star (v x) ⬝ᵥ R *ᵥ v x).re := by
      rw [← sum_image (f := fun x ↦ ENNReal.ofReal (star (v x) ⬝ᵥ R *ᵥ v x).re) h_distinct.injOn]
      exact sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := by
      rw [PlaceData.headSumNormSq_eq_sum, Complex.re_sum, ofReal_sum_of_nonneg fun x _ ↦ h_nonneg x]

/-- The terms over one point `e`. Let the inverse of the level `M = S.ideleM` be integral off `T`,
and let `F` be a filling datum at `T`. Let `Z` be a group between the congruence group
`F.congruenceSubgroup` and the integral isometries at `T`. The heads `a p` (`p : J`) are sequences
in `Eˣ`, with Weyl elements `w_p = weylElem 𝔰.ϱ (a p)` and entries below `ϱ` that are units off `T`;
`F.headDensity` is a product of powers of the moduli of these entries at `T`. Let
`W = S.besselFn side` be the Bessel function at the infinite places or its cut, as `side` says. Let
the triples `(c' i, S.reduction (n i), γ i)`, `i : ι`, be distinct, with `γ i` rational and fixing
the `ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`) and `n i` in `Z` at `T`. Let the translates
`h_c⁻¹ γ h_c'` by the class representatives be integral off `T` and send the last frame vector `z`
to `e` at `T` (`orbitPoint 𝔰.top g = g⁻¹ z`). Let the left class `c i`, the product `⟨z, γ i z⟩` and
the `X₀`-part of `γ i z` be the same for all `i`. Let `ρ p` times the head density be `w`. Let `R`
be positive semidefinite and, for every `i`, the Gram matrix of the tensors
`ρ p • ∫ W(y) ⊗ W((w_p γ i)⁻¹ y)^* dy`. Then the squared norms of the sums over `p` of
`S.cosetAmplitude` at `w_p γ i`, times `w ^ 2`, the `F.measureH`-mass and the squared
`F.groupMeasure`-mass of `F.congruenceSubgroup` and the number of its cosets in `Z`, add up to at
most the real part of `∑ p q, R p q * F.fiberPairing Z (ω p) (ω q) e`. Here `ω p` is `a p` read at
`T`, the fiber pairing is the pairing of the orbital integrals of two heads integrated over
`besselH`, and `S.cosetAmplitude side c s c' γ` is the sum of the amplitudes of the rational
`u γ u'⁻¹`, with `u`, `u'` unipotent, whose translate by the class representatives is integral with
reduction `s`. -/
lemma IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing [WeilData E]
    (hF : S.IsFillingData T F) {side : FullOrCut}
    {Z : F.IntermediateGroup} {ι J : Type} [Fintype ι] [Fintype J] {c c' : ι → S.Classes}
    {γ : ι → S.G E} {n : ι → S.latticeStabilizer}
    (h_inj : (fun i : ι ↦ (c' i, S.reduction (n i), γ i)).Injective)
    (h_leftClass : ∀ i k : ι, c i = c k)
    (hγ : ∀ i : ι, γ i ∈ floorGroup 𝔰.ϱ)
    (h_tail : ∀ i k : ι, S.frameProducts (γ i) 𝔰.top 𝔰.top = S.frameProducts (γ k) 𝔰.top 𝔰.top)
    (h_col : ∀ (i k : ι) (l : 𝔰.κ),
      (γ i).val.val (𝔰.indexX₀ l) 𝔰.z = (γ k).val.val (𝔰.indexX₀ l) 𝔰.z)
    (hn : ∀ i : ι, S.toPlaces T (n i) ∈ Z.val)
    (h_off : ∀ i : ι, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (γ i)))
    {e : 𝔰.BesselIndex → LocProd T}
    (he : ∀ i : ι, orbitPoint 𝔰.top (S.toPlaces T (S.translateByClassReps (c i) (c' i) (γ i)))⁻¹ =
      e)
    {a : J → ℕ → Eˣ} {R : Matrix J J ℂ} (R_psd : R.PosSemidef) {ρ : J → ℝ} {w : ℝ}
    (hR : ∀ i : ι, R = .gram ℂ fun p : J ↦ ρ p • besselOrbitalIntegral volume
      (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
      (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ i)))
    (h_weight : ∀ p : J, ρ p * (F.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ a p) 1).toReal = w)
    (h_head : ∀ p : J, ∀ l < 𝔰.ϱ,
      (a p l : E) ∈ ratIntegralOff T ∧ ((a p l)⁻¹ : Eˣ).val ∈ ratIntegralOff T) :
    let ω (p : J) : ℕ → (LocProd T)ˣ := Units.map (ratToPlaces T) ∘ a p
    F.measureH F.congruenceSubgroup * (F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets) *
        ∑ i : ι, .ofReal (w ^ 2 * ‖∑ p : J, S.cosetAmplitude side (c i) (S.reduction (n i)) (c' i)
          (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2) ≤
      .ofReal (∑ p : J, ∑ q : J, R p q * F.fiberPairing Z (ω p) (ω q) e).re := by
  classical
  -- Group the classes by the pair of the right class and the rational element, and bound each
  -- group by `sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq`. Different pairs have positions in
  -- different cosets of `F.congruenceSubgroup`.
  intro ω
  obtain _ | ⟨⟨i₀⟩⟩ := isEmpty_or_nonempty ι
  · simp [Finset.univ_eq_empty (α := ι)]
  obtain ⟨c₀, rfl⟩ : ∃ c₀, c = fun _ ↦ c₀ := ⟨c i₀, funext (h_leftClass · i₀)⟩
  let pair (i : ι) : S.Classes × S.G E := (c' i, γ i)
  let pos (x : Set.range pair) : (S.latticeMiddle (LocProd T)).G :=
    (S.toPlaces T (S.translateByClassReps c₀ x.1.1 x.1.2))⁻¹
  have h_point (x : Set.range pair) :
      pos x ∈ floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top (pos x) = e := by
    obtain ⟨_, i, rfl⟩ := x
    exact ⟨inv_mem (.map_mem_agreeWithOneOn _
      (translateByClassReps_mem_floorGroup (hγ i) c₀ (c' i))),
      he i⟩
  have h_sep (x x' : Set.range pair) (hK : pos x * (pos x')⁻¹ ∈ F.congruenceSubgroup) : x = x' := by
    obtain ⟨_, i, rfl⟩ := x
    obtain ⟨_, k, rfl⟩ := x'
    exact Subtype.ext (Prod.ext_iff.2 (hF.classes_eq_and_eq_of_inv_mul_mem_congruenceSubgroup rfl
      (hγ i) (hγ k)
      (h_tail i k) (h_col i k) (h_off i) (h_off k) (by simpa [pos, pair] using hK)))
  refine .trans ?_ (sum_headSumNormSq_le_fiberPairing Z R_psd ω h_point h_sep)
  rw [mul_assoc, ← Finset.sum_fiberwise univ (Set.rangeFactorization pair), mul_sum]
  gcongr with x
  obtain ⟨_, k, rfl⟩ := x
  have h_same (i : {i // pair i = pair k}) : c' i = c' k ∧ γ i = γ k := Prod.mk.inj i.2
  have h_inj_fiber : (fun i : {i // pair i = pair k} ↦ S.reduction (n i)).Injective :=
    fun i i' h ↦ Subtype.ext (h_inj (by simp [h_same i, h_same i', h]))
  rw [hR k]
  refine .trans (le_of_eq ?_) (hF.sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq (hγ k)
    h_inj_fiber (fun i ↦ hn i) h_weight (h_off k) h_head)
  rw [sum_subtype (F := inferInstance) (p := (pair · = pair k)) _ (by simp [Subtype.ext_iff])]
  simp only [h_same, pair]

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)]
  [IntegralPlace (LocProd T)] in
/-- The space has the hyperbolic pairs `e_a, e*_a` (`a < ϱ`), a definite part `X₀` with basis `𝔰.κ`
and a vector `z`; `floorGroup 𝔰.ϱ` is the group of isometries that fix the hyperbolic pairs. Let `γ`
be an element of this group over `E` with `⟨z, γ z⟩ = t`, and `x` the `X₀`-part of `γ z`, moved by
the inverse of the representative of the class `c`. Then at `T` the translate `h_c⁻¹ γ h_c'` sends
`z` to `vectorOfLastEntry S.piN t x = x - N⁻¹ t z`, written in the lattice basis. -/
lemma orbitPoint_toPlaces_translateByClassReps {c c' : S.Classes} {γ : S.G E}
    (hγ : γ ∈ floorGroup 𝔰.ϱ) {t : E} (h_tail : S.frameProducts γ 𝔰.top 𝔰.top = t) :
    orbitPoint 𝔰.top (S.toPlaces T (S.translateByClassReps c c' γ))⁻¹ =
      evalPlaces T ∘ vectorOfLastEntry S.piN (algebraMap E (𝔸f E) t)
        (c.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ fun l : 𝔰.κ ↦ γ.val.val (𝔰.indexX₀ l) 𝔰.z) := by
  rw [← h_tail, ← orbitPoint_top_translateByClassReps_inv hγ c c']
  have h_map : (S.toPlaces T (S.translateByClassReps c c' γ)).val.val =
      (S.translateByClassReps c c' γ).val.val.map (evalPlaces T) := rfl
  ext l
  simp [orbitPoint, h_map]

end Level

variable [WeilData E]

/-- Siegel's formula as an upper bound. Let `S` be admissible, with the inverse of the level
`M = S.ideleM` integral off `T`, let `N⁻¹` be integral off `T`, where `N = S.N`, and let `F` be a
filling datum at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose
character is that of `S`. Let `Ψ ≥ 0` be a function of compact support on the vectors over the
product `LocProd T` of the completions at `T`, invariant under small translations and under the
elements of `F.congruenceSubgroup` that fix all basis vectors outside the definite part `X₀`
(`besselH`). Let `|t|_v > N` under all embeddings `Φ v` of the CM type. For a pair `z = (class, v)`
let `x` be the rational vector `v` of `X₀` moved by the inverse of the representative of the class.
If the pairs in a finite set `s` have `N (v* v) = t t̄ - N²` and `x` integral off `T`, then the
values of `Ψ` at `vectorOfLastEntry S.piN t x` (`x` minus `N⁻¹ t` times the last frame vector) add
up to at most the product of `1 + S.b⁻⁶`, the number of classes, `S.siegelConst = (π^k / ((k - 1)!
N^k))^f |disc E|^(1/4) (volÔ E)^k`, `(∏ v, (|t|_v² - N²)) ^ (k - 1)`, the inverse modulus of
`S.piNAt T` (a unit of norm `N`) and the integral of `Ψ ∘ vectorOfLastEntry` over the sphere
`y* y = (t t̄ - N²) / N`, for the fiber measure `P.normFiberMeasure` with index
`lastEntrySphereIndex`. Here `S.b` is the size parameter of `S`, `k` the rank of `X₀` and `f` the
number of infinite places. -/
theorem IsFillingData.siegel_sum_le_lintegral_sphere (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) {Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0}
    (Ψ_supp : HasCompactSupport Ψ)
    (Ψ_unif : ∀ᶠ v : 𝔰.BesselIndex → LocProd T in 𝓝 0,
      ∀ x : 𝔰.BesselIndex → LocProd T, Ψ (x + v) = Ψ x)
    (Ψ_inv : ∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → LocProd T,
      Ψ (k.val.val *ᵥ x) = Ψ x)
    {s : Finset (S.Classes × (𝔰.κ → E))} {t : E}
    (ht : ∀ v : InfinitePlace E, S.N ^ 2 < ‖Φ v t‖ ^ 2)
    (h_norm : ∀ z ∈ s, S.N * star z.2 ⬝ᵥ z.2 = t * star t - S.N ^ 2)
    (h_int : ∀ z ∈ s, ∀ i : 𝔰.κ,
      (z.1.out⁻¹.1.1 *ᵥ algebraMap E (𝔸f E) ∘ z.2) i ∈ integralOff T) :
    (∑ z ∈ s, Ψ (evalPlaces T ∘
        vectorOfLastEntry S.piN t (z.1.out⁻¹.1.1 *ᵥ algebraMap E (𝔸f E) ∘ z.2)) : ℝ≥0∞) ≤
      .ofReal ((1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst *
          (∏ v : InfinitePlace E, (‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) *
        ((P.modulus (S.piNAt T))⁻¹ *
          ∫⁻ y : 𝔰.κ → LocProd T, Ψ (vectorOfLastEntry (S.piNAt T) (ratToPlaces T t) y)
          ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex (S.piNAt T) (ratToPlaces T t))) := by
  -- Apply `classSum_eq_mul_normDensity` at the norm `β = (t t̄ - N²) / N` to the test function `f`
  -- that is `Ψ` at `T` and the indicator of the integral vectors off `T`; bound the density by
  -- `enorm_normDensity_le_mul_lintegral_normFiberMeasure`.
  classical
  have hN₀ : 0 < S.N := S.N_prime.pos
  have h_rank : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
  set β : E := (t * star t - S.N ^ 2) / S.N
  set π : (LocProd T)ˣ := S.piNAt T
  let t' : LocProd T := evalPlaces T t
  have hβ : star β = β := by simp [β, field]
  have hβ_pos (v : InfinitePlace E) : 0 < (Φ v β).re := by simpa [β, mul_conj', sq, hN₀] using ht v
  have h_level : P.skewUnit⁻¹.1 * lastEntrySphereIndex π t' = evalPlaces T β :=
    skewUnit_inv_mul_lastEntrySphereIndex_piNAt t
  have Ψ_lc : IsLocallyConstant Ψ := isLocallyConstant_of_eventually_add Ψ_unif
  -- the integral vectors off `T` form a clopen set
  let L : OpenAddSubgroup (𝔰.κ → 𝔸f E) :=
    ⟨(intVectors (integralOff T) 𝔰.κ).toAddSubgroup, isOpen_intVectors (isOpen_integralOff T)⟩
  let f : LocallyConstant (𝔰.κ → 𝔸f E) ℝ≥0 :=
    .indicator ⟨fun y ↦ Ψ (vectorOfLastEntry π t' (evalPlaces T ∘ y)),
      Ψ_lc.comp_continuous (by fun_prop)⟩
      (isClopen L)
  let C : ℂ := (classSum stdRatPoints S.sourceLevel 1 * √√|NumberField.discr E| *
    ∏ v : InfinitePlace E, Real.pi ^ card 𝔰.κ / (card 𝔰.κ - 1).factorial *
      (Φ v β).re ^ (card 𝔰.κ - 1) : ℝ)
  obtain ⟨h_summable, (h_siegel : ((classSum stdRatPoints S.sourceLevel fun h : Gf E 𝔰.κ ↦
      ((∑' v : 𝔰.κ → E, if star v ⬝ᵥ v = β then f (h⁻¹.1.1 *ᵥ fun i ↦ (v i : 𝔸f E)) else 0 :
        ℝ≥0) : ℝ) : ℝ) : ℂ) = C * normDensity f β)⟩ :=
    classSum_eq_mul_normDensity (by lia) S.sourceLevel f
      (fun k hk ↦ hF.testFunction_mulVec Ψ_inv t hk)
      (hasCompactSupport_testFunction Ψ_supp π t') hβ hβ_pos
  set I : ℝ≥0∞ := ∫⁻ y, (Ψ (vectorOfLastEntry π (ratToPlaces T t) y) : ℝ≥0∞)
    ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π (ratToPlaces T t))
  calc
    _ ≤ ‖C * normDensity f β‖ₑ := by
      -- each pair `z ∈ s` has norm `β` and is integral off `T`, so it is a term of the class sum
      rw [← h_siegel]
      simp_rw [classSum_sourceLevel_eq_sum, ← NNReal.coe_sum, enorm_eq_nnnorm, nnnorm_real,
        nnnorm_eq, ofNNReal_finsetSum, ENNReal.coe_tsum (h_summable _)]
      grw [← ENNReal.tsum_prod.trans (tsum_fintype _), ← ENNReal.sum_le_tsum s]
      gcongr with z hz
      have h_norm_eq : star z.2 ⬝ᵥ z.2 = β := by simp [β, ← h_norm z hz, Nat.Prime.ne_zero]
      grw [ite_eq_left h_norm_eq, ← vectorOfLastEntry_evalPlaces]
      exact (ite_eq_left (h_int z hz)).ge
    _ ≤ ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k * I) := by
      rw [enorm_mul]
      gcongr
      exact hF.enorm_normDensity_le_mul_lintegral_normFiberMeasure
        (Ψ_lc.continuous.comp isClosedEmbedding_vectorOfLastEntry.continuous)
        (Ψ_supp.comp_isClosedEmbedding isClosedEmbedding_vectorOfLastEntry)
        (by rw [star_algebraMap_finAdele, hβ]) h_level
    _ = ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k) * P.modulus π * ((P.modulus π)⁻¹ * I) := by
      rw [mul_assoc _ (P.modulus π), ENNReal.mul_inv_cancel_left (by simp) (by simp), ← mul_assoc]
    _ = _ := by rw [siegel_constant_eq hT_N piNAt_mul_star hβ_pos (C := C) rfl]

omit [WeilData E] [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- If the lattice basis and the translate `h_c⁻¹ γ h_c'` (`S.translateByClassReps`) of a rational
element `γ` of `floorGroup 𝔰.ϱ` are integral off `T`, then so is the `X₀`-part of the column of `γ`
at `z`, moved by the inverse of the representative of `c`. -/
lemma x₀Part_mem_integralOff (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    [_P : IntegralPlace (LocProd T)] {c c' : S.Classes} {γ : S.G E} (hγ : γ ∈ floorGroup 𝔰.ϱ)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' γ)) (i : 𝔰.κ) :
    (c.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ fun l : 𝔰.κ ↦ γ.val.val (𝔰.indexX₀ l) 𝔰.z) i ∈
      integralOff T := by
  have column : orbitPoint 𝔰.top (S.translateByClassReps c c' γ)⁻¹ ∈
      intVectors (integralOff T) 𝔰.BesselIndex :=
    fun l ↦ by simpa [orbitPoint] using h_off.isIntMatrix l 𝔰.z
  rw [orbitPoint_top_translateByClassReps_inv hγ] at column
  exact (mulVec_mem_intVectors_iff (inv_mem hT_basis)).1 column (𝔰.indexX₀ i)

/-- Siegel's step, for one last entry `t`. Let `S` be admissible, with the inverse of the level
`M = S.ideleM` integral off `T`, let `N⁻¹` and the lattice basis be integral off `T`, and let `F` be
a filling datum at `T`. Let `Z` be a group between the congruence group `F.congruenceSubgroup` and
the integral isometries at `T`. The heads `a p` (`p : J`) are sequences in `Eˣ`, with Weyl elements
`w_p = weylElem 𝔰.ϱ (a p)` and entries below `ϱ` that are units off `T`; `F.headDensity` is a
product of powers of the moduli of these entries at `T`. Let `W = S.besselFn side` be the Bessel
function at the infinite places or its cut, as `side` says. Let the terms
`(c i, c' i, S.reduction (n i), γ i)`, `i : j`, be distinct, with `γ i` rational, fixing the `ϱ`
hyperbolic pairs (`floorGroup 𝔰.ϱ`) and with `⟨z, γ i z⟩ = t`, translates by the class
representatives integral off `T` and `n i` in `Z` at `T`; there is at least one term, `i₀`. Let
`N < ‖t‖` at all infinite places, and let the heads have entry `t` at `ϱ`. Assume that `R` is, for
every `i`, the Gram matrix of the tensors `ρ p • ∫ W(y) ⊗ W((w_p γ i)⁻¹ y)^* dy`
(`besselOrbitalIntegral`), and that `ρ p` times the head density is `r * √G`, where
`G = (∏ v, (‖t‖_v² - N²)) ^ (k - 1)`. Then the squared norms of the sums over `p` of
`S.cosetAmplitude` at `w_p γ i`, times `r ^ 2`, add up to at most
`(1 + S.b⁻⁶) * S.scaledSiegelConst` times the real part of
`∑ p q, R p q * F.lastEntryDensity / Z.massRatio`. -/
theorem IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity
    (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) {side : FullOrCut} {Z : F.IntermediateGroup}
    {j J : Type} [Fintype j] [Fintype J] {c c' : j → S.Classes} {γ : j → S.G E}
    {n : j → S.latticeStabilizer} {t : Eˣ}
    (h_inj : (fun i : j ↦ (c i, c' i, S.reduction (n i), γ i)).Injective)
    (hγ : ∀ i : j, γ i ∈ floorGroup 𝔰.ϱ) (h_tail : ∀ i : j, S.frameProducts (γ i) 𝔰.top 𝔰.top = t)
    (ht : ∀ v : InfinitePlace E, S.N ^ 2 < ‖Φ v (t : E)‖ ^ 2)
    (hn : ∀ i : j, S.toPlaces T (n i) ∈ Z.val)
    (h_off : ∀ i : j, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (γ i))) (i₀ : j)
    {a : J → ℕ → Eˣ} (h_last : ∀ p : J, a p 𝔰.ϱ = t)
    (h_head : ∀ p : J, ∀ l < 𝔰.ϱ,
      (a p l : E) ∈ ratIntegralOff T ∧ ((a p l)⁻¹ : Eˣ).val ∈ ratIntegralOff T)
    {R : Matrix J J ℂ} {ρ : J → ℝ} {r : ℝ}
    (hR : ∀ i : j, R = .gram ℂ fun p : J ↦ ρ p • besselOrbitalIntegral volume
      (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
      (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ i)))
    (h_weight : ∀ p : J, ρ p * (F.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ a p) 1).toReal =
      r * √((∏ v : InfinitePlace E, (‖Φ v (t : E)‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1))) :
    ∑ i : j, r ^ 2 * ‖∑ p : J, S.cosetAmplitude side (c i) (S.reduction (n i)) (c' i)
        (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2 ≤
      (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst * (∑ p : J, ∑ q : J, R p q *
        (F.lastEntryDensity (S.piNAt T) Z (Units.map (ratToPlaces T) ∘ a p)
          (Units.map (ratToPlaces T) ∘ a q) / Z.massRatio.toReal)).re := by
  classical
  -- Group the classes by the point `g i` of Siegel's sum (the class and the `X₀`-part of `γ i z`).
  -- Over one point they are bounded by the value of a step function `Ψ`; Siegel's formula sums
  -- over the points, and the integral of `Ψ` over the sphere of `t`, divided by the modulus of
  -- `S.piNAt T`, is the real part of the sum `Q` of densities.
  let ω (p : J) : ℕ → (LocProd T)ˣ := Units.map (ratToPlaces T) ∘ a p
  let y (i : j) : ℝ := r ^ 2 * ‖∑ p : J, S.cosetAmplitude side (c i) (S.reduction (n i)) (c' i)
    (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2
  set G : ℝ := (∏ v : InfinitePlace E, (‖Φ v t.1‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)
  let g (i : j) : S.Classes × (𝔰.κ → E) := (c i, fun l ↦ (γ i).1.1 (𝔰.indexX₀ l) 𝔰.z)
  let x (z : S.Classes × (𝔰.κ → E)) : 𝔰.κ → 𝔸f E := z.1.out⁻¹.1.1 *ᵥ algebraMap E (𝔸f E) ∘ z.2
  let Q : ℂ := ∑ p, ∑ q, R p q * F.lastEntryDensity (S.piNAt T) Z (ω p) (ω q)
  have R_psd : R.PosSemidef := by simpa only [hR i₀] using posSemidef_gram ℂ _
  have G_pos : 0 < G := by simp [G, ht, prod_pos]
  -- The translate of a term by the class representatives moves `z` to the vector with last entry
  -- `t` over `g i`, which has norm `(t t̄ - N²) / N` and is integral off `T`.
  have norm_eq (i : j) : S.N * star (g i).2 ⬝ᵥ (g i).2 = t.1 * star t.1 - S.N ^ 2 := by
    rw [← h_tail i]
    exact mul_star_dotProduct_eq_last_frameProducts (hγ i)
  have x_int (i : j) : ∀ l : 𝔰.κ, x (g i) l ∈ integralOff T :=
    x₀Part_mem_integralOff hT_basis (hγ i) (h_off i)
  have point_eq (i : j) : orbitPoint 𝔰.top
    (S.toPlaces T (S.translateByClassReps (c i) (c' i) (γ i)))⁻¹ =
      evalPlaces T ∘ vectorOfLastEntry S.piN t.1 (x (g i)) :=
    orbitPoint_toPlaces_translateByClassReps (hγ i) (h_tail i)
  -- Extend the real part of the sum of the fiber pairings against `R` to a step function `Ψ`; its
  -- value at a point bounds the classes there.
  obtain ⟨Ψ, Ψ_supp, Ψ_unif, Ψ_inv, Ψ_eq : ∀ e ∈ lastVectorQuadric (S.latticeMiddle (LocProd T)),
      Ψ e = ENNReal.ofReal (∑ p, ∑ q, R p q * F.fiberPairing Z (ω p) (ω q) e).re⟩ :=
    hF.exists_step_sum_fiberPairing Z R ω
  obtain ⟨D, hD : 0 < D, h_const : S.scaledSiegelConst = D * card S.Classes * S.siegelConst,
      h_unit : Z.massRatio ≤ F.measureH F.congruenceSubgroup *
        (F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets) * .ofReal D⟩ :=
    hF.exists_scaledSiegelConst_eq_and_massRatio_le Z
  have le_Ψ (k₀ : j) :
      .ofReal G * (Z.massRatio / .ofReal D) * ∑ k with g k = g k₀, .ofReal (y k) ≤
        (Ψ (evalPlaces T ∘ vectorOfLastEntry S.piN t.1 (x (g k₀))) : ℝ≥0∞) := by
    have same (k k' : {k // g k = g k₀}) :
        c k = c k' ∧ (g k).2 = (g k').2 := Prod.mk.inj (k.2.trans k'.2.symm)
    have point_mem : evalPlaces T ∘ vectorOfLastEntry S.piN t.1 (x (g k₀)) ∈
        lastVectorQuadric (S.latticeMiddle (LocProd T)) := by
      rw [← point_eq]
      exact orbitPoint_mem_lastVectorQuadric (inv_mem (.map_mem_agreeWithOneOn _
        (translateByClassReps_mem_floorGroup (hγ k₀) (c k₀) (c' k₀))))
    have h_scale (k : j) : ENNReal.ofReal G * .ofReal (y k) =
        .ofReal ((r * √G) ^ 2 * ‖∑ p, S.cosetAmplitude side (c k) (S.reduction (n k)) (c' k)
          (weylElem 𝔰.ϱ (a p) * γ k)‖ ^ 2) := by
      rw [← ENNReal.ofReal_mul G_pos.le, mul_pow, Real.sq_sqrt G_pos.le, mul_left_comm, mul_assoc]
    suffices h_over : F.measureH F.congruenceSubgroup *
      (F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets) *
        ∑ k : {k // g k = g k₀}, ENNReal.ofReal G * .ofReal (y k) ≤
          Ψ (evalPlaces T ∘ vectorOfLastEntry S.piN t.1 (x (g k₀))) by
      grw [div_le_of_le_mul h_unit, mul_comm (ENNReal.ofReal G), mul_assoc _ (ENNReal.ofReal G),
        mul_sum, sum_subtype (F := inferInstance) (p := fun k ↦ g k = g k₀) _ mem_filter_univ,
        h_over]
    simp only [h_scale, Ψ_eq _ point_mem]
    exact hF.mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing (ι := {k // g k = g k₀})
      (fun k k' h ↦ Subtype.ext (h_inj (Prod.ext (same k k').1 h))) (fun k k' ↦ (same k k').1)
      (fun k ↦ hγ k) (fun k k' ↦ by simp only [h_tail])
      (fun k k' ↦ congrFun (same k k').2) (fun k ↦ hn k) (fun k ↦ h_off k)
      (fun k ↦ by rw [point_eq, k.2]) R_psd (fun k ↦ hR k) h_weight h_head
  -- Siegel's formula sums over the points; the normalized integral over the sphere is `Q.re`.
  obtain ⟨⟨re_nonneg : 0 ≤ Q.re, -⟩, h_sphere⟩ :=
    sum_lastEntryDensity_nonneg_and_eq_inv_mul_lintegral Z piNAt_mul_star
    R_psd ω (t := t.map (ratToPlaces T)) fun p ↦ by simp [ω, h_last]
  have h_total : .ofReal G * (Z.massRatio / .ofReal D) * ∑ k, .ofReal (y k) ≤
      .ofReal ((1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst * G) * ENNReal.ofReal Q.re := by
    calc
      _ ≤ ∑ z ∈ univ.image g, (Ψ (evalPlaces T ∘ vectorOfLastEntry S.piN t.1 (x z)) : ℝ≥0∞) := by
        rw [← sum_fiberwise_of_maps_to fun k _ ↦ mem_image_of_mem g (mem_univ k), mul_sum]
        exact sum_le_sum (forall_mem_image.2 fun k _ ↦ le_Ψ k)
      _ ≤ _ := hF.siegel_sum_le_lintegral_sphere hT_N Ψ_supp Ψ_unif Ψ_inv ht
        (forall_mem_image.2 fun k _ ↦ norm_eq k)
        (forall_mem_image.2 fun k _ ↦ x_int k)
      _ = _ := by
        -- almost every point of the sphere lies on the top quadric, where `Ψ_eq` gives `Ψ`
        rw [h_sphere, lintegral_congr_ae
          ((P.ae_vectorOfLastEntry_mem_lastVectorQuadric piNAt_mul_star hF.two_le_card _).mono
            fun _ ↦ Ψ_eq _)]
        rfl
  -- pass to real numbers and cancel the constants
  have unit_pos : 0 < Z.massRatio.toReal := (massRatio_ne_zero_and_ne_top Z).elim toReal_pos
  have h_real : G * (Z.massRatio.toReal / D) * ∑ i, y i ≤
      (1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst * G * Q.re := by
    simpa (disch := finiteness) only [toReal_sum, toReal_mul, toReal_ofReal, toReal_div,
      siegelConst] using toReal_mono (by finiteness) h_total
  have h_re : (∑ p, ∑ q, R p q *
      (F.lastEntryDensity (S.piNAt T) Z (ω p) (ω q) / Z.massRatio.toReal)).re =
        Q.re / Z.massRatio.toReal := by
    simp [Q, ← mul_div_assoc, ← Finset.sum_div]
  refine le_of_mul_le_mul_left (h_real.trans_eq ?_) (by positivity)
  rw [h_re, h_const]
  field

end New.Filling
