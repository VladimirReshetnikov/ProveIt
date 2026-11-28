import New.Spanning.Bessel.Orthonormality
import New.Spanning.Unfolding.CutoffIntegral

/-!
# Sums of amplitudes over blocks

This file proves convergence, change of weight and the behaviour under the Bessel subgroup of the
block sums `S.amplitudeSum side T c s c'`. The block is the sum, over the rational `γ ∈ T` that lie
over `(c, s, c')` (`New.Filling.termsOver`), of the amplitudes
`∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy`. Here `β_c = S.classCutoff c` is a cutoff for the group
`S.classUnipotent c`, the argument `side : FullOrCut` selects the full or the cut Bessel function
`W`, and `ν = New.Filling.unipotentCovolume`. The listed results assume that `S` is admissible
(`New.Filling.IsAdmissible`).

## Main definitions and results

* `New.Filling.exists_tsum_classCutoff_mul_prod_enorm_le`,
  `New.Filling.tsum_amplitudeMajorant_lt_top`,
  `New.Filling.tsum_lintegral_enorm_besselKernel_sub_cut_le`: the sums are bounded and converge
  absolutely, and cutting `W` changes them little.
* `New.Filling.hasSum_amplitudeSum_of_cutoff`: for stable `T`, any measurable weight with orbit sums
  `1` may replace the product of the cutoffs `S.classCutoff c` and `S.classCutoff c'`.
* `New.Filling.amplitudeSum_mul_mul_inv`, `New.Filling.amplitudeSum_besselU_mul`: moving a block by
  the Bessel subgroup; the unipotent part acts through the character `New.Filling.unipotentChar`.
* `New.Filling.amplitudeSum_eq_zero_of_not_agrees`: the block of a stable set vanishes unless `s`
  agrees.
* `New.Filling.amplitudeSum_besselS_one_eq_ite`: for the full Bessel function only, at `s = 1` the
  Bessel subgroup contributes `S.unipotentCovolume` times the identity if `c = c'`, and `0`
  otherwise.

Notions from other files:
* `New.Filling.latticeStabilizer`, `New.Filling.reduction`, `New.Filling.ResidueGL`: the group K of
  integral elements of the finite adelic unitary group, and its reduction modulo the chosen places
  above p₀ and p₁, with values in the product `ResidueGL` of the general linear groups over the
  residue fields. The kernel is K(M) = `New.Filling.principalLevel`.
* `New.Filling.termsOver`: a rational `γ` is a term over `(c, s, c')` if h_c⁻¹ γ h_c' lies in K and
  has reduction `s`; here h_c = `S.classRep c` represents the class `c`.
* `New.Shape.Form.besselU`, `New.Shape.Form.besselS`, `New.Filling.IsStable`: the group 𝖴 of block
  upper unitriangular isometries, and the Bessel subgroup, which 𝖴 generates together with the
  unitary group of the standard form on κ; a set `T` of rational elements is stable if
  multiplication on either side by rational points of 𝖴 does not affect membership in `T`.
* `New.Filling.IsAdmissible`: the standing hypotheses. The level `sourceLevel` is the preimage of
  K(M), `reduction` is onto, and size inequalities hold between b, M and ϖ, κ_v, N, the second
  moments, the number of Bessel coordinates, an index and the constant `scaledSiegelConst`.
* `New.Filling.classUnipotent`, `New.Filling.unipotentCovolume`: the rational points u of 𝖴 with
  h_c⁻¹ u h_c in the principal congruence subgroup K(M); an explicit positive number built from M,
  N, |κ|, ϱ, the discriminant of E and the scales of the frame at the infinite places.

## Relation to the literature

The results on block sums belong to two steps: the bound for the second moment of the Poincaré
series (`New.Spanning.Unfolding.Moments`, which lists related work) and the bound for degenerate
terms and pairs with different links (`New.Spanning.RemainingTerms.Sum`).
-/

section AmplitudeSums

open NumberField MeasureTheory Measure Complex ENNReal Finset Fintype

namespace New.Filling

section GeneralBlocks

variable {E : Type} [Field E] [CMType E]
  {𝔰 : Shape} {S : Filling E 𝔰} {side : FullOrCut}

/-! ### Preliminaries on cutoffs, the kernel, sums by layers and majorants -/

/-- The rational points of the Bessel subgroup `besselS` form a stable set: multiplying on either
side by rational points of `besselU` does not affect membership in `besselS`. -/
lemma isStable_besselS : S.IsStable (S.ratMiddle E).besselS := by
  simp +contextual [IsStable, mul_mem_cancel_right, mul_mem_cancel_left]

/-- The quotient measure of a unimodular Haar measure `ν` on a subgroup of `G₁` is σ-finite, as its
density, a chosen cutoff for `ν`, is almost everywhere finite. -/
instance sigmaFinite_orbitMeasure
    {A : Subgroup 𝔰.G₁} (ν : Measure A) [h : RealPlace.IsUnimodularHaar ν] :
    SigmaFinite (orbitMeasure ν (@volume 𝔰.G₁ _)) :=
  have h_cutoff : IsCutoff ν (chosenCutoff ν) := Classical.epsilon_spec h.out
  .withDensity_of_ne_top (h_cutoff.ae_cutoff_lt_top.mono fun _ hy ↦ hy.ne)

/-- Unfolding at several places: if `ν` is a unimodular Haar measure on a subgroup of `G₁`, then
`(x, u) ↦ (u v * x v)_v` carries the product of the quotient measures and of the copies of `ν` to
the Haar measure on `P → G₁`, for a finite type `P`. -/
lemma measurePreserving_pi_orbitMeasure {A : Subgroup 𝔰.G₁} (ν : Measure A)
    [RealPlace.IsUnimodularHaar ν] {P : Type*} [Fintype P] :
    MeasurePreserving (fun p : (P → 𝔰.G₁) × (P → A) ↦ (fun v : P ↦ (p.2 v).1) * p.1)
      ((Measure.pi fun _ : P ↦ orbitMeasure ν (volume : Measure 𝔰.G₁)).prod
        (Measure.pi fun _ : P ↦ ν))
      (volume : Measure (P → 𝔰.G₁)) :=
  (measurePreserving_pi _ _ fun _ : P ↦
      measurePreserving_orbitMeasure (ν := ν) (μ := (volume : Measure 𝔰.G₁))).comp
    (measurePreserving_arrowProdEquivProdArrow ..).symm

/-- Let `g j`, for `j` in a countable index set `J`, be measurable functions with values in a
finite-dimensional space `EuclideanSpace ℂ I`, and let the sum over `j` of the integrals of `‖g j‖`
be finite. Then the `i`-th coordinate of `∑' j, ∫ g j` equals the integral of `∑' j, (g j x) i`. -/
lemma tsum_integral_apply {X J I : Type*} [MeasurableSpace X] {μ : Measure X} [Countable J]
    [Fintype I] {g : J → X → EuclideanSpace ℂ I} (hg_meas : ∀ j : J, Measurable (g j))
    (hg_fin : ∑' j : J, ∫⁻ x : X, ‖g j x‖ₑ ∂μ < ∞) (i : I) :
    (∑' j : J, ∫ x : X, g j x ∂μ) i = ∫ x : X, ∑' j : J, g j x i ∂μ := by
  -- Take the `i`-th coordinate through the sum and the integral, then exchange the two.
  have h_integrable (j) : Integrable (g j) μ := ⟨by fun_prop, (ENNReal.le_tsum j).trans_lt hg_fin⟩
  have h_coord_fin : ∑' j, ∫⁻ x, ‖g j x i‖ₑ ∂μ < ∞ := by grw [PiLp.enorm_apply_le, hg_fin]
  have h_summable : Summable fun j ↦ ∫ x, g j x ∂μ :=
    .of_enorm (ne_of_lt (by grw [enorm_integral_le_lintegral_enorm, hg_fin]))
  calc
    _ = ∑' j, (∫ x, g j x ∂μ) i := (EuclideanSpace.proj i).map_tsum h_summable
    _ = ∑' j, ∫ x, g j x i ∂μ := tsum_congr fun j ↦ eval_integral_piLp (h_integrable j).eval_piLp i
    _ = ∫ x, ∑' j, g j x i ∂μ := (integral_tsum (by fun_prop) h_coord_fin.ne).symm

/-- The group `S.ResidueGL`, a finite product of general linear groups over finite residue fields,
is finite. -/
noncomputable instance : Fintype S.ResidueGL := .ofFinite _

/-- The Bessel function `S.besselFn side` is invariant under left translation by the image at the
infinite places of the group `S.classUnipotent c` of a class `c`. -/
lemma besselFn_mul_of_mem_classUnipotent {c : S.Classes} (u : S.classUnipotent c)
    (y : InfinitePlace E → 𝔰.G₁) :
    S.besselFn side (S.ratToInf u * y) = S.besselFn side y := by
  -- `besselFn` changes by the inverse of `unipotentChar`. The conjugate of `u` by the
  -- representative of `c` lies in `S.principalLevel`, so the character has at `u` its value at `1`.
  obtain ⟨hu_besselU, hu_level⟩ := u.2
  have h_char : S.unipotentChar (S.ratToFin u) = 1 := by
    simp_all [unipotentChar_eq_of_mem_principalLevel (one_mem _) _ c.out]
  simp [besselFn_ratToInf_mul hu_besselU, h_char]

/-- Let `besselKernel γ y` be the tensor `besselFn(y) ⊗ besselFn(γ⁻¹ y)^*` of Bessel functions. Let
`u`, `u'` lie in the unipotent subgroup `besselU` of `(S.ratMiddle E).G`, the group `S.G E` of
rational isometries of the form with middle Gram matrix `S.ratMiddle E`. Then the kernel at
`(u γ u'⁻¹, u y)` is `ψ(u)⁻¹ ψ(u')` times the kernel at `(γ, y)`. Here `ψ` is `unipotentChar`
applied to the finite-adelic images `ratToFin u` and `ratToFin u'`. -/
lemma besselKernel_besselU_mul {u u' : (S.ratMiddle E).G} (hu : u ∈ besselU) (hu' : u' ∈ besselU)
    (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
    S.besselKernel side (u * γ * u'⁻¹) (S.ratToInf u * y) =
      ((S.unipotentChar (S.ratToFin u))⁻¹ * S.unipotentChar (S.ratToFin u')) •
        S.besselKernel side γ y := by
  -- Apply `besselFn_ratToInf_mul` in both factors; conjugation inverts the second character, of
  -- modulus `1`.
  ext p
  have h_arg : (S.ratToInf (u * γ * u'⁻¹))⁻¹ * (S.ratToInf u * y) =
      S.ratToInf u' * ((S.ratToInf γ)⁻¹ * y) := by
    simp [mul_assoc]
  have h_conj : starRingEnd ℂ (S.unipotentChar (S.ratToFin u')) =
      (S.unipotentChar (S.ratToFin u'))⁻¹ := by simp [unipotentChar, ← inv_eq_conj]
  simp only [besselKernel, PiLp.smul_apply, h_arg, besselFn_ratToInf_mul hu,
    besselFn_ratToInf_mul hu']
  simp [h_conj]
  ring

/-- Unfolding: let each `w v` be measurable and left invariant under the unipotent group `besselU`
(`FixesLeft`). Then the integral of the cutoff `S.classCutoff c y` of the class `c` times
`∏ v, w v (y v)` is the covolume `S.unipotentCovolume` times the product of the integrals of the
`w v` for the quotient measure `besselQuotMeasure` on `𝖴 \ G₁`. -/
lemma lintegral_classCutoff_mul_prod [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {w : InfinitePlace E → 𝔰.G₁ → ℝ≥0∞} (hw_meas : ∀ v : InfinitePlace E, Measurable (w v))
    (hw_inv : ∀ v : InfinitePlace E, besselU.FixesLeft (w v)) (c : S.Classes) :
    ∫⁻ y : InfinitePlace E → 𝔰.G₁, S.classCutoff c y * ∏ v : InfinitePlace E, w v (y v) =
      .ofReal S.unipotentCovolume *
        ∏ v : InfinitePlace E, ∫⁻ y : 𝔰.G₁, w v y ∂besselQuotMeasure := by
  -- Unfold `y = u * x` with `u` in the product of the groups `besselU`: the factors `w v` do not
  -- see `u`, and the integral of `S.classCutoff c` over `u` is `S.unipotentCovolume`.
  calc
    _ = ∫⁻ x, (∫⁻ u, S.classCutoff c (fun v ↦ ((u v).1 : 𝔰.G₁) * x v)
          ∂(Measure.pi fun _ : InfinitePlace E ↦ 𝔰.besselHaar)) *
        ∏ v, w v (x v) ∂(Measure.pi fun _ : InfinitePlace E ↦ besselQuotMeasure) := by
      simp (disch := measurability) [lintegral_prod, Pi.mul_def, hw_inv, lintegral_mul_const,
        ← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar).lintegral_comp]
    _ = .ofReal S.unipotentCovolume *
        ∫⁻ x, ∏ v, w v (x v) ∂(.pi fun _ : InfinitePlace E ↦ besselQuotMeasure) := by
      simp only [lintegral_classCutoff_eq_unipotentCovolume]
      exact lintegral_const_mul' _ _ ofReal_ne_top
    _ = _ := by simp (disch := measurability) [lintegral_pi_prod]

/-- Summation by layers. Let `u ≥ 1` and `K ≥ 0`. If the points with `u p ≤ R` have total weight at
most `(K R ^ e) ^ d` for all `R ≥ 1`, then the weighted sum of `u p ^ (-i)` is at most `2 K ^ d` as
soon as `2 e d < i`. -/
lemma tsum_mul_inv_pow_le_of_layers {α : Type*} {w : α → ℝ≥0∞} {u : α → ℝ} {K : ℝ} {e d i : ℕ}
    (hu : ∀ p : α, 1 ≤ u p) (hK : 0 ≤ K)
    (h_count : ∀ R ≥ (1 : ℝ), ∑' p : α, {p : α | u p ≤ R}.indicator w p ≤ .ofReal ((K * R ^ e) ^ d))
    (hi : 2 * (e * d) < i) :
    ∑' p : α, w p * .ofReal ((u p)⁻¹ ^ i) ≤ .ofReal (2 * K ^ d) := by
  -- Apply the layer cake bound to the measure with mass `w p` at the point `p`.
  let : MeasurableSpace α := ⊤
  let μ : Measure α := Measure.count.withDensity w
  have hi_real : 2 * ((e : ℝ) * d) < i := mod_cast hi
  have h_ed : 0 ≤ (e : ℝ) * d := by positivity
  have h_vol (R : ℝ) (hR : R ≥ 1) : μ {p | u p ≤ R} ≤ .ofReal ((K * R ^ e) ^ d) * 1 := by
    rw [withDensity_apply _ MeasurableSpace.measurableSet_top,
      ← lintegral_indicator MeasurableSpace.measurableSet_top, lintegral_count, mul_one]
    exact h_count R hR
  calc
    _ = ∫⁻ p, .ofReal (u p ^ (-i : ℝ)) ∂μ := by
      rw [lintegral_withDensity_eq_lintegral_mul _ measurable_from_top measurable_from_top,
        lintegral_count]
      simp only [Pi.mul_apply, Real.rpow_neg (zero_le_one.trans (hu _)), Real.rpow_natCast, inv_pow]
    _ ≤ .ofReal (K ^ d * 2) * 1 :=
      lintegral_rpow_neg_le_of_measure_sublevel_le measurable_from_top hu hK h_vol (by linarith)
        (by linarith)
    _ = .ofReal (2 * K ^ d) := by rw [mul_one, mul_comm]

variable (S) in
/-- The product over the infinite places `v` of the scaled lengths of `y v`, each of which is
`max 1 (besselLength (y v) / b ^ (6 n))`. Here `besselLength x` is the infimum of `‖s x‖ + 1` over
`s` in the Bessel subgroup `besselS`, `b = S.b` and `n = ϱ + 1`. -/
noncomputable def scaledBesselLengthProd (y : InfinitePlace E → 𝔰.G₁) : ℝ :=
  ∏ v : InfinitePlace E, scaledBesselLength (y v) S.b

/-- The product of the scaled lengths over the infinite places is at least one. -/
lemma one_le_scaledBesselLengthProd (y : InfinitePlace E → 𝔰.G₁) : 1 ≤ S.scaledBesselLengthProd y :=
  Finset.one_le_prod₀ fun v _ ↦ one_le_scaledBesselLength (y v) S.b

/-- The scaled length at one infinite place is at most the product of all of them. -/
lemma scaledBesselLength_le_scaledBesselLengthProd (y : InfinitePlace E → 𝔰.G₁)
    (v : InfinitePlace E) :
    scaledBesselLength (y v) S.b ≤ S.scaledBesselLengthProd y := by
  rw [scaledBesselLengthProd, ← mul_prod_erase _ _ (mem_univ v)]
  exact le_mul_of_one_le_right (zero_le_one.trans (one_le_scaledBesselLength ..))
    (Finset.one_le_prod₀ fun w _ ↦ one_le_scaledBesselLength (y w) S.b)

/-- Let `S` be admissible, `T` a set of rational elements, `c` a class and `s` an element of the
finite group `S.ResidueGL`. Write `γ⁻¹ y` for `(S.ratToInf γ)⁻¹ * y`. Over all classes `d` and all
`γ` in `T ∩ S.termsOver c s d`, the cutoff `S.classCutoff d` at `γ⁻¹ y` times
`S.scaledBesselLengthProd (γ⁻¹ y) ^ (-(r ^ 3 * f))` adds up to at most `2 b ^ (12 n ^ 3 r f)`. Here
`b = S.b` is the real size parameter of `S`, `f` is the number of infinite places, `n = ϱ + 1` and
`r` is the rank of `G₁`. -/
lemma tsum_classCutoff_mul_inv_pow_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (y : InfinitePlace E → 𝔰.G₁) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) ≤
      .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) := by
  -- Sort the terms by the product `S.scaledBesselLengthProd` of the scaled lengths of `γ⁻¹ y` over
  -- the infinite places. Packing in the space of tuples of vectors, of real dimension `2 n r f`,
  -- bounds the total weight of the terms for which this product is at most `R`.
  have hb : 1 ≤ S.b := S.one_le_b
  let z (p : Σ d : S.Classes, ↥(T ∩ S.termsOver c s d)) : InfinitePlace E → 𝔰.G₁ :=
    (S.ratToInf p.2)⁻¹ * y
  let weight (p : Σ d : S.Classes, ↥(T ∩ S.termsOver c s d)) : ℝ≥0∞ :=
    S.classCutoff p.1 (z p)
  have h_dim : Module.finrank ℝ (⊤ : Submodule ℝ
      (InfinitePlace E → Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex)) =
      2 * 𝔰.n * 𝔰.r * numInfPlaces E := by
    simp [finrank_top, Module.finrank_pi_fintype, finrank_real_of_complex]
    ring
  have h_count (R : ℝ) (hR : R ≥ 1) :
      ∑' p, {p | S.scaledBesselLengthProd (z p) ≤ R}.indicator weight p ≤
        .ofReal ((S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2) ^ (2 * 𝔰.n * 𝔰.r * numInfPlaces E)) := by
    have h_size (p) (hp : p ∈ ({p | S.scaledBesselLengthProd (z p) ≤ R}.indicator weight).support)
        (v : InfinitePlace E) : besselLength (z p v) ≤ S.b ^ (6 * 𝔰.n + 2) * R := by
      have h_scaled : besselLength (z p v) / S.b ^ (6 * 𝔰.n) ≤ R :=
        (le_max_right ..).trans ((scaledBesselLength_le_scaledBesselLengthProd (z p) v).trans
          (Set.mem_of_indicator_ne_zero (s := {p | S.scaledBesselLengthProd (z p) ≤ R}) hp))
      grw [(div_le_iff₀' (by positivity)).1 h_scaled,
        pow_le_pow_right₀ hb (Nat.le_add_right (6 * 𝔰.n) 2)]
    rw [← h_dim, ← mul_one (ENNReal.ofReal _)]
    exact tsum_le_of_le_classCutoff_mul (y := y)
      (k := fun p : Σ d, ↥(T ∩ S.termsOver c s d) ↦ p.1) (γ := fun p ↦ p.2) hR Sigma.subtype_ext
      (fun p _ ↦ p.2.property.2) h_size
      (fun p _ ↦ (Set.indicator_le_self _ _ p).trans_eq (mul_one _).symm)
      fun _ _ _ _ ↦ Submodule.mem_top
  -- The exponent `r ^ 3 f` exceeds four times the dimension, as `8 n < r ^ 2`.
  have h_exp : 2 * (2 * (2 * 𝔰.n * 𝔰.r * numInfPlaces E)) < 𝔰.r ^ 3 * numInfPlaces E := by
    have hϱ := S.ten_pow_five_le_varrho
    have hr : 2 * 𝔰.ϱ + 1 ≤ 𝔰.r := by simp; lia
    have h_rank : 8 * 𝔰.n < 𝔰.r ^ 2 := by nlinarith
    nlinarith [show 0 < 𝔰.r * numInfPlaces E by positivity]
  calc
    _ = ∑' p, weight p *
        .ofReal ((S.scaledBesselLengthProd (z p))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) :=
      (ENNReal.tsum_sigma' _).symm
    _ ≤ .ofReal (2 * (S.b ^ (6 * 𝔰.n ^ 2)) ^ (2 * 𝔰.n * 𝔰.r * numInfPlaces E)) :=
      tsum_mul_inv_pow_le_of_layers (fun p ↦ one_le_scaledBesselLengthProd (z p)) (by positivity)
        h_count h_exp
    _ = _ := by rw [← pow_mul]; ring_nf

/-- Let `besselKernel γ y` be the tensor `besselFn(y) ⊗ besselFn(γ⁻¹ y)^*` of Bessel functions.
Where the kernel chosen by `side` differs from the cut kernel, the full and the cut Bessel function
differ at some place, at `y` or at `γ⁻¹ y`; so the product of the scaled lengths
(`scaledBesselLengthProd`) of the two points is at least the size parameter `S.b`. -/
lemma le_scaledBesselLengthProd_mul {γ : S.G E} {y : InfinitePlace E → 𝔰.G₁}
    (h_ne : S.besselKernel side γ y ≠ S.besselKernel .cut γ y) :
    S.b ≤ S.scaledBesselLengthProd y * S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y) := by
  by_contra h_near
  have h_eq (z : InfinitePlace E → 𝔰.G₁) (hz : ¬S.b ≤ S.scaledBesselLengthProd z)
    (v : InfinitePlace E) :
      (S.besselSystem v).besselFn .cut (z v) = (S.besselSystem v).besselFn .full (z v) := by
    by_contra h_cut
    have h_size : S.b ≤ scaledBesselLength (z v) S.b :=
      le_scaledBesselLength (by linarith [S.thousand_le_b])
        ((S.besselSystem v).isCutPair.lt_besselLength_of_ne _ h_cut)
    exact hz (h_size.trans (scaledBesselLength_le_scaledBesselLengthProd z v))
  have h_one_y : 1 ≤ S.scaledBesselLengthProd y := one_le_scaledBesselLengthProd y
  have h_one_z : 1 ≤ S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y) :=
    one_le_scaledBesselLengthProd _
  have h_left : ∀ v,
      (S.besselSystem v).besselFn .cut (y v) = (S.besselSystem v).besselFn .full (y v) :=
    h_eq y fun h ↦ h_near (h.trans (le_mul_of_one_le_right (by linarith) h_one_z))
  have h_right : ∀ v, (S.besselSystem v).besselFn .cut (((S.ratToInf γ)⁻¹ * y) v) =
      (S.besselSystem v).besselFn .full (((S.ratToInf γ)⁻¹ * y) v) :=
    h_eq _ fun h ↦ h_near (h.trans (le_mul_of_one_le_left (by linarith) h_one_y))
  -- For the full kernel this gives equality; for the cut kernel there is nothing to prove.
  cases side with
  | full => exact h_ne (by simp only [besselKernel, besselFn, h_left, h_right])
  | cut => exact h_ne rfl

section Majorant

variable {w : InfinitePlace E → 𝔰.G₁ → ℝ≥0∞} {a : InfinitePlace E → ℝ≥0∞}

/-- Let `hw` say that at each infinite place `v` the function `w v` is a decay majorant
(`IsDecayMajorant`, with constants `S.b` and `a v`) of the Bessel functions
`(S.besselSystem v).besselFn`. That is, `w v` bounds their norms times the scaled length
`max 1 (besselLength x / b ^ (6 n))` to the power `3 * r ^ 3 * f`. Here `b = S.b`, `n = ϱ + 1`, `r`
is the rank of `G₁` and `f = numInfPlaces E`. Then for every `y`, the product over `v` of the norms
`‖besselFn side (y v)‖`, times `scaledBesselLengthProd y` to the power
`r ^ 3 * f + 2 * (r ^ 3 * f)`, is at most the product over `v` of `w v (y v)`. -/
lemma pow_mul_pow_mul_prod_enorm_le
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (y : InfinitePlace E → 𝔰.G₁) :
    ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (𝔰.r ^ 3 * numInfPlaces E) *
      (ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
        ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ) ≤
      ∏ v : InfinitePlace E, w v (y v) := by
  have h_nonneg (v : InfinitePlace E) : 0 ≤ scaledBesselLength (y v) S.b :=
    zero_le_one.trans (one_le_scaledBesselLength ..)
  calc
    _ = ∏ v, ENNReal.ofReal (scaledBesselLength (y v) S.b ^ (3 * 𝔰.r ^ 3 * numInfPlaces E)) *
        ‖(S.besselSystem v).besselFn side (y v)‖ₑ := by
      simp only [scaledBesselLengthProd, ofReal_prod_of_nonneg fun v _ ↦ h_nonneg v,
        ofReal_pow (h_nonneg _), prod_mul_distrib, prod_pow]
      ring
    _ ≤ _ := prod_le_prod fun v _ ↦ (hw v).pow_mul_enorm_le side (y v)

/-- At each infinite place `v` let the function `w v` be a decay majorant (`IsDecayMajorant`) of the
Bessel functions: it bounds their norm times the scaled length to the power `3 * r ^ 3 * f`, where
`r` is the rank of `G₁` and `f` the number of infinite places. Then the product over the places of
the norms, times the product `scaledBesselLengthProd` of the scaled lengths to the power
`2 * (r ^ 3 * f)`, is at most the product of the `w v`. -/
lemma pow_mul_prod_enorm_le_majorant
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (y : InfinitePlace E → 𝔰.G₁) :
    ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
      ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ ≤
      ∏ v : InfinitePlace E, w v (y v) := by
  refine (le_mul_of_one_le_left' (one_le_pow₀ ?_)).trans (pow_mul_pow_mul_prod_enorm_le hw y)
  exact one_le_ofReal.2 (one_le_scaledBesselLengthProd y)

/-- At each infinite place `v` let the function `w v`, bounded by the constant `a v`, be a decay
majorant (`IsDecayMajorant`) of the Bessel functions: it bounds their norm times the scaled length
to the power `3 * r ^ 3 * f`, where `r` is the rank of `G₁` and `f` the number of infinite places.
Then the product of the norms, times the product `scaledBesselLengthProd` of the scaled lengths to
the power `2 * (r ^ 3 * f)`, is at most the product of the `a v` times `scaledBesselLengthProd` to
the power `-(r ^ 3 * f)`. -/
lemma pow_mul_prod_enorm_le_bound
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (y : InfinitePlace E → 𝔰.G₁) :
    ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
        ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ ≤
      (∏ v : InfinitePlace E, a v) *
        .ofReal ((S.scaledBesselLengthProd y)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) := by
  have h_pos : 0 < S.scaledBesselLengthProd y := one_pos.trans_le (one_le_scaledBesselLengthProd y)
  -- Move the power `-(r ^ 3 * f)` to the left side.
  rw [mul_comm (∏ v, a v), ofReal_pow (inv_pos.2 h_pos).le, ofReal_inv_of_pos h_pos,
    ← ENNReal.inv_pow, ← mul_le_iff_le_inv (pow_ne_zero _ (ofReal_pos.2 h_pos).ne')
      (pow_ne_top ofReal_ne_top)]
  exact (pow_mul_pow_mul_prod_enorm_le hw y).trans (prod_le_prod fun v _ ↦ (hw v).le_bound (y v))

/-- At each infinite place `v` there are a Bessel function W and its cut W♭, of bounded support
modulo the Bessel subgroup. Let the function `w v`, bounded by the constant `a v`, be a decay
majorant (`IsDecayMajorant`): it bounds the norms of W and W♭ times the scaled length
`max 1 (besselLength / b ^ (6 n))` to the power `3 * r ^ 3 * f`. Then the kernel
`W(y) ⊗ W(γ⁻¹ y)^*`, built from W or W♭ as `side` says, and the kernel built from W♭ differ by at
most `2 * b ^ (-(2 * (r ^ 3 * f)))` times the product of the `w v` at `y`, the product of the `a v`
and the product of the scaled lengths of `γ⁻¹ y` (`scaledBesselLengthProd`) to the power
`-(r ^ 3 * f)`. Here `b = S.b`, `n = ϱ + 1`, `r` is the rank of `G₁` and `f` the number of infinite
places. -/
lemma enorm_besselKernel_sub_cut_le
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
    ‖S.besselKernel side γ y - S.besselKernel .cut γ y‖ₑ ≤
      (ENNReal.ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E))))⁻¹ *
        (2 * ((∏ v : InfinitePlace E, w v (y v)) * ((∏ v : InfinitePlace E, a v) *
          .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
            (𝔰.r ^ 3 * numInfPlaces E))))) := by
  rcases eq_or_ne (S.besselKernel side γ y) (S.besselKernel .cut γ y) with h_eq | h_ne
  · simp [h_eq]
  have hb : 0 < S.b := one_pos.trans_le S.one_le_b
  set z : InfinitePlace E → 𝔰.G₁ := (S.ratToInf γ)⁻¹ * y
  let gain : ℝ≥0∞ := .ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)))
  -- The cut acts at one of the two points, so the spare powers of the scaled lengths pay for the
  -- gain.
  have h_gain : gain ≤ ENNReal.ofReal (S.scaledBesselLengthProd y) ^
    (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
      ENNReal.ofReal (S.scaledBesselLengthProd z) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) := by
    have h_far : S.b ≤ S.scaledBesselLengthProd y * S.scaledBesselLengthProd z :=
      le_scaledBesselLengthProd_mul h_ne
    rw [← mul_pow, ← ofReal_mul (zero_le_one.trans (one_le_scaledBesselLengthProd y)),
      ← ofReal_pow (hb.le.trans h_far)]
    exact ofReal_le_ofReal (pow_le_pow_left₀ hb.le h_far _)
  have h_kernel (τ : FullOrCut) : gain * ‖S.besselKernel τ γ y‖ₑ ≤ (∏ v, w v (y v)) *
      ((∏ v, a v) * .ofReal ((S.scaledBesselLengthProd z)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E))) := by
    grw [h_gain, enorm_besselKernel, mul_mul_mul_comm, pow_mul_prod_enorm_le_majorant hw,
      pow_mul_prod_enorm_le_bound hw]
  rw [← mul_le_iff_le_inv (by positivity) ofReal_ne_top]
  grw [enorm_sub_le, mul_add, h_kernel, h_kernel, two_mul]

end Majorant

variable [S.IsAdmissible]

/-- For 12 n³ + 500 ≤ k < r and f ≥ 1, the exponent 12 n³ r f + 1 + 400 r² f + 2 k f of the
losses in the tail bound plus the saving k³ f is at most the gain 2 r³ f. -/
lemma cut_exponent_le {n r k f : ℕ} (hk : 12 * n ^ 3 + 500 ≤ k) (hr : k + 1 ≤ r) (hf : 1 ≤ f) :
    12 * n ^ 3 * r * f + 1 + 400 * r ^ 2 * f + 2 * k * f + k ^ 3 * f ≤ 2 * (r ^ 3 * f) := by
  have h_count : 12 * n ^ 3 * r ≤ r ^ 2 := by grw [sq, show 12 * n ^ 3 ≤ r by lia]
  have h_dim : 2 * k + 1 ≤ r ^ 2 := by nlinarith
  have h_small : 402 * r ^ 2 ≤ r ^ 3 := by grw [pow_succ' r 2, show 402 ≤ r by lia]
  have h_cube : k ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (by lia) 3
  calc
    _ ≤ (12 * n ^ 3 * r + 400 * r ^ 2 + (2 * k + 1) + k ^ 3) * f := by nlinarith
    _ ≤ 2 * r ^ 3 * f := Nat.mul_le_mul_right f (by lia)
    _ = _ := mul_assoc ..

/-- Let `E` contain a primitive 5040th root of unity, let `S` be admissible and let `T` be a set of
rational elements. Sum, over all classes `d` and all `γ ∈ T` that are terms over `(c, s, d)`
(`termsOver`), the cutoff of `d` at `γ⁻¹ y` times `A` times the product of the scaled lengths of
`γ⁻¹ y` (`scaledBesselLengthProd`) to the power `-(r ^ 3 * f)`. The sum is at most
`A * 2 b ^ (12 n ^ 3 r f)`. Here `b = S.b` is the size parameter of `S`, `f` is the number of
infinite places, `n = ϱ + 1` and `r` is the rank of the hermitian space of `G₁`. -/
lemma tsum_classCutoff_mul_const_mul_inv_pow_le [HasPrimitiveRoot5040 E]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (A : ℝ≥0∞) (y : InfinitePlace E → 𝔰.G₁) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        (A * .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
          (𝔰.r ^ 3 * numInfPlaces E))) ≤
      A * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) := by
  simp only [mul_left_comm _ A, ENNReal.tsum_mul_left]
  exact mul_le_mul_right (tsum_classCutoff_mul_inv_pow_le T c s y) _

/-- Let `S` be admissible and `T` a set of rational elements. At each infinite place `v` let `w v`
be a decay majorant of the Bessel functions (`IsDecayMajorant`); what is used is that `w v` is
measurable and left invariant under the unipotent group `besselU`, and that the constant `a v` times
the integral of `w v` over `𝖴 \ G₁` is at most `b ^ (400 r ^ 2)` times the dimension of the value
space. Let `d` run over all classes and `γ` over the terms of `T` over `(c, s, d)`. Then the sum of
the integrals of `β_c(y) β_d(γ⁻¹ y)` times the product of the `w v` at `y`, the product of the `a v`
and `scaledBesselLengthProd (γ⁻¹ y)` to the power `-(r ^ 3 * f)` is at most `ν * 2 b ^ (12 n ^ 3 r
f) * b ^ (400 r ^ 2 f) * card S.BesselCoord`. Here `β_c = S.classCutoff c`,
`ν = S.unipotentCovolume`, `b` is the size parameter of `S`, `f` is the number of infinite places,
`n = ϱ + 1` and `r` is the rank of `G₁`. -/
lemma tsum_lintegral_classCutoff_mul_majorant_le [HasPrimitiveRoot5040 E]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL)
    {w : InfinitePlace E → 𝔰.G₁ → ℝ≥0∞} {a : InfinitePlace E → ℝ≥0∞}
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v)) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), ∫⁻ y : InfinitePlace E → 𝔰.G₁,
        S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
          ((∏ v : InfinitePlace E, w v (y v)) * ((∏ v : InfinitePlace E, a v) * .ofReal
            ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)))) ≤
      .ofReal S.unipotentCovolume * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) *
        (.ofReal (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * card S.BesselCoord) := by
  -- Multiply the sum over the terms by `β_c * ∏ v, w v`, integrate, and unfold over `besselU`.
  let countBound : ℝ≥0∞ := .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E))
  have hw_meas (v : InfinitePlace E) : Measurable (w v) := (hw v).measurable
  have hw_inv (v : InfinitePlace E) : besselU.FixesLeft (w v) :=
    fun u hu ↦ (hw v).fixesLeft u (mem_partialUnitriangularGroup_of_mem_besselU hu)
  have h_size : Measurable S.scaledBesselLengthProd := by
    fun_prop [scaledBesselLengthProd, scaledBesselLength]
  calc
    _ = ∫⁻ y, S.classCutoff c y * (∏ v, w v (y v)) * ∑' (d : S.Classes)
        (γ : ↥(T ∩ S.termsOver c s d)), S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * ((∏ v, a v) *
          .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
            (𝔰.r ^ 3 * numInfPlaces E))) := by
      simp (disch := fun_prop) only [← ENNReal.tsum_mul_left, lintegral_tsum,
        mul_mul_mul_comm _ _ (classCutoff ..)]
    _ ≤ ∫⁻ y, S.classCutoff c y * (∏ v, w v (y v)) * ((∏ v, a v) * countBound) := by
      grw [tsum_classCutoff_mul_const_mul_inv_pow_le]
    _ = .ofReal S.unipotentCovolume * countBound * ∏ v, a v * ∫⁻ y, w v y ∂besselQuotMeasure := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_classCutoff_mul_prod hw_meas hw_inv,
        mul_comm _ countBound, mul_mul_mul_comm, mul_comm (univ.prod _), ← prod_mul_distrib]
    _ ≤ _ := by
      grw [prod_le_prod fun v _ ↦ (hw v).bound_mul_lintegral_le]
      simp [countBound, prod_mul_distrib, Fintype.card_pi]

/-- For admissible `S`, twice the product of `ν`, `2 b ^ (12 n ^ 3 r f)`, `b ^ (400 r ^ 2 f)` and
the number `card S.BesselCoord` of Bessel coordinates, divided by `b ^ (2 r ^ 3 f)`, is at most
`ν b ^ (-k³ f) / 2`. Here `b` is the size parameter of `S`, `f` the number of infinite places,
`ν = S.unipotentCovolume`, `k = 𝔰.k`, `n = ϱ + 1` and `r` is the rank of `G₁`. -/
lemma inv_pow_mul_unipotentCovolume_mul_card_le :
    (ENNReal.ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E))))⁻¹ * 2 *
      (.ofReal S.unipotentCovolume * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) *
        (.ofReal (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * card S.BesselCoord)) ≤
      .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 1 ≤ S.b := S.one_le_b
  have hk : 12 * 𝔰.n ^ 3 + 500 ≤ 𝔰.k := by
    have h_large : 1000 * (2 * 𝔰.ϱ + 2) ^ 3 ≤ 𝔰.k := S.pow_le_k.trans' (by gcongr; simp)
    rw [show 2 * 𝔰.ϱ + 2 = 2 * 𝔰.n by ring, mul_pow] at h_large
    linarith [Nat.one_le_pow 3 𝔰.n 𝔰.ϱ.succ_pos]
  have h_rank : 𝔰.k + 1 ≤ 𝔰.r := by simp +arith
  have h_pow : S.b * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E) *
      (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * S.b ^ (2 * 𝔰.k * numInfPlaces E) *
        S.b ^ (𝔰.k ^ 3 * numInfPlaces E) ≤ S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) := by
    simp only [← pow_mul, ← pow_add, ← pow_succ']
    exact pow_le_pow_right₀ hb (cut_exponent_le hk h_rank Fintype.card_pos)
  rw [le_ofReal_iff_toReal_le (by finiteness) (by positivity)]
  -- Clear the denominators and cancel `unipotentCovolume`; the constant `8` is at most `b`, and the
  -- number of coordinates is at most `b ^ (2 k f)`.
  simp (disch := positivity) only [toReal_mul, toReal_inv, toReal_pow, toReal_ofReal,
    toReal_ofNat, toReal_natCast, fieldLe]
  change (2 : ℝ) ^ 3 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E) *
      (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * (card S.BesselCoord : ℝ) *
        S.b ^ (𝔰.k ^ 3 * numInfPlaces E) ≤ S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E))
  have h_card : (card S.BesselCoord : ℝ) ≤ S.b ^ (2 * 𝔰.k * numInfPlaces E) :=
    IsAdmissible.card_besselCoord_le
  grw [h_card, show (2 : ℝ) ^ 3 ≤ S.b by linarith [S.thousand_le_b]]
  exact h_pow

/-! ### Convergence and the tail bound -/

/-! At each place the Bessel functions lie below an invariant majorant `w v`, bounded by a constant
`a v`, with the power `3 i` of the scaled length to spare, `i = r ^ 3 f`. At `γ⁻¹ y` the power `i`
makes the sum over `γ` converge; at `y` we unfold `classCutoff c` and integrate `w`. The power `2 i`
that is left at both points gains `b ^ (-2 i)` where the cut acts, and this beats all the losses. -/

omit [S.IsAdmissible] in
/-- A power of the product of the scaled lengths is at least `1`, so it may be inserted as a
factor. -/
lemma le_scaledBesselLengthProd_pow_mul (y : InfinitePlace E → 𝔰.G₁) (i : ℕ) (x : ℝ≥0∞) :
    x ≤ ENNReal.ofReal (S.scaledBesselLengthProd y) ^ i * x :=
  le_mul_of_one_le_left' (one_le_pow₀ (one_le_ofReal.2 (one_le_scaledBesselLengthProd y)))

variable [HasPrimitiveRoot5040 E]

/-- Let the CM field `E` contain a primitive 5040th root of unity, and let the data `S` satisfy the
standing hypotheses `IsAdmissible`. Let `d` run over all classes and `γ` over the elements of `T`
that are terms over `(c, s, d)`. Then the sum of `β_d(γ⁻¹ y) ∏_v ‖W_v((γ⁻¹ y)_v)‖` is at most a
finite constant `C` that does not depend on the point `y` of G_∞, the product of one copy of `G₁`
for each infinite place `v`. -/
theorem exists_tsum_classCutoff_mul_prod_enorm_le {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰} {side : FullOrCut} [S.IsAdmissible]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) :
    ∃ C : NNReal, ∀ y : InfinitePlace E → 𝔰.G₁,
      ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
          S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
            ∏ v : InfinitePlace E,
              ‖(S.besselSystem v).besselFn side (((S.ratToInf γ)⁻¹ * y) v)‖ₑ ≤
        C := by
  -- The Bessel functions decay in the scaled lengths, and this decay makes the sum converge.
  have h_majorant (v : InfinitePlace E) : ∃ (w : 𝔰.G₁ → ℝ≥0∞) (a : ℝ≥0∞),
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn w a :=
    (S.besselSystem v).isCutPair.exists_majorant
  choose w a hw using h_majorant
  have h_decay (z : InfinitePlace E → 𝔰.G₁) : ∏ v, ‖(S.besselSystem v).besselFn side (z v)‖ₑ ≤
      (∏ v, a v) * .ofReal ((S.scaledBesselLengthProd z)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) :=
    (le_scaledBesselLengthProd_pow_mul z _ _).trans (pow_mul_prod_enorm_le_bound hw z)
  let bound : ℝ≥0∞ :=
    (∏ v, a v) * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E))
  have h_bound_fin : bound ≠ ∞ :=
    mul_ne_top (prod_ne_top fun v _ ↦ (hw v).bound_ne_top) ofReal_ne_top
  refine ⟨bound.toNNReal, fun y ↦ ?_⟩
  calc
    _ ≤ ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
          S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * ((∏ v, a v) * .ofReal
            ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
              (𝔰.r ^ 3 * numInfPlaces E))) := by
      grw [h_decay]
    _ ≤ bound := tsum_classCutoff_mul_const_mul_inv_pow_le T c s (∏ v, a v) y
    _ = bound.toNNReal := (coe_toNNReal h_bound_fin).symm

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `S` be admissible, and let `γ` run over the elements of `T` that are terms over `(c, s, d)`,
for all classes `d`. The sum of the integrals `∫ β_c(y) β_d(γ⁻¹ y) ‖W(y) ⊗ W(γ⁻¹ y)^*‖ dy`
(`amplitudeMajorant`) is finite. -/
theorem tsum_amplitudeMajorant_lt_top (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), S.amplitudeMajorant side c d γ < ∞ := by
  choose w a hw using fun v : InfinitePlace E ↦ (S.besselSystem v).isCutPair.exists_majorant
  have h_majorant (y : InfinitePlace E → 𝔰.G₁) :
      ∏ v, ‖(S.besselSystem v).besselFn side (y v)‖ₑ ≤ ∏ v, w v (y v) :=
    (le_scaledBesselLengthProd_pow_mul y _ _).trans (pow_mul_prod_enorm_le_majorant hw y)
  have h_decay (z : InfinitePlace E → 𝔰.G₁) : ∏ v, ‖(S.besselSystem v).besselFn side (z v)‖ₑ ≤
      (∏ v, a v) * .ofReal ((S.scaledBesselLengthProd z)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) :=
    (le_scaledBesselLengthProd_pow_mul z _ _).trans (pow_mul_prod_enorm_le_bound hw z)
  calc
    _ ≤ ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), ∫⁻ y : InfinitePlace E → 𝔰.G₁,
          S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
            ((∏ v, w v (y v)) * ((∏ v, a v) * .ofReal
              ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
                (𝔰.r ^ 3 * numInfPlaces E)))) := by
      simp_rw [amplitudeMajorant, enorm_besselKernel]
      grw [h_majorant, h_decay]
    _ ≤ .ofReal S.unipotentCovolume * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) *
          (.ofReal (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * card S.BesselCoord) :=
      tsum_lintegral_classCutoff_mul_majorant_le T c s hw
    _ < ∞ := by finiteness

/-- Let `S` be admissible, let `d` run over all classes and `γ` over the elements of `T` that are
terms over `(c, s, d)`. The kernel `besselKernel side γ y` is `W(y) ⊗ W(γ⁻¹ y)^*`. The sum of the
integrals of `β_c(y) β_d(γ⁻¹ y)` times the norm of the difference between this kernel and the one
built from the cut function is at most `ν b ^ (-k³ f) / 2`. Here `ν = S.unipotentCovolume`,
`β_d = S.classCutoff d`, `k + 1` is the size of the middle block of the basis (`k = 𝔰.k`), `f` is
the number of infinite places and `b` is the size parameter of `S`. -/
theorem tsum_lintegral_enorm_besselKernel_sub_cut_le (T : Set (S.G E)) (c : S.Classes)
    (s : S.ResidueGL) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
      ∫⁻ y : InfinitePlace E → 𝔰.G₁, S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        ‖S.besselKernel side γ y - S.besselKernel .cut γ y‖ₑ ≤
      .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  choose w a hw using fun v : InfinitePlace E ↦ (S.besselSystem v).isCutPair.exists_majorant
  let gain : ℝ≥0∞ := .ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)))
  have hb : 1 ≤ S.b := S.one_le_b
  have h_gain_fin : gain⁻¹ ≠ ∞ := inv_ne_top.2 (by positivity)
  let majorant (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ :=
    (∏ v, w v (y v)) * ((∏ v, a v) * .ofReal
      ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)))
  calc
    _ ≤ ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), ∫⁻ y, S.classCutoff c y *
          S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * (gain⁻¹ * (2 * majorant γ y)) := by
      grw [enorm_besselKernel_sub_cut_le hw]
    _ = gain⁻¹ * 2 * ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
          ∫⁻ y, S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * majorant γ y := by
      simp (disch := finiteness) only [← mul_assoc gain⁻¹, mul_left_comm _ (gain⁻¹ * _),
        lintegral_const_mul', ENNReal.tsum_mul_left]
    _ ≤ _ := (mul_le_mul_right (tsum_lintegral_classCutoff_mul_majorant_le T c s hw) _).trans
      inv_pow_mul_unipotentCovolume_mul_card_le

/-- For admissible `S`, the amplitudes of the elements of `T` over `(c, s, c')` are summable. -/
lemma summable_amplitude (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    Summable fun γ : ↥(T ∩ S.termsOver c s c') ↦ S.amplitude side c c' γ := by
  refine .of_enorm (ne_of_lt ?_)
  grw [enorm_amplitude_le]
  exact (ENNReal.le_tsum c').trans_lt (tsum_amplitudeMajorant_lt_top T c s)

variable {T : Set (S.G E)}

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- If `σ` is a term over `(c, t, c₁)` and `σ'` one over `(c', t', c₁')`, then `γ` is a term over
`(c₁, s, c₁')` if and only if `σ γ σ'⁻¹` is one over `(c, t s t'⁻¹, c')`. -/
lemma mem_termsOver_iff_mul_mul_inv_mem {c c₁ c' c₁' : S.Classes} {t t' s : S.ResidueGL}
    {σ σ' γ : S.G E} (hσ_over : σ ∈ S.termsOver c t c₁) (hσ'_over : σ' ∈ S.termsOver c' t' c₁') :
    γ ∈ S.termsOver c₁ s c₁' ↔ σ * γ * σ'⁻¹ ∈ S.termsOver c (t * s * t'⁻¹) c' :=
  ⟨fun hγ ↦ termsOver.mul (.mul hσ_over hγ) (.inv hσ'_over),
    fun hγ ↦ by simpa using termsOver.mul (.inv hσ_over) (.mul hγ hσ'_over)⟩

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Let `σ` be a
rational isometry of the form with middle Gram matrix `S.ratMiddle E`. Assume that `σ` lies in the
Bessel subgroup `besselS`, generated by the unipotent group `besselU` and U(X₀), and is a term over
`(c, t, c₁)` (`termsOver`). Then `y ↦ S.classCutoff c (σ y)` has orbit sums `1` under
`S.classUnipotent c₁`, the rational points `u` of `besselU` with h_c₁⁻¹ u h_c₁ in the principal
congruence subgroup of level `S.M`. -/
lemma tsum_classCutoff_ratToInf_mul_eq_one {c c₁ : S.Classes} {t : S.ResidueGL}
    {σ : (S.ratMiddle E).G} (hσ : σ ∈ (S.ratMiddle E).besselS) (hσ_over : σ ∈ S.termsOver c t c₁)
    (y : InfinitePlace E → 𝔰.G₁) :
    ∑' u : S.classUnipotent c₁, S.classCutoff c (S.ratToInf σ * (S.ratToInf u * y)) = 1 := by
  -- Conjugation by `σ` carries `S.classUnipotent c₁` onto `S.classUnipotent c`.
  have conj_mem (γ : (S.ratMiddle E).G) :
      γ ∈ S.classUnipotent c₁ ↔ MulAut.conj σ γ ∈ S.classUnipotent c := by
    refine ((besselS_le_normalizer_besselU hσ γ).and
      (mem_termsOver_iff_mul_mul_inv_mem (s := 1) hσ_over hσ_over)).trans ?_
    simp only [MulAut.conj_apply, mul_one, mul_inv_cancel, mul_assoc]
    rfl
  simpa [mul_assoc] using (((MulAut.conj σ).subtypeEquiv conj_mem).tsum_eq _).trans
    (tsum_classCutoff_eq_one c (S.ratToInf σ * y))

/-- For admissible `S`, every class `c` and archimedean point `x`, the integral of `u ↦ β_c(u x)`,
`β_c = S.classCutoff c`, read as a complex function, over the product of the groups `besselU` is
`S.unipotentCovolume`. -/
lemma integral_classCutoff_eq_unipotentCovolume (c : S.Classes) (x : InfinitePlace E → 𝔰.G₁) :
    ∫ u : InfinitePlace E → besselU (T := 𝔰.middleGram (1 : ℂ)),
      ((S.classCutoff c fun v : InfinitePlace E ↦ u v * x v).toReal : ℂ)
        ∂(.pi fun _ : InfinitePlace E ↦ 𝔰.besselHaar) = S.unipotentCovolume := by
  rw [integral_complex_ofReal, integral_toReal (Measurable.aemeasurable (by fun_prop))
      (ae_lt_top (by fun_prop) (by simp [lintegral_classCutoff_eq_unipotentCovolume])),
    lintegral_classCutoff_eq_unipotentCovolume, toReal_ofReal S.unipotentCovolume_pos.le]

/-! ### Change of weight and moving blocks -/

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- Let `S` be a filling of shape `𝔰` over the CM field `E`. For stable `T`, the set of terms of `T`
over `(c, s, c')` is stable under `γ ↦ u γ u'⁻¹` for `u` in `S.classUnipotent c` and `u'` in
`S.classUnipotent c'`. -/
lemma mul_mul_inv_mem_inter_termsOver (hT : S.IsStable T) {c : S.Classes} {s : S.ResidueGL}
    {c' : S.Classes} (u : S.classUnipotent c) (u' : S.classUnipotent c') {γ : S.G E}
    (hγ_mem : γ ∈ T ∩ S.termsOver c s c') : u.1 * γ * u'.1⁻¹ ∈ T ∩ S.termsOver c s c' := by
  obtain ⟨hu, hu_over⟩ := u.2
  obtain ⟨hu', hu'_over⟩ := (u'⁻¹).2
  exact ⟨by simpa using (hT u.1⁻¹ (inv_mem hu) u'.1⁻¹ hu' γ).2 hγ_mem.1,
    by simpa [mul_assoc] using termsOver.mul (.mul hu_over hγ_mem.2) hu'_over⟩

/-- Let the group `H`, with an s-finite inversion invariant measure `η`, act measurably on `Z` and
preserve the s-finite measure `μ`. A cutoff (`IsCutoff η β`) is a measurable `β : Z → [0, ∞]` with
`∫ β (u • p) dη(u) = 1` for every `p`. Two cutoffs `β`, `β'` give every invariant measurable `F` the
same integral: `∫ β F dμ = ∫ β' F dμ`. -/
lemma lintegral_mul_eq_of_isCutoff {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z] [Group H]
    [MulAction H Z] [MeasurableInv H] [MeasurableSMul₂ H Z] {η : Measure H} [SFinite η]
    [IsInvInvariant η] {μ : Measure Z} [SFinite μ] [SMulInvariantMeasure H Z μ] {β β' F : Z → ℝ≥0∞}
    (hβ : IsCutoff η β) (hβ' : IsCutoff η β') (hF : Measurable F)
    (h_inv : ∀ (u : H) (p : Z), F (u • p) = F p) :
    ∫⁻ p : Z, β p * F p ∂μ = ∫⁻ p : Z, β' p * F p ∂μ := by
  -- Under both weighted measures `F` has the law it has on the quotient.
  simpa [lintegral_withDensity_eq_lintegral_mul μ hβ.1 hF,
    lintegral_withDensity_eq_lintegral_mul μ hβ'.1 hF] using
    ((identDistrib_orbitMeasure (μ := μ) hβ hF h_inv).symm.trans
      (identDistrib_orbitMeasure hβ' hF h_inv)).lintegral_eq

/-- Let `S` be admissible and `T` stable. Let `X` be the set of `γ ∈ T` with h_c⁻¹ γ h_c' integral
of reduction `s` (`termsOver`). Let `φ γ y ∈ [0, ∞]` be measurable in `y` with sum `1` on each orbit
`(u γ u'⁻¹, u y)`, `γ ∈ X`, of `classUnipotent c × classUnipotent c'`; the first factor is the group
of rational `u` in `besselU` with h_c⁻¹ u h_c in the principal congruence subgroup of level `S.M`.
Then (a) the integrals `∫ φ γ y • besselKernel side γ y dy`, `γ ∈ X`, sum to the block; (b) each
integrand is integrable; (c) `∑_γ ∫ φ ‖kernel - cut kernel‖` is at most `ν b ^ (-k³ f) / 2`. Here
`ν = S.unipotentCovolume`, `b` is the size parameter of `S`, `k + 1` is the size of the middle block
of the basis (`k = 𝔰.k`) and `f` is the number of infinite places. -/
lemma hasSum_amplitudeSum_of_cutoff (hT : S.IsStable T) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) (φ : S.G E → (InfinitePlace E → 𝔰.G₁) → ℝ≥0∞)
    (h_sum : ∀ γ ∈ T ∩ S.termsOver c s c', ∀ y : InfinitePlace E → 𝔰.G₁,
      ∑' u : S.classUnipotent c × S.classUnipotent c', φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1)
    (hφ_meas : ∀ γ : S.G E, Measurable (φ γ)) :
    -- (a)
    HasSum (fun γ : ↥(T ∩ S.termsOver c s c') ↦
        ∫ y : InfinitePlace E → 𝔰.G₁, (φ γ y).toReal • S.besselKernel side γ y)
      (S.amplitudeSum side T c s c') ∧
    -- (b)
    (∀ γ : ↥(T ∩ S.termsOver c s c'),
      Integrable fun y : InfinitePlace E → 𝔰.G₁ ↦ (φ γ y).toReal • S.besselKernel side γ y) ∧
    -- (c)
    ∑' γ : ↥(T ∩ S.termsOver c s c'), ∫⁻ y : InfinitePlace E → 𝔰.G₁,
      φ γ y * ‖S.besselKernel side γ y - S.besselKernel .cut γ y‖ₑ ≤
      .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  -- `Δ = S.classUnipotent c × S.classUnipotent c'` acts on pairs `(γ, y)` by `(u γ u'⁻¹, u y)`,
  -- keeping the measure `ρ` and the kernel. Both `β₀ = β_c β_c'` and `φ` are cutoffs for this
  -- action, so they give an invariant function the same integral; the convergence and the tail
  -- bound for `β₀` pass to `φ`.
  let X : Set (S.G E) := T ∩ S.termsOver c s c'
  let Δ : Type := S.classUnipotent c × S.classUnipotent c'
  let Y : Type := InfinitePlace E → 𝔰.G₁
  let : MeasurableSpace (S.G E) := ⊤
  let : MulAction Δ X :=
    { smul u γ := ⟨u.1 * γ * u.2⁻¹, mul_mul_inv_mem_inter_termsOver hT u.1 u.2 γ.2⟩
      one_smul := by simp [HSMul.hSMul, Δ]
      mul_smul := by simp [HSMul.hSMul, Δ, mul_assoc] }
  -- The first component of `u` acts on `y` by left translation.
  let action : MulAction Δ Y := .compHom _ ((S.ratToInf.domRestrict _).comp (.fst _ _))
  let : SMul Δ Y := action.toSMul
  let ρ : Measure (X × Y) := Measure.count.prod volume
  have preserving (u : Δ) : MeasurePreserving (u • ·) ρ ρ :=
    (measurePreserving_count (MulAction.toPerm u)).prod (measurePreserving_mul_left ..)
  have : MeasurableSMul₂ Δ (X × Y) :=
    ⟨measurable_from_prod_countable_right fun u ↦ (preserving u).measurable⟩
  have : SMulInvariantMeasure Δ (X × Y) ρ :=
    ((smulInvariantMeasure_tfae Δ ρ).out 7 1).1 preserving
  let kernel (τ : FullOrCut) (p : X × Y) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
    S.besselKernel τ p.1 p.2
  have kernel_smul (τ : FullOrCut) (u : Δ) (p : X × Y) : kernel τ (u • p) = kernel τ p := by
    simp +zetaDelta [besselKernel, HSMul.hSMul, besselFn_mul_of_mem_classUnipotent, mul_assoc,
      SMul.smul]
  have kernel_meas (τ : FullOrCut) : Measurable (kernel τ) := by fun_prop [besselKernel]
  let β₀ (p : X × Y) : ℝ≥0∞ := S.classCutoff c p.2 * S.classCutoff c' ((S.ratToInf p.1)⁻¹ * p.2)
  have β₀_cutoff : IsCutoff (count : Measure Δ) β₀ := by
    refine ⟨by fun_prop, fun p ↦ ?_⟩
    simp +zetaDelta [HSMul.hSMul, tsum_classCutoff_eq_one, mul_assoc, lintegral_count,
      ENNReal.tsum_prod', ENNReal.tsum_mul_left, SMul.smul]
  have φ_cutoff : IsCutoff (count : Measure Δ) fun p : X × Y ↦ φ p.1 p.2 :=
    ⟨measurable_from_prod_countable_right fun γ ↦ hφ_meas γ,
      fun p ↦ (lintegral_count _).trans (h_sum p.1 p.1.2 p.2)⟩
  -- The integral of an invariant `F` against any cutoff is at most the sum of integrals for `β₀`.
  have lintegral_le {β F : X × Y → ℝ≥0∞} (hβ : IsCutoff (count : Measure Δ) β)
      (hF : Measurable F) (h_inv : ∀ (u : Δ) (p : X × Y), F (u • p) = F p) :
      ∫⁻ p, β p * F p ∂ρ ≤ ∑' γ : X, ∫⁻ y, β₀ (γ, y) * F (γ, y) :=
    (lintegral_mul_eq_of_isCutoff hβ β₀_cutoff hF h_inv).le.trans
      ((lintegral_prod_le _).trans_eq (lintegral_count _))
  have integrable {β : X × Y → ℝ≥0∞} (hβ : IsCutoff (count : Measure Δ) β) :
      Integrable (fun p ↦ (β p).toReal • kernel side p) ρ :=
    integrable_toReal_smul hβ.1 (kernel_meas side).aestronglyMeasurable
      ((lintegral_le hβ (kernel_meas side).enorm (by simp [kernel_smul])).trans_lt
        ((ENNReal.le_tsum c').trans_lt (tsum_amplitudeMajorant_lt_top T c s)))
  -- Fubini: for every cutoff the integrals over `y` sum to that of the kernel over the quotient.
  have hasSum {β : X × Y → ℝ≥0∞} (hβ : IsCutoff (count : Measure Δ) β) :
      HasSum (fun γ : X ↦ ∫ y, (β (γ, y)).toReal • S.besselKernel side γ y)
        (∫ p, kernel side p ∂orbitMeasure (count : Measure Δ) ρ) := by
    rw [hβ.integral_orbitMeasure (kernel_smul side) (kernel_meas side),
      integral_prod _ (integrable hβ)]
    exact (hasSum_integral_measure (integrable hβ).integral_prod_left).congr_fun
      (by simp [kernel, Y])
  have block_eq :
      S.amplitudeSum side T c s c' = ∫ p, kernel side p ∂orbitMeasure (count : Measure Δ) ρ :=
    (hasSum β₀_cutoff).tsum_eq
  refine ⟨by simpa only [block_eq] using hasSum φ_cutoff,
    ae_count_iff.1 (integrable φ_cutoff).prod_right_ae, ?_⟩
  have diff_meas : Measurable fun p ↦ ‖kernel side p - kernel .cut p‖ₑ := by fun_prop
  calc
    _ = ∫⁻ p, φ p.1 p.2 * ‖kernel side p - kernel .cut p‖ₑ ∂ρ :=
      ((lintegral_prod _ (φ_cutoff.1.mul diff_meas).aemeasurable).trans (lintegral_count _)).symm
    _ ≤ ∑' γ : X, ∫⁻ y, β₀ (γ, y) * ‖kernel side (γ, y) - kernel .cut (γ, y)‖ₑ :=
      lintegral_le φ_cutoff diff_meas (by simp [kernel_smul])
    _ ≤ _ := (ENNReal.le_tsum c').trans (tsum_lintegral_enorm_besselKernel_sub_cut_le T c s)

/-- Moving a block. Let `S` be admissible and `T` stable. Let `σ` over `(c, t, c₁)` and `σ'` over
`(c', t', c₁')` be rational elements (`(S.ratMiddle E).G` is the group `S.G E`) of the Bessel
subgroup `besselS`. Suppose that `γ ∈ T ↔ σ γ σ'⁻¹ ∈ T`. If a continuous linear map `L` takes the
kernel at `(γ, y)` to the kernel at `(σ γ σ'⁻¹, σ y)`, then `L` takes the block over `(c₁, s, c₁')`
to that over `(c, t s t'⁻¹, c')`. -/
lemma amplitudeSum_mul_mul_inv (hT : S.IsStable T) {c : S.Classes} {t : S.ResidueGL}
    {c₁ : S.Classes} {σ : (S.ratMiddle E).G} {c' : S.Classes} {t' : S.ResidueGL} {c₁' : S.Classes}
    {σ' : (S.ratMiddle E).G} (hσ : σ ∈ besselS) (hσ_over : σ ∈ S.termsOver c t c₁)
    (hσ' : σ' ∈ besselS) (hσ'_over : σ' ∈ S.termsOver c' t' c₁')
    (hT_iff : ∀ γ : S.G E, γ ∈ T ↔ σ * γ * σ'⁻¹ ∈ T)
    (L : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) →L[ℂ]
      EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord))
    (hL : ∀ (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁),
      S.besselKernel side (σ * γ * σ'⁻¹) (S.ratToInf σ * y) = L (S.besselKernel side γ y))
    (s : S.ResidueGL) :
    S.amplitudeSum side T c (t * s * t'⁻¹) c' = L (S.amplitudeSum side T c₁ s c₁') := by
  -- The weight `β_c(σ y) β_c'(σ' γ⁻¹ y)` has orbit sums `1`, so
  -- `hasSum_amplitudeSum_of_cutoff` computes the right side with it; then substitute
  -- `γ ↦ σ γ σ'⁻¹` and `y ↦ σ y`.
  let φ (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ :=
    S.classCutoff c (S.ratToInf σ * y) * S.classCutoff c' (S.ratToInf σ' * ((S.ratToInf γ)⁻¹ * y))
  -- The orbit sums of `φ` are products of those of the two translated cutoffs, hence `1`.
  have φ_sum (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
      ∑' u : S.classUnipotent c₁ × S.classUnipotent c₁',
        φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 := by
    simp [φ, tsum_classCutoff_ratToInf_mul_eq_one hσ hσ_over,
      tsum_classCutoff_ratToInf_mul_eq_one hσ' hσ'_over,
      mul_assoc, ENNReal.tsum_prod', ENNReal.tsum_mul_left]
  have φ_meas (γ : S.G E) : Measurable (φ γ) := by fun_prop
  obtain ⟨hasSum, integrable, -⟩ :=
    hasSum_amplitudeSum_of_cutoff (side := side) hT c₁ s c₁' φ (fun γ _ ↦ φ_sum γ) φ_meas
  let move : ↥(T ∩ S.termsOver c₁ s c₁') ≃ ↥(T ∩ S.termsOver c (t * s * t'⁻¹) c') :=
    ((Equiv.mulLeft σ).trans (.mulRight σ'⁻¹)).subtypeEquiv fun γ ↦
      (hT_iff γ).and (mem_termsOver_iff_mul_mul_inv_mem hσ_over hσ'_over)
  refine (move.hasSum_iff.1 ((hasSum.mapL L).congr_fun fun γ ↦ ?_)).tsum_eq
  change S.amplitude side c c' (σ * γ * σ'⁻¹) = L (∫ y, (φ γ y).toReal • S.besselKernel side γ y)
  rw [← L.integral_comp_comm (integrable γ), amplitude,
    ← integral_mul_left_eq_self _ (S.ratToInf σ)]
  simp [φ, ← hL, mul_assoc]

/-- Let `S` be admissible and `T` stable (`IsStable`), and let `side` choose the full or the cut
Bessel function. Let `u`, `u'` in `besselU` be integral finite adelic elements
(`latticeStabilizer`), with reductions `ū`, `ū'` modulo the chosen places (`S.reduction`). Then the
block at `ū s ū'⁻¹` is `ψ(u)⁻¹ ψ(u')` times the block at `s`. Here `ψ = S.unipotentChar` is the
additive character `S.selfDualChar` at the sum of the entries just above the diagonal on the frame
(`simpleRootSum`), divided by the level `S.M`. -/
lemma amplitudeSum_besselU_mul (hT : S.IsStable T) {u u' : S.latticeStabilizer}
    (hu : u.1 ∈ besselU) (hu' : u'.1 ∈ besselU) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    S.amplitudeSum side T c (S.reduction u * s * (S.reduction u')⁻¹) c' =
      ((S.unipotentChar u)⁻¹ * S.unipotentChar u') • S.amplitudeSum side T c s c' := by
  -- Approximate `u`, `u'` modulo `S.principalLevel` by rational `x`, `x'` in `besselU` with the
  -- same character; they lie over `(c, ū, c)` and `(c', ū', c')`. Move the block by them.
  obtain ⟨x, hx, ⟨k, hk⟩, hψ⟩ := exists_rat_approx_unipotentChar_eq c hu
  obtain ⟨x', hx', ⟨k', hk'⟩, hψ'⟩ := exists_rat_approx_unipotentChar_eq c' hu'
  -- `h_c⁻¹ x h_c` is `u` times an element of the kernel of the reduction, and likewise for `x'`.
  have hx_over : x ∈ S.termsOver c (S.reduction u) c := ⟨u * k, by simp_all⟩
  have hx'_over : x' ∈ S.termsOver c' (S.reduction u') c' := ⟨u' * k', by simp_all⟩
  -- The kernel changes by the scalar `ψ(x)⁻¹ ψ(x')`, and so does the block.
  simpa [hψ, hψ'] using amplitudeSum_mul_mul_inv hT
    (mem_partialUnitriangularGroup_of_mem_besselU hx) hx_over
    (mem_partialUnitriangularGroup_of_mem_besselU hx') hx'_over
    (fun γ ↦ (hT x⁻¹ (inv_mem hx) _ (inv_mem hx') γ).symm) (.lsmul ℂ ℂ _)
    (besselKernel_besselU_mul hx hx') s

/-- Let `S` be admissible. If `T` is stable (`S.IsStable T`) and `s` does not agree, that is
`unipotentChar u ≠ unipotentChar u'` for some integral unipotent `u`, `u'` whose reductions satisfy
`ū s = s ū'`, then the amplitude sum `S.amplitudeSum side T c s c'` of the elements of `T` over
`(c, s, c')` vanishes. -/
lemma amplitudeSum_eq_zero_of_not_agrees (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes)
    (hT : S.IsStable T) (hs : ¬S.Agrees s) :
    S.amplitudeSum side T c s c' = 0 := by
  -- For `ū s = s ū'`, `amplitudeSum_besselU_mul` multiplies the block at `s` by `ψ(u)⁻¹ ψ(u')`
  -- without changing it; a nonzero block forces this scalar to be `1`.
  by_contra h_ne
  refine hs fun u u' hu hu' huu' ↦ eq_of_inv_mul_eq_one (smul_left_injective ℂ h_ne ?_)
  simp [← amplitudeSum_besselU_mul hT hu hu', huu']

end GeneralBlocks

/-! ### The identity block -/

open scoped Classical in
/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Let `c`, `c'` be
classes, and let `i`, `j` be tuples of one coordinate index of the Bessel function at each infinite
place (`BesselCoord`). Sum, over the rational points `γ` of the Bessel subgroup `besselS` with h_c⁻¹
γ h_c' integral of reduction `1` (`termsOver`), the integrals
`∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy`, with `W` the full Bessel function and
`β_c = S.classCutoff c`. The `(i, j)` entry of this sum (`amplitudeSum`) is `S.unipotentCovolume`,
the covolume of `S.classUnipotent c` in the real unipotent group, if `c = c'` and `i = j`, and `0`
otherwise. -/
lemma amplitudeSum_besselS_one_eq_ite {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [S.IsAdmissible] [HasPrimitiveRoot5040 E] (c c' : S.Classes) (i j : S.BesselCoord) :
    S.amplitudeSum .full (S.ratMiddle E).besselS c 1 c' (i, j) =
      (if c = c' ∧ i = j then S.unipotentCovolume else 0 : ℝ) := by
  -- Only `γ ∈ S.classUnipotent c` with `c = c'` contribute
  -- (`eq_and_mem_classUnipotent_of_besselS`). By `hasSum_amplitudeSum_of_cutoff` the whole
  -- weight `classCutoff c` may be put on the one term `γ = 1`; unfolding over `besselU` at every
  -- place then leaves `unipotentCovolume` times the product of the local inner products on
  -- `𝖴 \ G₁`.
  obtain hne | rfl := ne_or_eq c c'
  · have : IsEmpty ↥(↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c') :=
      ⟨fun ⟨_, hγ, hγ_over⟩ ↦ hne (eq_and_mem_classUnipotent_of_besselS hγ hγ_over).1⟩
    simp [amplitudeSum, tsum_empty, hne]
  let φ (γ : S.G E) : (InfinitePlace E → 𝔰.G₁) → ℝ≥0∞ := if 1 = γ then S.classCutoff c else 0
  have φ_sum : ∀ γ ∈ ↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c,
      ∀ y : InfinitePlace E → 𝔰.G₁, ∑' u : S.classUnipotent c × S.classUnipotent c,
        φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 := by
    rintro γ ⟨hγ, hγ_over⟩ y
    lift γ to S.classUnipotent c using (eq_and_mem_classUnipotent_of_besselS hγ hγ_over).2
    simp only [φ]
    norm_cast
    -- The default instance size is too small for the two copies of `S.classUnipotent c`.
    set_option synthInstance.maxSize 512 in
      simp [ite_apply, ↓eq_mul_inv_iff_mul_eq, tsum_classCutoff_eq_one, ENNReal.tsum_prod']
  have φ_meas (γ : S.G E) : Measurable (φ γ) := by measurability
  obtain ⟨hasSum, integrable, -⟩ :=
    hasSum_amplitudeSum_of_cutoff (side := .full) isStable_besselS c 1 c φ φ_sum φ_meas
  let F (v : InfinitePlace E) (y : 𝔰.G₁) : ℂ :=
    (S.besselSystem v).besselFn .full y (i v) * starRingEnd ℂ
      ((S.besselSystem v).besselFn .full y (j v))
  have ker_one (y : InfinitePlace E → 𝔰.G₁) :
      S.besselKernel .full 1 y (i, j) = ∏ v, F v (y v) := by
    simp [besselKernel, besselFn, F, prod_mul_distrib]
  -- The character by which `besselU` acts has modulus `1`, so it cancels in `F`.
  have F_mul (v : InfinitePlace E) (u : 𝔰.G₁) (hu : u ∈ besselU) (y : 𝔰.G₁) :
      F v (u * y) = F v y := by
    simp [F, ((S.besselSystem v).isCutPair.isBesselFunction _).map_unipotent_mul u hu, mul_conj',
      mul_mul_mul_comm _ _ (starRingEnd _ _)]
  have one_term : 1 ∈ ↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c :=
    ⟨besselS.one_mem, (S.classUnipotent c).one_mem.2⟩
  have others (γ : ↥(↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c)) (hγ : γ ≠ ⟨1, one_term⟩) :
      ∫ y, (φ γ.1 y).toReal • S.besselKernel .full γ y = 0 := by
    simp [φ, show 1 ≠ γ.1 from fun h ↦ hγ (Subtype.ext h.symm)]
  have h_int_prod : Integrable fun y : InfinitePlace E → 𝔰.G₁ ↦
      (S.classCutoff c y).toReal * ∏ v, F v (y v) := by
    simpa [φ, ker_one] using (integrable ⟨1, one_term⟩).eval_piLp (i, j)
  calc
    _ = ∫ y, (S.classCutoff c y).toReal * ∏ v, F v (y v) := by
      rw [hasSum.unique (hasSum_single ⟨1, one_term⟩ others),
        eval_integral_piLp (integrable ⟨1, one_term⟩).eval_piLp]
      simp [φ, ker_one]
    _ = ∫ x, S.unipotentCovolume * ∏ v, F v (x v) ∂.pi fun _ ↦ besselQuotMeasure := by
      rw [← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar).integral_integral_comp h_int_prod]
      simp [Pi.mul_def, F_mul, integral_mul_const, integral_const_mul,
        integral_classCutoff_eq_unipotentCovolume]
    _ = S.unipotentCovolume * ∏ v, if i v = j v then 1 else 0 := by
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
      exact congrArg _ (prod_congr rfl fun v _ ↦ (S.besselSystem v).orthonormal (i v) (j v))
    _ = _ := by simp [Fintype.prod_boole, funext_iff, apply_ite ofReal]

end New.Filling

end AmplitudeSums
