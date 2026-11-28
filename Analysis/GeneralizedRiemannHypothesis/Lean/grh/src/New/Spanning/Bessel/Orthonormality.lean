import Lib.DiscreteSeries.Bessel.SchurBound
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import New.Spanning.Bessel.Basic

/-!
# Normalisation of a Bessel function and of its cut

Let `W` be an integrable Bessel function on G₁ whose type is an irreducible representation of the
compact group `U(κ)`. The operator `∫ W ⊗ W^*` over 𝖴∖G₁ commutes with this representation, so it
is a scalar, and its trace is the squared L² norm of `W`.

* `New.BesselSystem.orthonormal`: for the full function of a Bessel system the operator is `1`, so
  its coordinates are orthonormal in L²(𝖴∖G₁).
* `New.IsCutPair.exists_integral_cut_mul_conj_eq`: for the cut function it is a scalar between `0`
  and `1`.
* `New.IsCutPair.lintegral_sq_inner_cut_le`: the upper bound, tested on a vector.

Notions from other files:

* `New.Shape.G₁`: the unitary group G₁ of the complex hermitian form given by a shape; `U(κ)` is
  the unitary group of the standard positive form on the index set κ of the shape, embedded in G₁
  by `New.RealPlace.embedH`.
* `New.besselQuotMeasure`: the measure on G₁ that computes integrals over 𝖴∖G₁, where 𝖴 is the
  unipotent group `New.Shape.Form.besselU`.
* `New.IsBesselFunction`: a bounded measurable function on G₁ that transforms on the left by a
  fixed character under 𝖴 and by a unitary representation, its type, under `U(κ)`.
* `New.IsCutPair`: a Bessel function (`.full`) whose squared L² norm is the dimension of its
  value space, and its cut (`.cut`): a Bessel function that vanishes outside a region of bounded
  size, is close to it in L² and agrees with it where the size is small.
* `New.BesselSystem`: a cut pair of irreducible type, with further bounds.

## Relation to the literature

See `New.Spanning.Bessel.CutTailBound` for related work.
-/

open Matrix MeasureTheory Complex Subgroup ComplexConjugate

/-- Let `W : G₁ → ℂ^I` be a Bessel function: a bounded measurable function on the unitary group G₁
such that `W (u y) = ψ(u) W y` for `u` in the unipotent subgroup 𝖴, with ψ a fixed character, and
`W (h y) = rep h (W y)` for `h` in the compact unitary group `U(κ)`, which sits in G₁ by
`RealPlace.embedH`. Translating `W` on the left by `s ∈ U(κ)` does not change the integral of
`W y i * conj (W y j)` over 𝖴∖G₁. -/
lemma New.IsBesselFunction.integral_mul_conj_embedH_mul {𝔰 : Shape} {I : Type} [Fintype I]
    [DecidableEq I] {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {W : 𝔰.G₁ → EuclideanSpace ℂ I} (hW : IsBesselFunction rep W)
    (s : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (i j : I) :
    ∫ y : 𝔰.G₁, W (RealPlace.embedH s * y) i * conj (W (RealPlace.embedH s * y) j)
        ∂besselQuotMeasure =
      ∫ y : 𝔰.G₁, W y i * conj (W y j) ∂besselQuotMeasure := by
  -- The element normalises 𝖴, conjugation by it keeps the Haar measure of 𝖴, and the integrand
  -- is invariant under 𝖴 because the characters cancel.
  have h_meas : Measurable fun y ↦ W y i * conj (W y j) := by
    have : StronglyMeasurable W := hW.stronglyMeasurable
    fun_prop
  have h_mem_besselS : RealPlace.embedH s ∈ Shape.Form.besselS :=
    mem_partialUnitriangularGroup_of_mem_floorGroup (toBesselH_mem s)
  have h_inv (u : (𝔰.middleGram (1 : ℂ)).besselU) (y : 𝔰.G₁) :
      W (u • y) i * conj (W (u • y) j) = W y i * conj (W y j) := by
    simp [Subgroup.smul_def, hW.map_unipotent_mul, mul_mul_mul_comm _ (W y i), mul_conj']
  refine (identDistrib_orbitMeasure_comp (F := fun y ↦ W y i * conj (W y j))
    (RealPlace.measurePreserving_conj_bessel mem_besselU besselS_le_normalizer_besselU
      h_mem_besselS)
    (measurePreserving_mul_left _ (RealPlace.embedH s)) (fun u y ↦ ?_) h_inv h_meas).integral_eq
  -- Equivariance: `s * (u * y) = (s * u * s⁻¹) * (s * y)`.
  simp [Subgroup.smul_def, ← mul_assoc]

/-- Let `W : 𝔰.G₁ → ℂ^I` be a Bessel function of type `rep`: it is bounded and measurable,
`W (u y) = ψ(u) W y` for `u` in the unipotent subgroup 𝖴 of `𝔰.G₁`, with ψ a fixed character, and
`W (h y) = rep h (W y)` for `h` in the compact unitary group `U(κ)` = `U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)`
inside `𝔰.G₁`, with `rep` a unitary representation. Suppose that `W` is integrable over 𝖴∖G₁ and
that every matrix commuting with all `rep h` is scalar. Then the operator `∫ W ⊗ W^*` over 𝖴∖G₁ is
the scalar `‖W‖₂ ^ 2 / |I|`. -/
lemma New.IsBesselFunction.integral_mul_conj_eq {𝔰 : Shape} {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {W : 𝔰.G₁ → EuclideanSpace ℂ I} (hW : IsBesselFunction rep W)
    (h_int : Integrable W besselQuotMeasure)
    (h_irred : ∀ M : Matrix I I ℂ,
      (∀ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), Commute M (rep h : Matrix I I ℂ)) →
        M ∈ Set.range (scalar I))
    (i j : I) :
    ∫ y : 𝔰.G₁, W y i * conj (W y j) ∂besselQuotMeasure =
      if i = j then (((∫ y : 𝔰.G₁, ‖W y‖ ^ 2 ∂besselQuotMeasure) / Fintype.card I : ℝ) : ℂ)
      else 0 := by
  -- The matrix `M` of these integrals commutes with `rep`, so it is scalar; its trace is the
  -- squared norm of the function.
  let M : Matrix I I ℂ := of fun k l ↦ ∫ y, W y k * conj (W y l) ∂besselQuotMeasure
  have h_int_prod (k l : I) : Integrable (fun y ↦ W y k * conj (W y l)) besselQuotMeasure :=
    (h_int.eval_piLp k).mul_of_top_left (hW.memLp_top.eval_piLp l).star
  have h_comm (s : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) : Commute M (rep s : Matrix I I ℂ) := by
    let R : Matrix I I ℂ := rep s
    suffices h_conj : R * M * star R = M from
      ((commute_unitary_iff_star_right_conjugate (SetLike.coe_mem (rep s))).2 h_conj).symm
    ext p q
    have h_expand (y : 𝔰.G₁) :
        W (RealPlace.embedH s * y) p * conj (W (RealPlace.embedH s * y) q) =
          ∑ l, ∑ k, R p k * (W y k * conj (W y l)) * conj (R q l) := by
      simp [R, hW.map_unitary_mul, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc,
        mul_comm (conj (W y _))]
    calc (R * M * star R) p q
        = ∑ l, ∑ k, R p k * M k l * conj (R q l) := by simp [mul_apply, Finset.sum_mul]
      _ = ∫ y, ∑ l, ∑ k, R p k * (W y k * conj (W y l)) * conj (R q l) ∂besselQuotMeasure := by
        simp (disch := fun_prop) only [M, of_apply, integral_finsetSum, integral_mul_const,
          integral_const_mul]
      _ = M p q := by simp only [← h_expand, hW.integral_mul_conj_embedH_mul, M, of_apply]
  have h_trace : M.trace = (∫ y, ‖W y‖ ^ 2 ∂besselQuotMeasure : ℝ) := by
    calc M.trace = ∫ y, ∑ k, W y k * conj (W y k) ∂besselQuotMeasure :=
        (integral_finsetSum _ fun k _ ↦ h_int_prod k k).symm
      _ = _ := by simp [mul_conj', PiLp.norm_sq_eq_of_L2, ← integral_complex_ofReal]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, scalar I c = M := h_irred M h_comm
  have h_scalar : c = (∫ y, ‖W y‖ ^ 2 ∂besselQuotMeasure : ℝ) / Fintype.card I := by
    simp [← h_trace, ← hc]
  calc _ = scalar I c i j := (congrFun₂ hc i j).symm
    _ = _ := by simp [h_scalar, diagonal_apply]

/-- The coordinates of the full function of a Bessel system `B` are orthonormal in L²(𝖴∖G₁): the
integral of `B.besselFn .full y i` times the conjugate of `B.besselFn .full y j` for the measure
`besselQuotMeasure` is 1 if `i = j` and 0 otherwise. -/
lemma New.BesselSystem.orthonormal {𝔰 : Shape} {b : ℝ} {f : ℕ} (B : BesselSystem 𝔰 b f)
    (i j : B.Index) :
    ∫ y : 𝔰.G₁, B.besselFn .full y i * conj (B.besselFn .full y j) ∂besselQuotMeasure =
      if i = j then 1 else 0 := by
  have hW : IsBesselFunction B.rep (B.besselFn .full) := B.isCutPair.isBesselFunction .full
  have h_mass : ∫ y, ‖B.besselFn .full y‖ ^ 2 ∂besselQuotMeasure = Fintype.card B.Index := by
    simpa [lintegral_enorm_sq B.isCutPair.integrable hW.memLp_top] using
      B.isCutPair.lintegral_sq_full_eq
  rw [hW.integral_mul_conj_eq B.isCutPair.integrable B.irreducible, h_mass]
  simp

/-- Let `W` be a cut pair on G₁: a Bessel function `W .full` and its cut `W .cut`, a Bessel function
that vanishes outside a region whose size is bounded by a power of `b`. By hypothesis a power of the
scaled size, with an exponent proportional to `f` and a base at least 1, times the norm of either
function lies below a majorant `A` of finite integral. Hence the cut function is integrable over
𝖴∖G₁. -/
lemma New.IsCutPair.integrable_cut {𝔰 : Shape} {I : Type} [Fintype I] [DecidableEq I] {b : ℝ}
    {f : ℕ} {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {W : FullOrCut → C(𝔰.G₁, EuclideanSpace ℂ I)} (hW : IsCutPair b f rep W) :
    Integrable (W .cut) besselQuotMeasure := by
  -- The function lies below the decay majorant `A`, whose integral is finite.
  obtain ⟨A, a, hA⟩ : ∃ (A : 𝔰.G₁ → ENNReal) (a : ENNReal), IsDecayMajorant b f W A a :=
    hW.exists_majorant
  have h_le (y : 𝔰.G₁) : ‖W .cut y‖ₑ ≤ A y := by
    have h_one_le_weight : 1 ≤ ENNReal.ofReal (scaledBesselLength y b ^ (3 * 𝔰.r ^ 3 * f)) :=
      ENNReal.one_le_ofReal.2 (one_le_pow₀ (one_le_scaledBesselLength y b))
    exact (le_mul_of_one_le_left' h_one_le_weight).trans (hA.pow_mul_enorm_le .cut y)
  have h_fin : ∫⁻ y, A y ∂besselQuotMeasure < ⊤ := by
    obtain rfl | ha := eq_or_ne a 0
    · have h_zero (y : 𝔰.G₁) : A y = 0 := le_zero_iff.1 (hA.le_bound y)
      simp [h_zero]
    · have h_mul : a * ∫⁻ y, A y ∂besselQuotMeasure < ⊤ :=
        hA.bound_mul_lintegral_le.trans_lt (by finiteness)
      exact ENNReal.lt_top_of_mul_ne_top_right h_mul.ne ha
  exact ⟨(W .cut).continuous.aestronglyMeasurable, (lintegral_mono h_le).trans_lt h_fin⟩

/-- Let `W` be a cut pair of type `rep` with values in `ℂ^I`: a Bessel function `W .full` and its
cut `W♭ = W .cut`, a Bessel function that vanishes outside a region of size bounded in terms of `b`.
Suppose that `rep` is irreducible: every matrix that commutes with all `rep h` is scalar. Then the
operator `∫ W♭ ⊗ W♭^*` over 𝖴∖G₁ is a scalar `c` between `0` and `1`. -/
theorem New.IsCutPair.exists_integral_cut_mul_conj_eq {𝔰 : Shape} {I : Type} [Fintype I]
    [DecidableEq I] [Nonempty I] {b : ℝ} {f : ℕ}
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {W : FullOrCut → C(𝔰.G₁, EuclideanSpace ℂ I)} (hW : IsCutPair b f rep W)
    (h_irred : ∀ M : Matrix I I ℂ,
      (∀ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), Commute M (rep h : Matrix I I ℂ)) →
        M ∈ Set.range (scalar I)) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, ∀ i j : I,
      ∫ y : 𝔰.G₁, W .cut y i * conj (W .cut y j) ∂besselQuotMeasure =
        if i = j then (c : ℂ) else 0 := by
  have h_bessel : IsBesselFunction rep (W .cut) := hW.isBesselFunction .cut
  have h_mass : ∫ y, ‖W .cut y‖ ^ 2 ∂besselQuotMeasure ≤ Fintype.card I := by
    simpa [lintegral_enorm_sq hW.integrable_cut h_bessel.memLp_top] using hW.lintegral_sq_cut_le
  refine ⟨(∫ y, ‖W .cut y‖ ^ 2 ∂besselQuotMeasure) / Fintype.card I, ⟨?_, ?_⟩,
    h_bessel.integral_mul_conj_eq hW.integrable_cut h_irred⟩
  · positivity
  · exact div_le_one_of_le₀ h_mass (Nat.cast_nonneg _)

/-- Let `W` be a cut pair of type `rep` with values in `ℂ^I`: a Bessel function `W .full` and its
cut `W♭ = W .cut`, both transforming on the left by a character under the unipotent group 𝖴 and by
`rep` under `U(κ)`, with squared L² norm over 𝖴∖G₁ at most `|I|`; `b` is the parameter of the length
at which `W` is cut, `f` the rate of decay in the length. Suppose that every matrix commuting with
all `rep h` is scalar. Then for every vector `v` the integral of `|⟪v, W♭ y⟫| ^ 2` over 𝖴∖G₁ is at
most `‖v‖ ^ 2`. -/
theorem New.IsCutPair.lintegral_sq_inner_cut_le {𝔰 : Shape} {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] {b : ℝ} {f : ℕ} {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {W : FullOrCut → C(𝔰.G₁, EuclideanSpace ℂ I)} (hW : IsCutPair b f rep W)
    (h_irred : ∀ M : Matrix I I ℂ,
      (∀ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), Commute M (rep h : Matrix I I ℂ)) →
        M ∈ Set.range (scalar I))
    (v : EuclideanSpace ℂ I) :
    ∫⁻ y : 𝔰.G₁, ‖inner ℂ v (W .cut y)‖ₑ ^ 2 ∂besselQuotMeasure ≤ ‖v‖ₑ ^ 2 := by
  -- The operator is a scalar `c ≤ 1`, so the integral is `c * ‖v‖ ^ 2`.
  have h_int : Integrable (W .cut) besselQuotMeasure := hW.integrable_cut
  have h_memLp_top : MemLp (W .cut) ⊤ besselQuotMeasure := (hW.isBesselFunction .cut).memLp_top
  obtain ⟨c, ⟨-, hc_le⟩, h_scalar⟩ : ∃ c ∈ Set.Icc (0 : ℝ) 1, ∀ i j : I,
      ∫ y : 𝔰.G₁, W .cut y i * conj (W .cut y j) ∂besselQuotMeasure =
        if i = j then (c : ℂ) else 0 := hW.exists_integral_cut_mul_conj_eq h_irred
  have h_int_prod (i j : I) :
      Integrable (fun y ↦ W .cut y i * conj (W .cut y j)) besselQuotMeasure :=
    (h_int.eval_piLp i).mul_of_top_left (h_memLp_top.eval_piLp j).star
  have h_expand (y : 𝔰.G₁) : ((‖inner ℂ v (W .cut y)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, conj (v i) * v j * (W .cut y i * conj (W .cut y j)) := by
    rw [ofReal_pow, ← mul_conj', PiLp.inner_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [RCLike.inner_apply, map_mul, conj_conj]
    ring
  have h_integral : ∫ y, ‖inner ℂ v (W .cut y)‖ ^ 2 ∂besselQuotMeasure = c * ‖v‖ ^ 2 := by
    refine ofReal_injective ?_
    calc ((∫ y, ‖inner ℂ v (W .cut y)‖ ^ 2 ∂besselQuotMeasure : ℝ) : ℂ)
        = ∑ i, ∑ j, conj (v i) * v j *
            ∫ y, W .cut y i * conj (W .cut y j) ∂besselQuotMeasure := by
          simp (disch := fun_prop) only [← integral_complex_ofReal, h_expand, integral_finsetSum,
            integral_const_mul]
      _ = ∑ i, conj (v i) * v i * c := by simp [h_scalar]
      _ = ((c * ‖v‖ ^ 2 : ℝ) : ℂ) := by
          simp [conj_mul', PiLp.norm_sq_eq_of_L2, Finset.sum_mul, mul_comm (c : ℂ)]
  grw [lintegral_enorm_sq (h_int.const_inner v) (h_memLp_top.const_inner v), h_integral, hc_le,
    one_mul, ENNReal.ofReal_pow (norm_nonneg v), ofReal_norm]
