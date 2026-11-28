import New.Spanning.RemainingTerms.OneRealPlace
import New.Spanning.Unfolding.AmplitudeSums

/-!
# Schur's test: Cauchy–Schwarz and integration in stages

The amplitude majorant of a term is bounded by Cauchy–Schwarz with a weight that is inverted when
the two frames are exchanged. The resulting integrals are bounded by a mean over the unipotent
elements that fix the frame. The frame is the list of basis vectors e₁, …, e_ϱ, z of the hermitian
space: one isotropic vector from each hyperbolic plane and the vector z of negative norm.

## Main definitions and results

* `New.Filling.boxCutoff`: the cutoff restricted to the set `New.Filling.boxedPoints`.
* `New.Filling.besselCutNormSq`: the squared norm of the cut Bessel function.
* `New.Filling.amplitudeMajorant_sq_le`: Cauchy–Schwarz with the weight `New.Filling.schurWeight`, a
  boxed cutoff times powers of `New.volumeRatio`, bounds the square of
  `New.Filling.amplitudeMajorant` by a product of two integrals `New.Filling.schurIntegral`.
* `New.Filling.lintegral_boxCutoff_le_of_average`: integration in stages.

Notions from other files:
* `New.Filling.classCutoff`: the cutoff of a class at the infinite places.
* `besselU0`: the unipotent elements that fix the frame; `classUnipotent₀ c` is the group of
  rational such elements in the class `c`.
-/

noncomputable section

open MeasureTheory Fintype Subgroup

namespace New.Filling

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape}

/-- The cutoff of the class `c` at the infinite places, restricted to the boxed points: the reduced
points with every component in the cut. -/
def boxCutoff (S : Filling E 𝔰) (c : S.Classes) :
    (NumberField.InfinitePlace E → 𝔰.G₁) → ENNReal :=
  S.boxedPoints.indicator (S.classCutoff c)

/-- The squared norm of the cut Bessel function at a point `y` at the infinite places: the product
over the places `v` of the squared norms of the local cut Bessel functions at `y v`. -/
def besselCutNormSq (S : Filling E 𝔰) (y : NumberField.InfinitePlace E → 𝔰.G₁) : ENNReal :=
  ∏ v : NumberField.InfinitePlace E, ‖(S.besselSystem v).besselFn .cut (y v)‖ₑ ^ 2

/-- The weight of Schur's test for the class `c` and the rational element `γ`: the product over the
places `v` of `ν_v ^ (-(k + i))`, where `ν_v` is the ratio of the volumes of the projections of
the frame of `γ` and of the standard frame to the negative space of `y v`, times the boxed cutoff of
`c` at `γ⁻¹ y`. The natural number `i`, the shift, only changes this exponent. -/
def schurWeight (S : Filling E 𝔰) (c : S.Classes) (γ : S.G E) (i : ℕ)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) : ENNReal :=
  S.boxCutoff c ((S.ratToInf γ)⁻¹ * y) *
    ∏ v : NumberField.InfinitePlace E,
      ENNReal.ofReal ((volumeRatio (S.ratToInf γ v) (y v))⁻¹ ^ (𝔰.k + i))

/-- One of the two factors that the Cauchy–Schwarz inequality gives in Schur's test: the integral
of the boxed cutoff of `c`, the squared norm of the cut Bessel function and the weight for `c'`
and `γ` with shift `i`. -/
def schurIntegral (S : Filling E 𝔰) (c c' : S.Classes) (γ : S.G E) (i : ℕ) : ENNReal :=
  ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁,
    S.boxCutoff c y * S.besselCutNormSq y * S.schurWeight c' γ i y

variable {S : Filling E 𝔰}

omit [HasPrimitiveRoot5040 E] in
/-- Let `S` be data of the filling theorem over the CM field `E`, let `γ` be a rational element of
the unitary group and `y` a point at the infinite places. If the cut Bessel kernel of `γ`, the
tensor of the cut Bessel functions at `y` and at `γ⁻¹ y`, is nonzero, then at every infinite place
`v` both components lie in the cut. By definition `InCut g b` says exactly that
`besselLength g ≤ b ^ (6 * 𝔰.n + 2)`. -/
lemma inCut_of_besselKernel_ne_zero {γ : S.G E} {y : NumberField.InfinitePlace E → 𝔰.G₁}
    (h_kernel : S.besselKernel .cut γ y ≠ 0) (v : NumberField.InfinitePlace E) :
    InCut (y v) S.b ∧ InCut (((S.ratToInf γ)⁻¹ * y) v) S.b := by
  -- All local factors at `y` and at `γ⁻¹ y` are nonzero, and each vanishes outside the cut.
  rw [← enorm_ne_zero, enorm_besselKernel, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.prod_ne_zero_iff] at h_kernel
  obtain ⟨h_at_y, h_at_γy⟩ := h_kernel
  have h_factors : (S.besselSystem v).besselFn .cut (y v) ≠ 0 ∧
      (S.besselSystem v).besselFn .cut (((S.ratToInf γ)⁻¹ * y) v) ≠ 0 :=
    ⟨enorm_ne_zero.1 (h_at_y v (Finset.mem_univ v)),
      enorm_ne_zero.1 (h_at_γy v (Finset.mem_univ v))⟩
  exact h_factors.imp ((S.besselSystem v).isCutPair.inCut_of_ne_zero _)
    ((S.besselSystem v).isCutPair.inCut_of_ne_zero _)

@[fun_prop]
lemma measurable_boxCutoff {c : S.Classes} [S.IsAdmissible] : Measurable (S.boxCutoff c) :=
  (measurable_classCutoff c).indicator measurableSet_boxedPoints

omit [HasPrimitiveRoot5040 E] in
@[fun_prop]
lemma measurable_besselCutNormSq : Measurable S.besselCutNormSq := by
  fun_prop [besselCutNormSq]

/-- The weight of Schur's test is measurable. -/
@[fun_prop]
lemma measurable_schurWeight {c : S.Classes} {γ : S.G E} [S.IsAdmissible] (shift : ℕ) :
    Measurable (S.schurWeight c γ shift) := by
  fun_prop [schurWeight]

/-- **Cauchy–Schwarz.** Let `S` be data of the filling theorem over the CM field `E`, which contains
a primitive root of unity of order `5040`, and let `S` be admissible: its level is the preimage of
the principal congruence subgroup, reduction is onto, and the size inequalities hold. Let `c`, `c'`
be classes and `γ` a rational element of the unitary group. The square of the amplitude majorant
(the integral of the cutoffs of `c` at `y` and of `c'` at `γ⁻¹ y` against the norm of the cut Bessel
kernel) is at most the product of the Schur integrals for `(c, c', γ)` and `(c', c, γ⁻¹)`. -/
lemma amplitudeMajorant_sq_le {c c' : S.Classes} {γ : S.G E} [S.IsAdmissible] (shift : ℕ) :
    S.amplitudeMajorant .cut c c' γ ^ 2 ≤
      S.schurIntegral c c' γ shift * S.schurIntegral c' c γ⁻¹ shift := by
  -- Cauchy–Schwarz, after the substitution `y ↦ γ⁻¹y` in `S.schurIntegral c' c γ⁻¹`.
  rw [mul_comm, schurIntegral, ← lintegral_mul_left_eq_self _ (S.ratToInf γ⁻¹)]
  -- It is enough to bound the square of the integrand at each `y`.
  refine sq_lintegral_le (by fun_prop) (by fun_prop) fun y ↦ ?_
  by_cases h_zero :
      S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) * ‖S.besselKernel .cut γ y‖ₑ = 0
  · simp [h_zero]
  simp only [mul_eq_zero, enorm_eq_zero, not_or] at h_zero
  obtain ⟨⟨h_cutoff, h_cutoff'⟩, h_ker⟩ := h_zero
  -- Where the integrand is nonzero, `y` and `γ⁻¹y` lie in `S.boxedPoints`, so there `boxCutoff`
  -- equals `classCutoff`.
  have h_box {d : S.Classes} {z : NumberField.InfinitePlace E → 𝔰.G₁}
      (hz : S.classCutoff d z ≠ 0) (h_cut : ∀ v : NumberField.InfinitePlace E, InCut (z v) S.b) :
      S.boxCutoff d z = S.classCutoff d z :=
    Set.indicator_of_mem (mem_boxedPoints_of_classCutoff_ne_zero hz h_cut) _
  have h_box_y : S.boxCutoff c y = S.classCutoff c y :=
    h_box h_cutoff fun v ↦ (inCut_of_besselKernel_ne_zero h_ker v).1
  have h_box_γy :
      S.boxCutoff c' ((S.ratToInf γ)⁻¹ * y) = S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) :=
    h_box h_cutoff' fun v ↦ (inCut_of_besselKernel_ne_zero h_ker v).2
  -- The volume ratios in the two weights `schurWeight` are inverse to each other, so the product of
  -- the two integrands is exactly the square of the integrand of `amplitudeMajorant`.
  have h_cancel :
      (∏ v : NumberField.InfinitePlace E,
          ENNReal.ofReal ((volumeRatio (S.ratToInf γ v) (y v))⁻¹ ^ (𝔰.k + shift))) *
        ∏ v : NumberField.InfinitePlace E, ENNReal.ofReal ((volumeRatio (S.ratToInf γ v)⁻¹
          ((S.ratToInf γ v)⁻¹ * y v))⁻¹ ^ (𝔰.k + shift)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ ↦ ?_
    have h_pos : 0 < volumeRatio (S.ratToInf γ v) (y v) := volumeRatio_pos _ _
    rw [volumeRatio_inv, inv_inv, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      inv_mul_cancel₀ h_pos.ne', one_pow, ENNReal.ofReal_one]
  refine le_of_eq ?_
  -- Insert the product `h_cancel`, equal to one, on the left; both sides then have equal factors.
  rw [← mul_one (_ ^ 2), ← h_cancel]
  simp only [enorm_besselKernel, schurWeight, besselCutNormSq, map_inv, inv_inv,
    mul_inv_cancel_left, Finset.prod_pow, Pi.mul_apply, Pi.inv_apply, h_box_y, h_box_γy]
  ring

/-- On a unimodular group `G`, let a countable group `Γ` act on the left through `i`, let `p` be a
cutoff, that is, a function whose translates under `Γ` sum to one, and let `F` be invariant under
`Γ`. The integral of `F` against `p` does not change when `F` is translated on the right. -/
lemma lintegral_cutoff_mul_eq_mul_right {G Γ : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group Γ] [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant]
    [ν.IsMulRightInvariant] (i : Γ →* G) {p F : G → ENNReal} (p_meas : Measurable p)
    (F_meas : Measurable F) (p_sum : ∀ u : G, ∑' k : Γ, p (i k * u) = 1)
    (F_inv : ∀ (k : Γ) (u : G), F (i k * u) = F u) (t : G) :
    ∫⁻ u : G, p u * F u ∂ν = ∫⁻ u : G, F (u * t) * p u ∂ν := by
  -- Translate by `t`, insert the sum of the translates of `p` at `u`, substitute `u ↦ i k * u` in
  -- the `k`-th term and sum the first factor `p` over `k`.
  have p_sum_inv (u : G) : ∑' k : Γ, p ((i k)⁻¹ * u) = 1 := by
    simpa [p_sum] using (Equiv.inv Γ).tsum_eq fun k ↦ p (i k * u)
  calc
    _ = ∫⁻ u, p (u * t) * F (u * t) ∂ν := (lintegral_mul_right_eq_self _ t).symm
    _ = ∑' k : Γ, ∫⁻ u, p (u * t) * F (u * t) * p ((i k)⁻¹ * u) ∂ν := by
      simp (disch := fun_prop) [← lintegral_tsum, ENNReal.tsum_mul_left, p_sum_inv]
    _ = ∑' k : Γ, ∫⁻ u, p (i k * (u * t)) * (F (u * t) * p u) ∂ν := by
      refine tsum_congr fun k ↦ ?_
      rw [← lintegral_mul_left_eq_self _ (i k)]
      simp only [mul_assoc, F_inv, inv_mul_cancel_left]
    _ = _ := by simp (disch := fun_prop) [← lintegral_tsum, ENNReal.tsum_mul_right, p_sum]

/-- On a unimodular group `G`, let `p` be a cutoff for a countable group `Γ` acting on the left
through `i` and let `F` be invariant under `Γ`. If the mean of `F (u * t x)` over `x ∈ B` is at most
`C` for all `u`, then the integral of `F` against `p` is at most `C` times that of `p`. -/
lemma lintegral_cutoff_mul_le_of_average {G Γ Y : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [Group Γ] [Countable Γ] [MeasurableSpace Y] (ν : Measure G) [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (i : Γ →* G) {p F : G → ENNReal}
    (p_meas : Measurable p) (F_meas : Measurable F) (p_sum : ∀ u : G, ∑' k : Γ, p (i k * u) = 1)
    (F_inv : ∀ (k : Γ) (u : G), F (i k * u) = F u) (m : Measure Y) [SFinite m]
    {t : Y → G} (t_meas : Measurable t) {B : Set Y} (h_pos : m B ≠ 0) (h_finite : m B ≠ ⊤)
    {C : ENNReal} (h_bound : ∀ u : G, ∫⁻ x in B, F (u * t x) ∂m ≤ m B * C) :
    ∫⁻ u, p u * F u ∂ν ≤ ∫⁻ u, C * p u ∂ν := by
  rw [← ENNReal.mul_le_mul_iff_right h_pos h_finite]
  calc
    _ = ∫⁻ _ in B, ∫⁻ u, p u * F u ∂ν ∂m := by rw [setLIntegral_const, mul_comm]
    _ = ∫⁻ x in B, ∫⁻ u, F (u * t x) * p u ∂ν ∂m := by
      simp only [← lintegral_cutoff_mul_eq_mul_right ν i p_meas F_meas p_sum F_inv]
    _ = ∫⁻ u, (∫⁻ x in B, F (u * t x) ∂m) * p u ∂ν := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      simp (disch := fun_prop) only [lintegral_mul_const]
    _ ≤ ∫⁻ u, m B * C * p u ∂ν := lintegral_mono fun u ↦ mul_le_mul_left (h_bound u) (p u)
    _ = _ := by simp only [mul_assoc, lintegral_const_mul' _ _ h_finite]

omit [HasPrimitiveRoot5040 E] in
/-- The norm of the cut Bessel function is left invariant under the unipotent group `besselU`,
which acts on the function by a unitary character. -/
lemma enorm_besselSystem_cut_mul (v : NumberField.InfinitePlace E) {u : 𝔰.G₁} (hu : u ∈ besselU)
    (y : 𝔰.G₁) :
    ‖(S.besselSystem v).besselFn .cut (u * y)‖ₑ = ‖(S.besselSystem v).besselFn .cut y‖ₑ := by
  obtain ⟨_, h_equivariant⟩ := (S.besselSystem v).isCutPair.isBesselFunction .cut
  simp [← ofReal_norm, norm_smul, h_equivariant, hu]

/-- Let `S` be data of the filling theorem over the CM field `E`, which contains a primitive root of
unity of order `5040`, and let `S` be admissible. For every class `c`, the integral over the
archimedean points `y` of `S.classCutoff c y` times `S.besselCutNormSq y` is at most
`S.unipotentCovolume`, the common covolume of the unipotent groups of the classes, times the number
`card S.BesselCoord` of Bessel coordinates. -/
lemma lintegral_classCutoff_mul_sq_le [S.IsAdmissible] (c : S.Classes) :
    ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁, S.classCutoff c y * S.besselCutNormSq y ≤
      ENNReal.ofReal S.unipotentCovolume * card S.BesselCoord := by
  have h_invariant (v : NumberField.InfinitePlace E) (u : 𝔰.G₁) (hu : u ∈ besselU) (y : 𝔰.G₁) :
      ‖(S.besselSystem v).besselFn .cut (u * y)‖ₑ ^ 2 =
        ‖(S.besselSystem v).besselFn .cut y‖ₑ ^ 2 := by
    rw [enorm_besselSystem_cut_mul v hu]
  calc
    _ = ENNReal.ofReal S.unipotentCovolume * ∏ v : NumberField.InfinitePlace E,
          ∫⁻ y, ‖(S.besselSystem v).besselFn .cut y‖ₑ ^ 2 ∂besselQuotMeasure :=
      lintegral_classCutoff_mul_prod (fun v ↦ by fun_prop) h_invariant c
    _ ≤ ENNReal.ofReal S.unipotentCovolume *
          ∏ v : NumberField.InfinitePlace E, (card (S.besselSystem v).Index : ENNReal) := by
      gcongr with v
      exact (S.besselSystem v).isCutPair.lintegral_sq_cut_le
    _ = _ := by rw [card_pi, Nat.cast_prod]

omit [HasPrimitiveRoot5040 E] in
/-- Let `𝔰.G₁` be the complex unitary group of the shape `𝔰`. Let `f` be measurable on the product
of its copies at the infinite places of the CM field `E`. The integral of `f` is an iterated
integral. The inner one runs over the orbit of `a` under `besselU0`, the unipotent elements that fix
the frame vectors e₁, …, e_ϱ, z, with the measure `𝔰.besselHaar₀` at each place. The outer one runs
over `a`, with `orbitMeasure 𝔰.besselHaar₀ volume` at each place: `volume` weighted by a cutoff, a
function with integral one over each orbit. -/
lemma lintegral_eq_lintegral_orbit
    {f : (NumberField.InfinitePlace E → 𝔰.G₁) → ENNReal} (hf : Measurable f) :
    ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁, f y =
      ∫⁻ a : NumberField.InfinitePlace E → 𝔰.G₁,
          ∫⁻ u : NumberField.InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU0,
            f ((fun v : NumberField.InfinitePlace E ↦ (u v : 𝔰.G₁)) * a) ∂Measure.pi
              fun _ ↦ 𝔰.besselHaar₀
        ∂Measure.pi fun _ ↦ orbitMeasure 𝔰.besselHaar₀ volume := by
  rw [← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar₀).lintegral_comp hf,
    lintegral_prod _ (by fun_prop)]

/-- **Integration in stages.** Let `S` be data of the filling theorem over the CM field `E`, which
contains a primitive root of unity of order `5040`, and let `S` be admissible. Let `F` be measurable
and left invariant under `S.classUnipotent₀ c`, the rational unipotent elements of the class `c`
that fix the frame vectors e₁, …, e_ϱ, z. Let `s` be measurable with components in `besselU0`, the
unipotent elements that fix these vectors, and let `B` have finite positive measure. If for all `u`
with components in `besselU0` and all boxed points `y` the integral of `F (u * s x * y)` over
`x ∈ B` is at most `m B * C`, then the integral of `F` against the boxed cutoff and
`S.besselCutNormSq`, the product of the squared norms of the local cut Bessel functions, is at most
`C` times `S.unipotentCovolume` times the cardinality of `S.BesselCoord`. -/
lemma lintegral_boxCutoff_le_of_average {X : Type*} [MeasurableSpace X] [S.IsAdmissible]
    (c : S.Classes) (m : Measure X) [SFinite m]
    {s : X → NumberField.InfinitePlace E → 𝔰.G₁} (s_meas : Measurable s)
    (hs : ∀ (x : X) (v : NumberField.InfinitePlace E), s x v ∈ besselU0)
    {F : (NumberField.InfinitePlace E → 𝔰.G₁) → ENNReal} (F_meas : Measurable F)
    (hF : ∀ u ∈ S.classUnipotent₀ c, ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      F (S.ratToInf u * y) = F y)
    (B : Set X) (h_pos : m B ≠ 0) (h_finite : m B ≠ ⊤) {C : ENNReal}
    (h_bound : ∀ u : NumberField.InfinitePlace E → 𝔰.G₁,
      (∀ v : NumberField.InfinitePlace E, u v ∈ besselU0) →
      ∀ y ∈ S.boxedPoints, ∫⁻ x in B, F (u * s x * y) ∂m ≤ m B * C) :
    ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁, S.boxCutoff c y * S.besselCutNormSq y * F y ≤
      C * (ENNReal.ofReal S.unipotentCovolume * card S.BesselCoord) := by
  -- Unfold both sides along `G`, the group `besselU0` at the infinite places. On an orbit in
  -- `S.boxedPoints` the Bessel norms and all factors of the boxed cutoff are constant, except the
  -- cutoff `p` for `S.classUnipotent₀ c`. The `p`-weighted integral of `F` does not change when
  -- `u ∈ G` is replaced by `u * s x` in `F`: average over `x ∈ B`.
  let Γ : Subgroup (S.classUnipotent c) := (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c)
  let ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ENNReal := S.reducedIndicator
  obtain ⟨p, h_cutoff, p_meas, p_sum⟩ : ∃ p : (NumberField.InfinitePlace E → 𝔰.G₁) → ENNReal,
      S.classCutoff c = p * ω ∧ Measurable p ∧
        ∀ y : NumberField.InfinitePlace E → 𝔰.G₁, ∑' k : Γ, p (S.ratToInf k * y) = 1 :=
    S.exists_classCutoff_eq_mul c
  let G : Type := NumberField.InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU0
  let ν : Measure G := .pi fun _ ↦ 𝔰.besselHaar₀
  let i : Γ →* G :=
    MonoidHom.mk' (fun k v ↦ ⟨S.ratToInf ((k : S.classUnipotent c) : S.G E) v,
        ratToInf_mem_besselU0 (Subgroup.mem_inf.1 (mem_subgroupOf.1 k.2)).2 v⟩)
      fun k k' ↦ funext fun v ↦ Subtype.ext <| congrFun (map_mul S.ratToInf _ _) v
  let ι (u : G) : NumberField.InfinitePlace E → 𝔰.G₁ := fun v ↦ u v
  have ι_mul (k : Γ) (u : G) : ι (i k * u) = S.ratToInf k * ι u := rfl
  -- The `p`-weighted integral over an orbit is bounded by averaging over the translations `s x`.
  have h_orbit (a : NumberField.InfinitePlace E → 𝔰.G₁) (ha : a ∈ S.boxedPoints) :
      ∫⁻ u, p (ι u * a) * F (ι u * a) ∂ν ≤ ∫⁻ u, C * p (ι u * a) ∂ν := by
    refine lintegral_cutoff_mul_le_of_average ν i (t := fun x v ↦ ⟨s x v, hs x v⟩)
      (by fun_prop) (by fun_prop) ?_ ?_ m (by fun_prop) h_pos h_finite ?_
    · simp only [ι_mul, mul_assoc, p_sum, implies_true]
    · intro k u
      rw [ι_mul, mul_assoc, hF _ (mem_subgroupOf.1 k.2)]
    · exact fun u ↦ h_bound (ι u) (fun v ↦ (u v).2) a ha
  -- Write both integrals as integrals of orbit integrals and compare orbit by orbit.
  grw [← lintegral_classCutoff_mul_sq_le c]
  rw [← lintegral_const_mul C (by fun_prop), lintegral_eq_lintegral_orbit (by fun_prop),
    lintegral_eq_lintegral_orbit (by fun_prop)]
  gcongr 1 with a
  change ∫⁻ u, S.boxCutoff c (ι u * a) * S.besselCutNormSq (ι u * a) * F (ι u * a) ∂ν ≤
    ∫⁻ u, C * (S.classCutoff c (ι u * a) * S.besselCutNormSq (ι u * a)) ∂ν
  -- On the orbit of `a` only the factor `p` of `S.classCutoff c` varies, and `S.boxedPoints` is
  -- `G`-stable.
  have hω : S.IsBoxPartitionOfUnity c ω := isBoxPartitionOfUnity_reducedIndicator c
  have cutoff_orbit (u : G) : S.classCutoff c (ι u * a) = p (ι u * a) * ω a := by
    rw [h_cutoff, Pi.mul_apply,
      hω.besselFixer_invariant (ι u) a fun v ↦ mem_besselFixer_of_mem_besselU0 (u v).2]
  have norm_orbit (u : G) : S.besselCutNormSq (ι u * a) = S.besselCutNormSq a := by
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [Pi.mul_apply, enorm_besselSystem_cut_mul v (Subgroup.mem_inf.1 (u v).2).1]
  have box_orbit (u : G) : ι u * a ∈ S.boxedPoints ↔ a ∈ S.boxedPoints :=
    mul_mem_boxedPoints_iff fun v ↦ (u v).2
  by_cases ha : a ∈ S.boxedPoints
  · -- Pull the constant `K` out of both orbit integrals; `h_orbit` remains.
    let K : ENNReal := ω a * S.besselCutNormSq a
    calc
      _ = (∫⁻ u, p (ι u * a) * F (ι u * a) ∂ν) * K := by
        rw [← lintegral_mul_const K (by fun_prop)]
        simp only [boxCutoff, Set.indicator_of_mem ((box_orbit _).2 ha), cutoff_orbit, norm_orbit,
          K]
        exact lintegral_congr fun u ↦ by ring
      _ ≤ (∫⁻ u, C * p (ι u * a) ∂ν) * K := by grw [h_orbit a ha]
      _ = _ := by
        rw [← lintegral_mul_const K (by fun_prop)]
        simp only [cutoff_orbit, norm_orbit, mul_assoc, K]
  · simp [boxCutoff, box_orbit, ha]

end New.Filling

end
