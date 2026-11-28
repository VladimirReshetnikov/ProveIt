import Lib.Weil.Periods.BesselIntegral
import Lib.Weil.Periods.Equivariant

/-!
# Real and finite points of the Bessel group

The Bessel group `R(𝔸)` splits as `R(F_∞) × R(𝔸_fin)`, and both factors are unimodular. A function
on `R(𝔸)` that is supported on one coset of a level in the finite variable, and depends there only
on the real variable, has an integral that reduces to `R(F_∞)`.

Notions used in the statements:
* `G E ε = GInf E ε × Gf E ι` is the adelic unitary group `G(𝔸) = G_∞ × G_f`.
* `Y.besselGroup` is the Bessel (Fourier–Jacobi) subgroup `R(𝔸)` of the grading
  `Y : Grading V N X s` of the space `V : Space E ι ε` over the CM field `E` (both defined in
  earlier files); its real points `R(F_∞)` are `Y.besselReal`, and its finite points `R(𝔸_fin)` are
  `Y.besselFin`.
* A level `K` (`IsLevel K`) is an open subgroup of `G_f` inside the standard compact subgroup.
-/

open MeasureTheory Measure

noncomputable section

/-- If the product `μ × η` of two nonzero σ-finite measures on groups `A` and `B` is right
invariant, then both factors are right invariant. -/
lemma New.isMulRightInvariant_of_prod {A B : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A]
    [Group B] [MeasurableSpace B] [MeasurableMul B] {μ : Measure A} {η : Measure B}
    [SigmaFinite μ] [SigmaFinite η] [NeZero μ] [NeZero η]
    (h_prod : (μ.prod η).IsMulRightInvariant) :
    μ.IsMulRightInvariant ∧ η.IsMulRightInvariant := by
  -- Right translation by `(a, b)` keeps the measure of a rectangle `S × T`.
  have h_rect (a : A) (b : B) {S : Set A} {T : Set B} (hS : MeasurableSet S)
      (hT : MeasurableSet T) :
      μ ((fun x : A ↦ x * a) ⁻¹' S) * η ((fun y : B ↦ y * b) ⁻¹' T) = μ S * η T := by
    have h_meas : Measurable fun q : A × B ↦ q * (a, b) :=
      (measurable_fst.mul_const a).prodMk (measurable_snd.mul_const b)
    have h_preimage : (fun q : A × B ↦ q * (a, b)) ⁻¹' (S ×ˢ T) =
        ((fun x : A ↦ x * a) ⁻¹' S) ×ˢ ((fun y : B ↦ y * b) ⁻¹' T) := Set.ext fun q ↦ by simp
    calc _ = μ.prod η ((fun q : A × B ↦ q * (a, b)) ⁻¹' (S ×ˢ T)) := by rw [h_preimage, prod_prod]
      _ = (μ.prod η).map (fun q : A × B ↦ q * (a, b)) (S ×ˢ T) :=
        (map_apply h_meas (hS.prod hT)).symm
      _ = μ S * η T := by rw [map_mul_right_eq_self, prod_prod]
  -- Take `a = 1` or `b = 1` and cancel a side of finite positive measure.
  obtain ⟨U, hU_meas, -, hU_pos, hU_fin⟩ :
      ∃ U : Set A, MeasurableSet U ∧ U ⊆ Set.univ ∧ 0 < μ U ∧ μ U < ⊤ :=
    μ.exists_subset_measure_lt_top MeasurableSet.univ (measure_univ_pos.2 (NeZero.ne μ))
  obtain ⟨V, hV_meas, -, hV_pos, hV_fin⟩ :
      ∃ V : Set B, MeasurableSet V ∧ V ⊆ Set.univ ∧ 0 < η V ∧ η V < ⊤ :=
    η.exists_subset_measure_lt_top MeasurableSet.univ (measure_univ_pos.2 (NeZero.ne η))
  constructor
  · refine (forall_measure_preimage_mul_right_iff μ).1 fun a S hS ↦ ?_
    have h_left : μ ((fun x : A ↦ x * a) ⁻¹' S) * η V = μ S * η V := by
      simpa only [mul_one, Set.preimage_id'] using h_rect a 1 hS hV_meas
    exact (ENNReal.mul_left_inj hV_pos.ne' hV_fin.ne).1 h_left
  · refine (forall_measure_preimage_mul_right_iff η).1 fun b T hT ↦ ?_
    have h_right : μ U * η ((fun y : B ↦ y * b) ⁻¹' T) = μ U * η T := by
      simpa only [mul_one, Set.preimage_id'] using h_rect 1 b hU_meas hT
    exact (ENNReal.mul_right_inj hU_pos.ne' hU_fin.ne).1 h_right

namespace New.Grading

variable {E ι X : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [DecidableEq X]
  {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)

/-- A real point `x` lies in `R(F_∞)` if and only if `(x, 1)` lies in the Bessel group `R(𝔸)`. -/
private lemma mem_besselReal_iff {x : GInf E ε} :
    x ∈ Y.besselReal ↔ ((x, 1) : G E ε) ∈ Y.besselGroup := Iff.rfl

/-- A finite point `t` lies in `R(𝔸_fin)` if and only if `(1, t)` lies in the Bessel group
`R(𝔸)`. -/
private lemma mem_besselFin_iff {t : Gf E ι} :
    t ∈ Y.besselFin ↔ ((1, t) : G E ε) ∈ Y.besselGroup := Iff.rfl

/-- A real point `s` and a finite point `t` of the Bessel group `R(𝔸)` give the point `(s, t)` of
`R(𝔸)`. -/
lemma mk_mem_besselGroup (z : Y.besselReal × Y.besselFin) :
    (((z.1 : GInf E ε), (z.2 : Gf E ι)) : G E ε) ∈ Y.besselGroup := by
  -- `(s, t) = (s, 1) (1, t)`, and both factors lie in the Bessel group.
  simpa using mul_mem (Y.mem_besselReal_iff.mp z.1.prop) (Y.mem_besselFin_iff.mp z.2.prop)

/-- The real component `r_∞` of a point `r` of the Bessel group `R(𝔸)` is a real point of the
Bessel group. -/
lemma fst_mem_besselReal (r : Y.besselGroup) : (r : G E ε).1 ∈ Y.besselReal := by
  -- `(r_∞, 1) = r (1, r_fin)⁻¹`, and `(1, r_fin)` lies in the Bessel group.
  have h_fin : ((1 : GInf E ε), (r : G E ε).2) ∈ Y.besselGroup :=
    Y.mem_besselFin_iff.mp (Y.snd_mem_besselFin r.prop)
  simpa [Y.mem_besselReal_iff, Prod.mul_def] using mul_mem r.prop (inv_mem h_fin)

/-- The decomposition `R(𝔸) = R(F_∞) × R(𝔸_fin)`: the map `(s, t) ↦ (s, t)` from the real points
times the finite points of the Bessel group to the Bessel group, as an isomorphism of
topological groups. -/
def besselProdEquiv : Y.besselReal × Y.besselFin ≃ₜ* Y.besselGroup where
  toFun z := ⟨(z.1.1, z.2.1), Y.mk_mem_besselGroup z⟩
  invFun r := (⟨r.1.1, Y.fst_mem_besselReal r⟩, ⟨r.1.2, Y.snd_mem_besselFin r.2⟩)
  map_mul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The image of the product of the Haar measures of `R(F_∞)` and `R(𝔸_fin)` is a Haar measure
on `R(𝔸)`. -/
lemma isHaarMeasure_map_besselProdEquiv :
    ((haar.prod haar).map Y.besselProdEquiv : Measure Y.besselGroup).IsHaarMeasure :=
  have : (haar.prod haar : Measure (Y.besselReal × Y.besselFin)).IsHaarMeasure :=
    prod.instIsHaarMeasure haar haar
  Y.besselProdEquiv.isHaarMeasure_map _

/-- The groups `R(F_∞)` and `R(𝔸_fin)` of real and finite points of the Bessel subgroup `R` are
unimodular: their left Haar measures are right invariant. -/
theorem isMulRightInvariant_haar_besselReal_besselFin [Fintype X] :
    (haar : Measure Y.besselReal).IsMulRightInvariant ∧
    (haar : Measure Y.besselFin).IsMulRightInvariant := by
  -- The group `R(𝔸)` is unimodular and is the product of the two groups.
  let ν : Measure Y.besselGroup := (haar.prod haar).map Y.besselProdEquiv
  have : ν.IsHaarMeasure := Y.isHaarMeasure_map_besselProdEquiv
  have h_right : ν.IsMulRightInvariant := by
    rw [isMulLeftInvariant_eq_smul ν haar]
    infer_instance
  -- Pulling `ν` back along the isomorphism gives the product measure.
  have h_emb : MeasurableEmbedding Y.besselProdEquiv :=
    Y.besselProdEquiv.toHomeomorph.measurableEmbedding
  have h_prod : (haar.prod haar : Measure (Y.besselReal × Y.besselFin)).IsMulRightInvariant := by
    rw [← h_emb.comap_map (haar.prod haar)]
    exact IsMulRightInvariant.comap ν (f := Y.besselProdEquiv.toMulEquiv.toMonoidHom) h_emb
  exact isMulRightInvariant_of_prod h_prod

/-- Let `K` be a level and `J = R(𝔸_fin) ∩ K`. There is a constant `c ≠ 0`, the volume of `J`
for compatible Haar measures, with this property. Let `t₀` be a point of `R(𝔸_fin)`, and let `f`
be integrable on `R(𝔸)`, vanish off `R(F_∞) × t₀ J` and equal `a s` at the points `(s, t)` of this
set. Then `a` is integrable on `R(F_∞)` and `∫_{R(𝔸)} f = c ∫_{R(F_∞)} a`. -/
lemma exists_integral_eq_mul_integral_besselReal (K : Subgroup (Gf E ι)) [hK : IsLevel K] :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ (t₀ : Y.besselFin) {f : Y.besselGroup → ℂ} {a : Y.besselReal → ℂ},
      (∀ (s : Y.besselReal) (t : Y.besselFin), f (Y.besselProdEquiv (s, t₀ * t)) =
        a s * (K : Set (Gf E ι)).indicator 1 (t : Gf E ι)) →
      Integrable f haar →
        Integrable a haar ∧
        ∫ r : Y.besselGroup, f r ∂haar = c * ∫ s : Y.besselReal, a s ∂haar := by
  -- The image `ν` of the product Haar measure is a Haar measure on `R(𝔸)`, so a multiple of `haar`.
  let ν : Measure Y.besselGroup := (haar.prod haar).map Y.besselProdEquiv
  have : ν.IsHaarMeasure := Y.isHaarMeasure_map_besselProdEquiv
  obtain ⟨c, hc_pos, h_haar⟩ : ∃ c : NNReal, 0 < c ∧ haar = c • ν := ⟨haarScalarFactor haar ν,
    haarScalarFactor_pos_of_isHaarMeasure haar ν, isMulLeftInvariant_eq_smul haar ν⟩
  have h_emb : MeasurableEmbedding Y.besselProdEquiv :=
    Y.besselProdEquiv.toHomeomorph.measurableEmbedding
  let J : Set Y.besselFin := Subtype.val ⁻¹' K
  have hJ_open : IsOpen J := hK.isOpen.preimage continuous_subtype_val
  have hJ_compact : IsCompact J :=
    (IsClosed.isClosedEmbedding_subtypeVal inferInstance).isCompact_preimage hK.isCompact
  have hJ_pos : haar J ≠ 0 := hJ_open.measure_ne_zero haar ⟨1, one_mem K⟩
  refine ⟨c * haar.real J, ?_, fun t₀ f a h_eq hf ↦ ?_⟩
  · simp [hc_pos.ne', Measure.real, ENNReal.toReal_eq_zero_iff, hJ_pos, hJ_compact.measure_ne_top]
  -- Translate by `t₀`; in the coordinates `(s, t)` the function is a product.
  let τ : Y.besselGroup := Y.besselProdEquiv (1, t₀)
  have h_prod (p : Y.besselReal × Y.besselFin) :
      f (τ * Y.besselProdEquiv p) = a p.1 * J.indicator 1 p.2 := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul, h_eq]
    rfl
  have h_int : Integrable (fun p : Y.besselReal × Y.besselFin ↦ a p.1 * J.indicator 1 p.2)
      (haar.prod haar) := by
    have hf_τ : Integrable (fun r : Y.besselGroup ↦ f (τ * r)) (c • ν) := by
      simpa only [← h_haar] using hf.comp_mul_left τ
    rw [ENNReal.smul_def, integrable_smul_measure (mod_cast hc_pos.ne') ENNReal.coe_ne_top,
      h_emb.integrable_map_iff] at hf_τ
    simpa only [Function.comp_def, h_prod] using hf_τ
  obtain ⟨t, ht, h_slice⟩ :
      ∃ t ∈ J, Integrable (fun s : Y.besselReal ↦ a s * J.indicator 1 t) haar :=
    exists_mem_of_measure_ne_zero_of_ae hJ_pos (ae_restrict_of_ae h_int.prod_left_ae)
  refine ⟨by simpa [ht] using h_slice, ?_⟩
  calc ∫ r, f r ∂haar = ∫ r, f (τ * r) ∂c • ν := by rw [← h_haar, integral_mul_left_eq_self]
    _ = c * ∫ p : Y.besselReal × Y.besselFin, a p.1 * J.indicator 1 p.2 ∂haar.prod haar := by
        simp only [integral_smul_nnreal_measure, ν, h_emb.integral_map, h_prod, NNReal.smul_def,
          Complex.real_smul]
    _ = (c * haar.real J : ℝ) * ∫ s : Y.besselReal, a s ∂haar := by
        simp [integral_prod_mul, integral_indicator hJ_open.measurableSet, mul_assoc, mul_comm]

end New.Grading

end
