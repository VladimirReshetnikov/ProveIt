import Lib.Adelic.Adeles.IdeleModulus

/-!
# Idelic theta sums over principal ideles as Riemann sums

This file proves the lattice-sum estimate behind the continuation of Hecke `L`-functions to
`s = 1`. Ideles are pairs of a unit of the Minkowski space `mixedSpace K` and a finite idele. The
file defines the principal ideles, the module of an idele, an adelic tent and its theta sum over
the principal ideles. It writes theta sums as Riemann sums over the image of `K`. It shows that
`thetaSum d (r / 3) b` depends, up to an error, only on the module of `b`.

## Main definitions and results

* `New.ZetaIntegral.principalIdeles`: the image of `Kˣ` in the idele group;
  `New.ZetaIntegral.ideleModule` is the module of an idele.
* `New.ZetaIntegral.adelicTent r d`: a tent of height and radius `r` at `1` times the indicator of
  `d * (x - 1) ∈ Ô`.
* `New.ZetaIntegral.thetaSum d r b`: the sum of the tent over the coset of `b` modulo the
  principal ideles. `New.ZetaIntegral.exists_abs_sub_thetaSum_le_mul_rpow`: `thetaSum d (r / 3) b`
  depends only on the module `l` of `b`, up to an error: for each `l > 0` some `i` has
  `|i - thetaSum d (r / 3) b| ≤ C * l ^ δ * thetaSum d r b` for all `b` of module `l`.

Notions from other files:
* `New.finIdeleAbs`: The module |x| of a finite idele x: the adelic absolute value of the idele with
  finite part x and component 1 at infinity.
* `New.Ô`: The subring Ô of finite adeles of K that are integral at every finite place.

## Relation to the literature

Known; see `Lib.ClassField.HeckeL.ContinuationAtOne` for sources.
-/

noncomputable section

section IdelicThetaSum

open NumberField MeasureTheory Measure Metric mixedEmbedding Set ENNReal Module Algebra AddSubgroup
  ContinuousLinearMap Units Continuous Real

/-- Lowering a tent changes it little. Let `0 < r` and `0 < ε`, and let `D'` be within `ε * r / 3`
of `D`. Then the tent of height `(r - ε * r) / 3` at distance `D'` is within `ε * max (r - D) 0` of
the tent of height `r / 3` at distance `D`. -/
lemma abs_max_sub_max_le_mul_max {r ε D D' : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hD : |D' - D| ≤ ε * r / 3) :
    |max ((r - ε * r) / 3 - D') 0 - max (r / 3 - D) 0| ≤ ε * max (r - D) 0 := by
  obtain ⟨hD_lower, hD_upper⟩ := abs_le.mp hD
  have h_εr : 0 < ε * r := mul_pos hε hr
  rcases le_or_gt (r / 3) D with hD_ge | hD_lt
  · -- Both tents vanish.
    have h_max_low : max ((r - ε * r) / 3 - D') 0 = 0 := max_eq_right (by linarith)
    have h_max_mid : max (r / 3 - D) 0 = 0 := max_eq_right (by linarith)
    rw [h_max_low, h_max_mid, sub_zero, abs_zero]
    positivity
  · -- The tent loses at most `2 * ε * r / 3`, while `r - D > 2 * r / 3`.
    have h_max_mid : max (r / 3 - D) 0 = r / 3 - D := max_eq_left (by linarith)
    have h_max_top : max (r - D) 0 = r - D := max_eq_left (by linarith)
    have h_ε_le : ε * (2 * r / 3) ≤ ε * (r - D) := mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h_low_le : max ((r - ε * r) / 3 - D') 0 ≤ r / 3 - D := max_le (by linarith) (by linarith)
    rw [h_max_mid, h_max_top, abs_le]
    exact ⟨by linarith [le_max_left ((r - ε * r) / 3 - D') 0], by linarith⟩

namespace New.ZetaIntegral

/-! ### The principal ideles, the module and the test function -/

/-- The subgroup of principal ideles: the image of K^× in the idele group. -/
def principalIdeles (K : Type*) [Field K] [NumberField K] : Subgroup ((mixedSpace K)ˣ × (𝔸f K)ˣ) :=
  ((Units.map (mixedEmbedding K).toMonoidHom).prod principalIdele).range

variable {K : Type*} [Field K] [NumberField K]
  (r : ℝ) (d : (𝔸f K)ˣ) (a : (mixedSpace K)ˣ × (𝔸f K)ˣ)

/-- The module of an idele, a homomorphism to ℝ: the absolute value of the norm to ℝ of its
infinite part times the module `New.finIdeleAbs` of its finite part. -/
def ideleModule : (mixedSpace K)ˣ × (𝔸f K)ˣ →* ℝ :=
  (normHom.toMonoidHom.comp ((Algebra.norm ℝ).comp (coeHom (mixedSpace K)))).coprod
    (finIdeleAbs (E := K))

open scoped Classical in
/-- The function on adeles x = (x_∞, x_f) equal to the tent max(r − dist(x_∞, 1), 0) if x_f lies
in 1 + d⁻¹Ô, and 0 otherwise. -/
@[simp]
def adelicTent (x : mixedSpace K × 𝔸f K) : ℝ :=
  if d.val * (x.snd - 1) ∈ Ô K then max (r - dist x.fst 1) 0 else 0

deriving instance PolishSpace for mixedSpace K

/-! ### Continuity, scaling and supports -/

@[simp]
lemma ideleModule_pos : 0 < ideleModule a := mul_pos (a.fst.map (norm ℝ)).norm_pos ideleAbs_pos

/-- The module of an idele is continuous. -/
@[fun_prop]
lemma continuous_ideleModule : Continuous (ideleModule (K := K)) := by
  classical
  have h_inf : Continuous fun x : (mixedSpace K)ˣ ↦ |norm ℝ x.val| :=
    (continuous_det.comp ((mul ℝ (mixedSpace K)).continuous.comp continuous_val)).abs
  have h_fin : Continuous (finIdeleAbs (E := K)) :=
    continuous_ideleAbs.comp (units_map _ (prodMk_right _))
  exact h_inf.fst'.mul h_fin.snd'

@[fun_prop]
lemma continuous_adelicTent : Continuous (adelicTent r d) := by
  -- The condition on the finite part cuts out a clopen set, on which the tent is continuous.
  have h_clopen : IsClopen {x : mixedSpace K × 𝔸f K | d.val * (x.snd - 1) ∈ Ô K} :=
    IsClopen.preimage ⟨isCompact_Ô.isClosed, isOpen_Ô⟩ (by fun_prop)
  exact h_clopen.continuous_indicator (by fun_prop)

open scoped Classical in
/-- Multiplication by an idele `a` on `mixedSpace K × 𝔸f K` takes the Haar measure `volume` to
`(ideleModule a)⁻¹ • volume`. -/
lemma measurePreserving_idele_mul :
    MeasurePreserving (a.map val val * ·) volume (ENNReal.ofReal (ideleModule a)⁻¹ • volume) := by
  -- Multiplication scales the Haar measure by the inverse module on each of the two factors.
  have h_inf : MeasurePreserving (a.fst.val * ·) volume
      (ENNReal.ofReal |(norm ℝ a.fst.val)⁻¹| • volume) :=
    ⟨by fun_prop, map_linearMap_addHaar_eq_smul_addHaar volume (a.fst.map (norm ℝ)).ne_zero⟩
  have h_fin : MeasurePreserving (a.snd.val * ·) volume
      (ENNReal.ofReal (finIdeleAbs a.snd)⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← genIndex_eq_inv_finIdeleAbs, genIndex_eq_inv_distribHaarChar]
    exact map_smul_eq_inv_distribHaarChar_smul (A := 𝔸f K) a.snd
  have h_module : ideleModule a = |norm ℝ a.fst.val| * finIdeleAbs a.snd := rfl
  have h_measure : ENNReal.ofReal (ideleModule a)⁻¹ • (volume : Measure (mixedSpace K × 𝔸f K)) =
      (ENNReal.ofReal |(norm ℝ a.fst.val)⁻¹| • volume).prod
        (ENNReal.ofReal (finIdeleAbs a.snd)⁻¹ • volume) := by
    rw [prod_smul_left, prod_smul_right, smul_smul, ← Measure.volume_eq_prod,
      ← ENNReal.ofReal_mul (abs_nonneg _), h_module, _root_.mul_inv, abs_inv]
  rw [h_measure]
  exact h_inf.prod h_fin

/-- The product formula: a principal idele has module one. -/
@[simp]
lemma ideleModule_principal_eq_one : ∀ γ : principalIdeles K, ideleModule γ.val = 1 := by
  -- The finite part of the module of `x` is `|norm ℚ x|⁻¹` (`finIdeleAbs_principalIdele`), so it is
  -- enough to compare the two norms of `x`; the matrices of multiplication by `x` in
  -- `latticeBasis K` and `integralBasis K` have the same entries.
  have h_norm (x : K) : norm ℝ (mixedEmbedding K x) = norm ℚ x := by
    simp [← map_mul, norm_eq_matrix_det (latticeBasis K), norm_eq_matrix_det (integralBasis K),
      Matrix.det_apply', leftMulMatrix_eq_repr_mul, latticeBasis_repr_apply]
  simp [principalIdeles, ideleModule, finIdeleAbs_principalIdele, field, h_norm]

open scoped Classical in
/-- Where `adelicTent r d` is nonzero, the infinite part is within `r` of `1` and `d` times the
finite part minus `1` is integral. -/
lemma dist_le_and_mem_of_adelicTent_ne_zero {x : mixedSpace K × 𝔸f K}
    (hx : adelicTent r d x ≠ 0) : dist x.fst 1 ≤ r ∧ d.val * (x.snd - 1) ∈ Ô K := by
  grind [adelicTent]

/-- The tent `adelicTent r d`, composed with multiplication by an idele `a`, has compact support. -/
lemma hasCompactSupport_adelicTent_mul :
    HasCompactSupport (fun x : mixedSpace K × 𝔸f K ↦ adelicTent r d (a.map val val * x)) := by
  classical
  -- `adelicTent r d` vanishes off the product of a closed ball and a translate of `d⁻¹ Ô`;
  -- multiplication by a unit is a homeomorphism.
  have h_inf : IsCompact ((a.fst • ·) ⁻¹' closedBall (1 : mixedSpace K) r) :=
    (isCompact_closedBall 1 r).preimage_smul a.fst
  have h_fin : IsCompact ((a.snd • ·) ⁻¹' ((· + 1) '' ((d • ·) ⁻¹' (Ô K : Set (𝔸f K))))) :=
    ((isCompact_Ô.preimage_smul d).image (continuous_add_const 1)).preimage_smul a.snd
  refine .intro (h_inf.prod h_fin) fun x ↦ not_imp_comm.mp fun h_ne ↦ ?_
  obtain ⟨h_dist, h_mem⟩ := dist_le_and_mem_of_adelicTent_ne_zero r d h_ne
  exact ⟨h_dist, a.snd.val * x.snd - 1, h_mem, sub_add_cancel _ _⟩

open scoped Classical in
/-- Moving `x` by `w` with `‖w.1‖ ≤ ε * r / 3` and `d * w.2` integral, and lowering the tent from
`r / 3` to `(r - ε * r) / 3`, changes `adelicTent` by at most `ε * adelicTent r d x`. -/
lemma abs_adelicTent_add_sub_le {ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (x w : mixedSpace K × 𝔸f K)
    (hw_norm : ‖w.fst‖ ≤ ε * r / 3) (hw_mem : d.val * w.snd ∈ Ô K) :
    |adelicTent ((r - ε * r) / 3) d (x + w) - adelicTent (r / 3) d x| ≤ ε * adelicTent r d x := by
  -- The finite conditions of the three tents agree, as `d * w.2` is integral; at the infinite
  -- part the distance to `1` moves by at most `‖w.1‖` (`abs_max_sub_max_le_mul_max`).
  have h_dist : |dist (x.fst + w.fst) 1 - dist x.fst 1| ≤ ε * r / 3 :=
    (abs_dist_sub_le (x.fst + w.fst) x.fst 1).trans ((dist_self_add_left _ _).trans_le hw_norm)
  have h_mem_iff : d.val * (x.snd + w.snd - 1) ∈ Ô K ↔ d.val * (x.snd - 1) ∈ Ô K := by
    rw [add_sub_right_comm, mul_add, add_mem_cancel_right hw_mem]
  simp only [adelicTent, Prod.fst_add, Prod.snd_add, h_mem_iff]
  split_ifs
  · exact abs_max_sub_max_le_mul_max hr hε h_dist
  · simp

open scoped Classical in
/-- The box `ball 0 ρ ×ˢ d⁻¹ Ô` in `mixedSpace K × 𝔸f K`: the points whose infinite part has norm
less than `ρ` and whose finite part times `d` is integral. -/
def adelicBox (ρ : ℝ) : Set (mixedSpace K × 𝔸f K) :=
  ball (0 : mixedSpace K) ρ ×ˢ ((d.val * ·) ⁻¹' (Ô K : Set (𝔸f K)))

open scoped Classical in
lemma isOpen_adelicBox (ρ : ℝ) : IsOpen (adelicBox d ρ) :=
  isOpen_ball.prod (isOpen_Ô.preimage (continuous_const_mul d.val))

open scoped Classical in
/-- Blichfeldt's lemma for ideles. Let `F` be a fundamental domain for `K` in
`mixedSpace K × 𝔸f K`, and suppose the preimage, under multiplication by `a`, of the box
`ball 0 ρ ×ˢ d⁻¹ Ô` has more volume than `F`. Then for some principal idele `γ` the idele `a * γ`
has infinite part of norm less than `2 * ρ`, and `d` times its finite part is integral. -/
lemma exists_principal_mul_mem_box {F : Set (mixedSpace K × 𝔸f K)} {ρ : ℝ}
    (hF :
      IsAddFundamentalDomain ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range F)
    (h_vol : volume F <
      volume ((a.map val val * ·) ⁻¹' ball (0 : mixedSpace K) ρ ×ˢ ((d.val * ·) ⁻¹' Ô K))) :
    ∃ γ : principalIdeles K,
      ‖((a * γ.val).map val val).fst‖ < 2 * ρ ∧ d.val * ((a * γ.val).map val val).snd ∈ Ô K := by
  let j : K →+ mixedSpace K × 𝔸f K := ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom
  have : IsAddHaarMeasure (volume : Measure (mixedSpace K × 𝔸f K)) := prod.instIsAddHaarMeasure ..
  have : Countable j.range := (countable_range j).to_subtype
  let S : Set (mixedSpace K × 𝔸f K) := (a.map val val * ·) ⁻¹' adelicBox d ρ
  have hS : MeasurableSet S :=
    (measurePreserving_idele_mul a).measurable (isOpen_adelicBox d ρ).measurableSet
  -- Two points `x` and `y + x` of the preimage `S` differ by a nonzero `y ∈ K`.
  have h_blichfeldt : ∃ x ∈ S, ∃ x' ∈ S, ∃ z : j.range, z ≠ 0 ∧ z +ᵥ x = x' :=
    hF.exists_ne_zero_vadd_eq hS.nullMeasurableSet h_vol
  obtain ⟨x, hx_mem, _, hy_mem, ⟨_, y, rfl⟩, hy_ne, rfl⟩ := h_blichfeldt
  obtain ⟨hx_inf, hx_fin⟩ :
      dist (a.fst.val * x.fst) 0 < ρ ∧ d.val * (a.snd.val * x.snd) ∈ Ô K := hx_mem
  obtain ⟨hy_inf, hy_fin⟩ :
      dist (a.fst.val * (mixedEmbedding K y + x.fst)) 0 < ρ ∧
        d.val * (a.snd.val * (algebraMap K (𝔸f K) y + x.snd)) ∈ Ô K := hy_mem
  have hy_ne_zero : y ≠ 0 := fun hy ↦ hy_ne (Subtype.ext (by simp [hy]))
  -- `γ` is the principal idele of `y`; the difference of the two images is `a * γ`.
  let γ : principalIdeles K := ⟨_, .mk0 y hy_ne_zero, rfl⟩
  refine ⟨γ, ?_, ?_⟩
  · calc ‖a.fst.val * mixedEmbedding K y‖
        = dist (a.fst.val * (mixedEmbedding K y + x.fst)) (a.fst.val * x.fst) := by simp [mul_add]
      _ < ρ + ρ := (dist_triangle_right _ _ 0).trans_lt (add_lt_add hy_inf hx_inf)
      _ = 2 * ρ := (two_mul ρ).symm
  · change d.val * (a.snd.val * algebraMap K (𝔸f K) y) ∈ Ô K
    simpa [mul_add] using (Ô K).sub_mem hy_fin hx_fin

/-! ### Theta sums as Riemann sums over the image of `K` -/

/-- A principal idele, as a point of `mixedSpace K × 𝔸f K`, lies in the image of `K`. -/
lemma map_val_val_mem_range_of_mem_principalIdeles {b : (mixedSpace K)ˣ × (𝔸f K)ˣ}
    (hb : b ∈ principalIdeles K) :
    b.map val val ∈ ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range := by
  obtain ⟨x, rfl⟩ := hb
  exact ⟨x, rfl⟩

/-- A principal idele, as an element of the image of `K` in `mixedSpace K × 𝔸f K`. -/
private def principalIdelesToRange :
    principalIdeles K → ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range :=
  Subtype.map (fun b ↦ b.map val val) fun _ ↦ map_val_val_mem_range_of_mem_principalIdeles

private lemma principalIdelesToRange_injective :
    Function.Injective (principalIdelesToRange (K := K)) :=
  Subtype.map_injective _ (val_injective.prodMap val_injective)

/-- If the image of `K` in `mixedSpace K × 𝔸f K` is discrete, so are the principal ideles: they map
continuously and injectively to it. -/
lemma discreteTopology_principalIdeles
    (h_disc :
      DiscreteTopology ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range) :
    DiscreteTopology (principalIdeles K) :=
  .of_continuous_injective (f := principalIdelesToRange)
    ((continuous_val.prodMap continuous_val).subtype_map _) principalIdelesToRange_injective

/-- Let the image of `K` in `mixedSpace K × 𝔸f K` be discrete. For `ρ ≤ 1`, an idele `b` and a
principal idele `γ`, the sum of `adelicTent ρ d` at the points `b * γ * y`, `y` in the image of
`K`, is its sum at the points `γ' * b`, `γ'` principal. The term of `y = 0` vanishes, and the
nonzero `y` are the principal ideles. -/
lemma hasSum_adelicTent_mul_range
    (h_disc :
      DiscreteTopology ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range)
    {ρ : ℝ} (hρ : ρ ≤ 1) (b : (mixedSpace K)ˣ × (𝔸f K)ˣ) (γ : principalIdeles K) :
    HasSum (fun y : ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range ↦
        adelicTent ρ d ((b * γ.val).map val val * y))
      (∑' γ' : principalIdeles K, adelicTent ρ d ((γ'.val * b).map val val)) := by
  classical
  let j : K →+ mixedSpace K × 𝔸f K := ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom
  let f : mixedSpace K × 𝔸f K → ℝ := fun x ↦ adelicTent ρ d ((b * γ.val).map val val * x)
  -- `g` identifies the principal ideles with the nonzero elements of `j.range`, and `f 0 = 0`.
  let g : principalIdeles K → j.range := principalIdelesToRange
  have h_support : (Function.support fun y : j.range ↦ f y) ⊆ Set.range g := by
    rintro ⟨_, y, rfl⟩ hy
    have hy_ne_zero : y ≠ 0 := fun hy_zero ↦ hy (by simp [f, hy_zero, hρ])
    exact ⟨⟨_, .mk0 y hy_ne_zero, rfl⟩, rfl⟩
  -- Only finitely many points of the discrete `j.range` lie in the compact support of `f`.
  have h_fin_supp : Function.HasFiniteSupport fun y : j.range ↦ f y :=
    tendsto_coe_cofinite_of_isDiscrete _ ⟨h_disc⟩ <|
      Filter.mem_cocompact'.mpr ⟨_, hasCompactSupport_adelicTent_mul ρ d (b * γ), subset_closure⟩
  rw [(summable_of_hasFiniteSupport h_fin_supp).hasSum_iff]
  calc ∑' y : j.range, f y
      = ∑' γ' : principalIdeles K, f (g γ') :=
        (principalIdelesToRange_injective.tsum_eq h_support).symm
    _ = ∑' γ' : principalIdeles K, adelicTent ρ d (((γ * γ').val * b).map val val) := by
      refine tsum_congr fun γ' ↦ ?_
      change adelicTent ρ d ((b * γ.val * γ'.val).map val val) = _
      rw [Subgroup.coe_mul, mul_assoc, mul_comm b]
    _ = ∑' γ' : principalIdeles K, adelicTent ρ d ((γ'.val * b).map val val) :=
      (Equiv.mulLeft γ).tsum_eq fun γ' ↦ adelicTent ρ d ((γ'.val * b).map val val)

open scoped Classical in
/-- Multiplication by an idele `b`: for `t > 0`, the preimage of `adelicBox d (t * ρ)` has
`(ideleModule b)⁻¹ * t ^ [K : ℚ]` times the volume of `adelicBox d ρ`. -/
lemma volume_preimage_idele_mul_adelicBox {t ρ : ℝ} (ht : 0 < t) (b : (mixedSpace K)ˣ × (𝔸f K)ˣ) :
    volume ((b.map val val * ·) ⁻¹' adelicBox d (t * ρ)) =
      ENNReal.ofReal ((ideleModule b)⁻¹ * t ^ finrank ℚ K) * volume (adelicBox d ρ) := by
  rw [(measurePreserving_idele_mul b).measure_preimage (isOpen_adelicBox d _).nullMeasurableSet,
    Measure.smul_apply, _root_.smul_eq_mul, ENNReal.ofReal_mul (by simp [le_of_lt]), mul_assoc]
  simp only [adelicBox, Measure.volume_eq_prod (mixedSpace K) (𝔸f K), Measure.prod_prod,
    addHaar_ball_mul_of_pos volume (0 : mixedSpace K) ht ρ, mixedEmbedding.finrank, mul_assoc]

open scoped Classical in
open scoped Pointwise in
/-- One cell of the Riemann sum. Let `F ⊆ closedBall 0 R ×ˢ Ô K` be measurable of volume one, let
`c` be an idele with infinite part of norm less than `t * r / 3` and `d` times its finite part
integral, and let `y` be in the image of `K`. Then the mean over `y + F` of the tent of radius
`(r - R * t * r) / 3` at `c * x` is within `R * t` times the tent of radius `r` at `c * y` of
the tent of radius `r / 3` at `c * y`. -/
lemma norm_setIntegral_vadd_sub_adelicTent_le {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (hr : 0 < r)
    {F : Set (mixedSpace K × 𝔸f K)}
    (hF_sub : F ⊆ closedBall (0 : mixedSpace K) R ×ˢ (Ô K : Set (𝔸f K)))
    (hF_meas : MeasurableSet F) (hF_vol : volume F = 1) {c : (mixedSpace K)ˣ × (𝔸f K)ˣ}
    (hc_inf : ‖(c.map val val).fst‖ < t * r / 3) (hc_fin : d.val * (c.map val val).snd ∈ Ô K)
    (y : ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom.range) :
    ‖(∫ x in y +ᵥ F, adelicTent ((r - R * t * r) / 3) d (c.map val val * x)) -
        adelicTent (r / 3) d (c.map val val * y)‖ ≤
      R * t * adelicTent r d (c.map val val * y) := by
  -- The mean of a function over a cell lies in a closed ball if the function does at each point.
  have : IsAddHaarMeasure (volume : Measure (mixedSpace K × 𝔸f K)) := prod.instIsAddHaarMeasure ..
  have : IsProbabilityMeasure (volume.restrict (y +ᵥ F)) :=
    ⟨by rw [Measure.restrict_apply_univ, AddSubgroup.vadd_def, measure_vadd, hF_vol]⟩
  have h_int : Integrable fun x ↦ adelicTent ((r - R * t * r) / 3) d (c.map val val * x) :=
    (hasCompactSupport_adelicTent_mul ((r - R * t * r) / 3) d c).integrable
  rw [← mem_closedBall_iff_norm]
  refine (convex_closedBall _ _).integral_mem isClosed_closedBall
    (ae_restrict_of_forall_mem (hF_meas.const_vadd y) ?_) h_int.restrict
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hz_ball, hz_int⟩ : z.fst ∈ closedBall (0 : mixedSpace K) R ∧ z.snd ∈ Ô K := hF_sub hz
  have h_inf : ‖(c.map val val * z).fst‖ ≤ R * t * r / 3 :=
    (norm_mul_le_of_le hc_inf.le (mem_closedBall_zero_iff.mp hz_ball)).trans_eq (by ring)
  have h_fin : d.val * (c.map val val * z).snd ∈ Ô K := by
    simpa [mul_assoc] using mul_mem hc_fin hz_int
  change |adelicTent ((r - R * t * r) / 3) d (c.map val val * ((y : mixedSpace K × 𝔸f K) + z)) -
      adelicTent (r / 3) d (c.map val val * y)| ≤ R * t * adelicTent r d (c.map val val * y)
  rw [mul_add]
  exact abs_adelicTent_add_sub_le r d hr (mul_pos hR ht) _ (c.map val val * z) h_inf h_fin

/-- The theta sum of radius `ρ` at an idele `b`: the sum of the tent `adelicTent ρ d` over the coset
of `b` modulo the principal ideles. -/
def thetaSum (ρ : ℝ) (b : (mixedSpace K)ˣ × (𝔸f K)ˣ) : ℝ :=
  ∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * b).map val val)

open scoped Pointwise in
/-- Let `0 < r < 1`, and for an idele `b` let `thetaSum d ρ b` be the sum of the adelic tent
`adelicTent ρ d` of radius `ρ` (built from the finite idele `d`) over the coset of `b` modulo the
principal ideles `Kˣ`. There are `δ > 0` and `C > 0` such that for every `l > 0` some number `i` is
within `C * l ^ δ * thetaSum d r b` of `thetaSum d (r / 3) b`, for all ideles `b` of module `l`. The
bound on `r` makes the tents of radius `r` and `r / 3` vanish at `0`, so the theta sums may be taken
over all of `K`. -/
lemma exists_abs_sub_thetaSum_le_mul_rpow (hr_pos : 0 < r) (hr : r < 1) :
    ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ l > (0 : ℝ), ∃ i : ℝ, ∀ b : (mixedSpace K)ˣ × (𝔸f K)ˣ,
      ideleModule b = l → |i - thetaSum d (r / 3) b| ≤ C * l ^ δ * thetaSum d r b := by
  classical
  -- Take a fundamental domain `F` of volume one for `K` in its adeles. Blichfeldt's lemma moves `b`
  -- by a principal idele `γ` to a small `b * γ`; then `thetaSum d (r / 3) b` is a Riemann sum, over
  -- the cells `y +ᵥ F`, for an integral of `adelicTent` that depends only on `ideleModule b`.
  let j : K →+ mixedSpace K × 𝔸f K := ((mixedEmbedding K).prod (algebraMap K (𝔸f K))).toAddMonoidHom
  have : IsAddHaarMeasure (volume : Measure (mixedSpace K × 𝔸f K)) := prod.instIsAddHaarMeasure ..
  have : Countable j.range := (countable_range j).to_subtype
  obtain ⟨R, hR, h_fund⟩ :
      ∃ R > (0 : ℝ), HasFundDomain j (closedBall (0 : mixedSpace K) R ×ˢ (Ô K : Set (𝔸f K))) :=
    exists_hasFundDomain (mixedEmbedding K) (.refl ℝ (mixedSpace K)) (.id volume) fun _ ↦ rfl
  have h_disc : DiscreteTopology j.range := h_fund.isCovolOneLattice.toDiscreteTopology
  obtain ⟨-, F, hF_sub, hF_meas, hF_vol, hF_uniq⟩ := h_fund
  -- A unique `y ∈ K` with `j y + x ∈ F` is a unique element of `j.range`, as `j` is injective.
  have hF : IsAddFundamentalDomain j.range F := .mk' hF_meas.nullMeasurableSet fun x ↦
    (j.ofInjective (RingHom.injective _)).existsUnique_congr_right.mp (hF_uniq x)
  -- `n` copies of the box of radius `r / 6` have volume above `1 = volume F`.
  have h_box_ne_zero : volume (adelicBox d (r / 6)) ≠ 0 :=
    (isOpen_adelicBox d _).measure_ne_zero volume ⟨0, by simpa [adelicBox] using hr_pos⟩
  obtain ⟨n, hn, hn_vol⟩ : ∃ n : ℕ, 0 < n ∧ 1 < (n : ℝ≥0∞) * volume (adelicBox d (r / 6)) :=
    exists_nat_pos_mul_gt h_box_ne_zero one_ne_top
  refine ⟨(finrank ℚ K : ℝ)⁻¹, by simp [finrank_pos], R * (n : ℝ) ^ (finrank ℚ K : ℝ)⁻¹,
    by positivity, fun l hl ↦ ?_⟩
  let t : ℝ := ((n : ℝ) * l) ^ (finrank ℚ K : ℝ)⁻¹
  have ht : 0 < t := by positivity
  refine ⟨integral (ENNReal.ofReal l⁻¹ • volume) (adelicTent ((r - R * t * r) / 3) d),
    fun b hb ↦ ?_⟩
  -- Blichfeldt: as `t ^ [K : ℚ] = n * l`, the preimage of the box of radius `t * (r / 6)` under
  -- multiplication by `b` has `n` times the volume of the box of radius `r / 6`, which is more
  -- than the volume of `F`.
  have h_scale : (ideleModule b)⁻¹ * t ^ finrank ℚ K = n := by
    rw [hb, Real.rpow_inv_natCast_pow (by positivity) finrank_pos.ne']
    field_simp
  have h_vol : volume F < volume ((b.map val val * ·) ⁻¹' adelicBox d (t * (r / 6))) := by
    rwa [hF_vol, volume_preimage_idele_mul_adelicBox d ht b, h_scale, ENNReal.ofReal_natCast]
  obtain ⟨γ, hγ_inf, hγ_fin⟩ : ∃ γ : principalIdeles K,
      ‖((b * γ.val).map val val).fst‖ < 2 * (t * (r / 6)) ∧
        d.val * ((b * γ.val).map val val).snd ∈ Ô K :=
    exists_principal_mul_mem_box d b hF h_vol
  have hγ_small : ‖((b * γ.val).map val val).fst‖ < t * r / 3 := by linarith
  -- `f ρ` is the tent of radius `ρ` after multiplication by `b * γ`. For `ρ ≤ 1` the term of `0`
  -- vanishes, so `thetaSum d ρ b` is the sum of `f ρ` over `j.range`; and the integral of `f ρ` is
  -- the sum of its integrals over the cells.
  let f : ℝ → mixedSpace K × 𝔸f K → ℝ := fun ρ x ↦ adelicTent ρ d ((b * γ.val).map val val * x)
  have h_sum (ρ : ℝ) (hρ : ρ ≤ 1) : HasSum (fun y : j.range ↦ f ρ y) (thetaSum d ρ b) :=
    hasSum_adelicTent_mul_range d h_disc hρ b γ
  have h_cells (ρ : ℝ) : HasSum (fun y : j.range ↦ ∫ x in y +ᵥ F, f ρ x) (∫ x, f ρ x) := by
    have h_int : Integrable (f ρ) := (hasCompactSupport_adelicTent_mul ρ d (b * γ.val)).integrable
    rw [← hF.sum_restrict] at h_int
    simpa only [hF.sum_restrict] using hasSum_integral_measure h_int
  -- Each cell is within `R * t` times the tent of radius `r` of its term of `thetaSum d (r / 3) b`.
  have h_bound :
      ‖(∫ x, f ((r - R * t * r) / 3) x) - thetaSum d (r / 3) b‖ ≤ R * t * thetaSum d r b :=
    ((h_cells _).sub (h_sum (r / 3) (by linarith))).norm_le_of_bounded
      ((h_sum r hr.le).mul_left (R * t)) <|
      norm_setIntegral_vadd_sub_adelicTent_le r d hR ht hr_pos hF_sub hF_meas hF_vol hγ_small hγ_fin
  -- Change variables by `b * γ`, of module `l`.
  have h_module : ideleModule (b * γ.val) = l := by
    rw [map_mul, ideleModule_principal_eq_one, mul_one, hb]
  have h_change : ∫ x, adelicTent ((r - R * t * r) / 3) d x ∂(ENNReal.ofReal l⁻¹ • volume) =
      ∫ x, f ((r - R * t * r) / 3) x := by
    rw [← h_module]
    exact ((measurePreserving_idele_mul (b * γ.val)).hasLaw.integral_comp (by fun_prop)).symm
  rw [h_change]
  calc |(∫ x, f ((r - R * t * r) / 3) x) - thetaSum d (r / 3) b|
      ≤ R * t * thetaSum d r b := h_bound
    _ = R * (n : ℝ) ^ (finrank ℚ K : ℝ)⁻¹ * l ^ (finrank ℚ K : ℝ)⁻¹ * thetaSum d r b := by
        rw [mul_assoc R ((n : ℝ) ^ (finrank ℚ K : ℝ)⁻¹), ← Real.mul_rpow n.cast_nonneg hl.le]

open scoped Pointwise in
/-- Let `0 < r < 1`, and let `Θ r b` be the theta sum `thetaSum d r b`. (a) The principal ideles
are discrete. (b) The estimate of `exists_abs_sub_thetaSum_le_mul_rpow`, with `|Θ r b|` in the
bound. -/
lemma exists_abs_sub_thetaSum_le (hr_pos : 0 < r) (hr : r < 1) :
    let Θ (r : ℝ) (b : (mixedSpace K)ˣ × (𝔸f K)ˣ) :=
      ∑' γ : principalIdeles K, adelicTent r d ((γ.val * b).map val val)
    DiscreteTopology (principalIdeles K) ∧
    ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ l > (0 : ℝ), ∃ i : ℝ, ∀ b : (mixedSpace K)ˣ × (𝔸f K)ˣ,
      ideleModule b = l → |i - Θ (r / 3) b| ≤ C * l ^ δ * |Θ r b| := by
  classical
  intro Θ
  have : IsAddHaarMeasure (volume : Measure (mixedSpace K × 𝔸f K)) := prod.instIsAddHaarMeasure ..
  obtain ⟨R, -, h_fund⟩ :=
    exists_hasFundDomain (mixedEmbedding K) (.refl ℝ (mixedSpace K)) (.id volume) fun _ ↦ rfl
  obtain ⟨δ, hδ, C, hC, h_approx⟩ := exists_abs_sub_thetaSum_le_mul_rpow r d hr_pos hr
  refine ⟨discreteTopology_principalIdeles h_fund.isCovolOneLattice.toDiscreteTopology, δ, hδ, C,
    fun l hl ↦ ?_⟩
  obtain ⟨i, hi⟩ := h_approx l hl
  exact ⟨i, fun b hb ↦ (hi b hb).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))⟩

end New.ZetaIntegral

end IdelicThetaSum

end
