import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
import OAI.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "ContinuousAxis" => (Σ j : Fin m, I j)
local notation "IntegerAxis" => AllocatedActiveIntegerAxis U basis L

def forecastActiveCoordinateJoinEquiv :
    ((ContinuousAxis → ℝ) × (IntegerAxis → ℝ)) ≃ᵐ (Output → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : ContinuousAxis ⊕ IntegerAxis => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Output => ℝ)
      (forecastActiveAxisEquiv (I := I) U basis L).symm)

omit [∀ j, Fintype (I j)] in
theorem forecastActiveCoordinateJoinEquiv_apply
    (p : (ContinuousAxis → ℝ) × (IntegerAxis → ℝ)) :
    forecastActiveCoordinateJoinEquiv U basis L p =
      forecastActiveCoordinateJoin U basis L p.1 p.2 := by
  funext a
  obtain ⟨i, rfl⟩ := (forecastActiveAxisEquiv (I := I) U basis L).symm.surjective a
  simp only [forecastActiveCoordinateJoinEquiv, MeasurableEquiv.coe_trans,
    Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply,
    forecastActiveCoordinateJoin, Equiv.apply_symm_apply]
  rfl

omit [∀ j, Fintype (I j)] in
theorem forecastActiveCoordinateJoinEquiv_coe :
    (forecastActiveCoordinateJoinEquiv (I := I) U basis L :
      ((ContinuousAxis → ℝ) × (IntegerAxis → ℝ)) → (Output → ℝ)) =
      fun p => forecastActiveCoordinateJoin U basis L p.1 p.2 :=
  funext (forecastActiveCoordinateJoinEquiv_apply U basis L)

theorem forecastActiveCoordinateJoinEquiv_measurePreserving :
    MeasurePreserving (forecastActiveCoordinateJoinEquiv (I := I) U basis L)
      ((volume : Measure (ContinuousAxis → ℝ)).prod
        (volume : Measure (IntegerAxis → ℝ))) volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Output => ℝ)
    (forecastActiveAxisEquiv (I := I) U basis L).symm).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm
        (fun _ : ContinuousAxis ⊕ IntegerAxis => ℝ))

theorem forecastActiveCoordinateJoin_measurePreserving :
    MeasurePreserving (fun p : (ContinuousAxis → ℝ) × (IntegerAxis → ℝ) =>
      forecastActiveCoordinateJoin U basis L p.1 p.2)
      ((volume : Measure (ContinuousAxis → ℝ)).prod
        (volume : Measure (IntegerAxis → ℝ))) volume := by
  rw [← forecastActiveCoordinateJoinEquiv_coe]
  exact forecastActiveCoordinateJoinEquiv_measurePreserving U basis L

theorem forecastActiveCoordinateJoin_integrable_iff (F : (Output → ℝ) → ℂ) :
    Integrable (fun p : (ContinuousAxis → ℝ) × (IntegerAxis → ℝ) =>
        F (forecastActiveCoordinateJoin U basis L p.1 p.2))
        ((volume : Measure (ContinuousAxis → ℝ)).prod
          (volume : Measure (IntegerAxis → ℝ))) ↔ Integrable F := by
  simpa only [Function.comp_def, forecastActiveCoordinateJoinEquiv_apply] using
    (forecastActiveCoordinateJoinEquiv_measurePreserving (I := I) U basis L).integrable_comp_emb
      (forecastActiveCoordinateJoinEquiv U basis L).measurableEmbedding (g := F)

theorem forecastActiveCoordinateJoin_integral (F : (Output → ℝ) → ℂ) :
    (∫ y, F y) = ∫ p : (ContinuousAxis → ℝ) × (IntegerAxis → ℝ),
      F (forecastActiveCoordinateJoin U basis L p.1 p.2)
        ∂((volume : Measure (ContinuousAxis → ℝ)).prod
          (volume : Measure (IntegerAxis → ℝ))) := by
  simpa only [forecastActiveCoordinateJoinEquiv_apply] using
    ((forecastActiveCoordinateJoinEquiv_measurePreserving U basis L).integral_comp
      (forecastActiveCoordinateJoinEquiv U basis L).measurableEmbedding F).symm

theorem forecastActiveCoordinateJoin_iterated_integral (F : (Output → ℝ) → ℂ)
    (hF : Integrable F) :
    (∫ y, F y) = ∫ c : ContinuousAxis → ℝ, ∫ z : IntegerAxis → ℝ,
      F (forecastActiveCoordinateJoin U basis L c z) := by
  rw [forecastActiveCoordinateJoin_integral U basis L F,
    integral_prod _ ((forecastActiveCoordinateJoin_integrable_iff U basis L F).mpr hF)]

theorem forecastActiveCoordinateJoin_integral_integrable (F : (Output → ℝ) → ℂ)
    (hF : Integrable F) :
    Integrable (fun c : ContinuousAxis → ℝ => ∫ z : IntegerAxis → ℝ,
      F (forecastActiveCoordinateJoin U basis L c z)) :=
  ((forecastActiveCoordinateJoin_integrable_iff U basis L F).mpr hF).integral_prod_left

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "IntActive" => AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a}, Unit)
local notation "scale" => allocatedActiveIntegerGridScale U basis R S.value
local notation "join" => forecastActiveCoordinateJoin (I := I) U basis S.value

theorem forecastActive_density_test_grid_quadrature
    {Spatial : Type*} [Fintype Spatial]
    (hR : ∀ j, 0 < R j) {H radius : ℝ} (hH : 0 ≤ H)
    (q : ℕ) [NeZero q] (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (hradius : 0 ≤ radius) (hmesh : (q : ℝ) * H / S.value ≤ 1)
    (density : ((Spatial → ℝ) × (Output → ℝ)) → ℝ)
    (test : (IntActive → ZMod q) → ((Spatial → ℝ) × (Output → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hdensity : LipschitzWith L density)
    (hcap : ∀ y, |density y| ≤ C) (htest : ∀ r, LipschitzWith K (test r))
    (hbound : ∀ r y, ‖test r y‖ ≤ 1)
    (hsupport : ∀ y, radius < ‖y.2‖ → density y = 0)
    (spatial : Spatial → ℝ) :
    let f := fun (c : Cont → ℝ) (r : IntActive → ZMod q) (z : IntActive → ℝ) =>
      (density (spatial, join c z) : ℂ) * test r (spatial, join c z)
    ‖∫ c, ((∑' k : IntActive → ℤ,
        f c (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
          ((∏ a, scale a : ℝ) : ℂ) - 𝔼 r : IntActive → ZMod q, ∫ z, f c r z)‖ ≤
      (2 * (2 * radius + 2) ^ Fintype.card IntActive * ((L : ℝ) + C * K) *
        ((q : ℝ) * H / S.value)) * (2 * radius) ^ Fintype.card Cont := by
  intro f
  have hmap (c : Cont → ℝ) : LipschitzWith 1
      (fun z : IntActive → ℝ => (spatial, join c z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_prod_same_left]
    exact (forecastActiveCoordinateJoin_lipschitz (I := I) U basis S.value c).dist_le_mul x y
  have hLip (c : Cont → ℝ) (r : IntActive → ZMod q) :
      LipschitzWith (L + C * K) (f c r) := by
    apply density_complex_test_lipschitz _ _ C L K
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      apply (hdensity.dist_le_mul _ _).trans
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      simpa only [NNReal.coe_one, one_mul] using (hmap c).dist_le_mul x y
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      apply ((htest r).dist_le_mul _ _).trans
      apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
      simpa only [NNReal.coe_one, one_mul] using (hmap c).dist_le_mul x y
    · exact fun z => hcap _
    · exact fun z => hbound r _
  have hsi (c : Cont → ℝ) (r : IntActive → ZMod q) (z : IntActive → ℝ)
      (hz : radius < ‖z‖) : f c r z = 0 := by
    have hg := hsupport (spatial, join c z)
      (hz.trans_le (forecastActiveCoordinateJoin_integer_norm_le (I := I) U basis S.value c z))
    simp only [f, hg, Complex.ofReal_zero, zero_mul]
  have hsc (c : Cont → ℝ) (hc : radius < ‖c‖)
      (r : IntActive → ZMod q) (z : IntActive → ℝ) : f c r z = 0 := by
    have hg := hsupport (spatial, join c z)
      (hc.trans_le (forecastActiveCoordinateJoin_continuous_norm_le (I := I) U basis S.value c z))
    simp only [f, hg, Complex.ofReal_zero, zero_mul]
  simpa only [NNReal.coe_add, NNReal.coe_mul] using
    allocatedActiveInteger_partial_periodic_quadrature U basis B S hR hH q hRinv
      hradius hradius hmesh f hLip hsi hsc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {X : Type*} [Fintype X]
variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "Cont" => (Σ j : Fin m, I j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

def forecastJointAxisEquiv : Spatial ⊕ Output ≃ Cont ⊕ (X ⊕ IntAxis) where
  toFun a := match a with
    | .inl s => .inr (.inl s.1)
    | .inr a => match forecastActiveAxisEquiv U basis L a with
      | .inl c => .inl c
      | .inr z => .inr (.inr z)
  invFun a := match a with
    | .inl c => .inr ((forecastActiveAxisEquiv U basis L).symm (.inl c))
    | .inr (.inl x) => .inl ⟨x, .inl ()⟩
    | .inr (.inr z) => .inr ((forecastActiveAxisEquiv U basis L).symm (.inr z))
  left_inv a := by
    rcases a with ⟨x, u | e⟩ | a
    · cases u; rfl
    · exact e.elim
    · obtain ⟨c | z, rfl⟩ := (forecastActiveAxisEquiv U basis L).symm.surjective a
      all_goals simp only [Equiv.apply_symm_apply]
  right_inv a := by
    rcases a with c | x | z
    all_goals simp only [Equiv.apply_symm_apply]

def forecastJointCoordinateJoinEquiv :
    ((Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) ≃ᵐ ((Spatial → ℝ) × (Output → ℝ)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Cont ⊕ (X ⊕ IntAxis) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Spatial ⊕ Output => ℝ)
      (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).trans
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Spatial ⊕ Output => ℝ)))

def forecastJointCoordinateJoin (c : Cont → ℝ) (z : (X ⊕ IntAxis) → ℝ) :
    (Spatial → ℝ) × (Output → ℝ) :=
  (fun a => z (.inl a.1),
   forecastActiveCoordinateJoin U basis L c (fun a => z (.inr a)))

omit [Fintype X] [∀ j, Fintype (I j)] in
theorem forecastJointCoordinateJoinEquiv_apply
    (p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) :
    forecastJointCoordinateJoinEquiv U basis L p =
      forecastJointCoordinateJoin U basis L p.1 p.2 := by
  apply Prod.ext
  · funext a
    simp [forecastJointCoordinateJoinEquiv, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      forecastJointCoordinateJoin, forecastJointAxisEquiv]
  · funext a
    cases h : forecastActiveAxisEquiv U basis L a <;>
      simp [forecastJointCoordinateJoinEquiv, MeasurableEquiv.sumPiEquivProdPi,
        MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
        forecastJointCoordinateJoin, forecastJointAxisEquiv, forecastActiveCoordinateJoin, h]

theorem forecastJointCoordinateJoinEquiv_measurePreserving :
    MeasurePreserving (forecastJointCoordinateJoinEquiv (X := X) (I := I) U basis L)
      volume volume := by
  exact (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Spatial ⊕ Output => ℝ)).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Spatial ⊕ Output => ℝ)
        (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).comp
          (volume_measurePreserving_sumPiEquivProdPi_symm
            (fun _ : Cont ⊕ (X ⊕ IntAxis) => ℝ)))

theorem forecastJointCoordinateJoin_isometry :
    Isometry (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      forecastJointCoordinateJoin U basis L p.1 p.2) := by
  let e : ((Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) ≃ᵢ
      ((Spatial → ℝ) × (Output → ℝ)) :=
    IsometryEquiv.sumArrowIsometryEquivProdArrow.symm.trans
      ((IsometryEquiv.piCongrLeft (Y := fun _ : Spatial ⊕ Output => ℝ)
        (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).trans
          IsometryEquiv.sumArrowIsometryEquivProdArrow)
  have he : (e : _ → _) = fun p => forecastJointCoordinateJoin U basis L p.1 p.2 := by
    funext p
    exact forecastJointCoordinateJoinEquiv_apply U basis L p
  rw [← he]
  exact e.isometry

theorem forecastJointCoordinateJoin_lipschitz :
    LipschitzWith 1 (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      forecastJointCoordinateJoin U basis L p.1 p.2) :=
  (forecastJointCoordinateJoin_isometry (X := X) (I := I) U basis L).lipschitzWith

omit [Fintype X] [∀ j, Fintype (I j)] in
theorem forecastJointCoordinateJoin_zero :
    forecastJointCoordinateJoin (X := X) (I := I) U basis L 0 0 = 0 := by
  apply Prod.ext <;> funext a
  · rfl
  · change Sum.elim (fun _ => (0 : ℝ)) (fun _ => 0)
      (forecastActiveAxisEquiv U basis L a) = 0
    cases forecastActiveAxisEquiv U basis L a <;> rfl

theorem forecastJointCoordinateJoin_norm (c : Cont → ℝ) (z : (X ⊕ IntAxis) → ℝ) :
    ‖forecastJointCoordinateJoin U basis L c z‖ = max ‖c‖ ‖z‖ := by
  have h := (forecastJointCoordinateJoin_isometry (X := X) (I := I) U basis L).dist_eq
    (c, z) (0, 0)
  simpa only [forecastJointCoordinateJoin_zero, Prod.dist_eq, dist_zero_right, Prod.norm_def] using h

theorem forecastJointCoordinateJoin_integrable_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ((Spatial → ℝ) × (Output → ℝ)) → V) :
    Integrable (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      F (forecastJointCoordinateJoin U basis L p.1 p.2)) ↔ Integrable F := by
  simpa only [Function.comp_def, forecastJointCoordinateJoinEquiv_apply] using
    (forecastJointCoordinateJoinEquiv_measurePreserving (X := X) (I := I) U basis L).integrable_comp_emb (forecastJointCoordinateJoinEquiv U basis L).measurableEmbedding
        (g := F)

theorem forecastJointCoordinateJoin_integral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ((Spatial → ℝ) × (Output → ℝ)) → V) :
    (∫ y, F y) = ∫ p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
      F (forecastJointCoordinateJoin U basis L p.1 p.2) := by
  simpa only [forecastJointCoordinateJoinEquiv_apply] using
    ((forecastJointCoordinateJoinEquiv_measurePreserving (X := X) (I := I) U basis L).integral_comp (forecastJointCoordinateJoinEquiv U basis L).measurableEmbedding F).symm

theorem forecastJointCoordinateJoin_iterated_integral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ((Spatial → ℝ) × (Output → ℝ)) → V) (hF : Integrable F) :
    (∫ y, F y) = ∫ c : Cont → ℝ, ∫ z : (X ⊕ IntAxis) → ℝ,
      F (forecastJointCoordinateJoin U basis L c z) := by
  rw [forecastJointCoordinateJoin_integral U basis L F]
  exact integral_prod _ ((forecastJointCoordinateJoin_integrable_iff U basis L F).mpr hF)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "IntActive" => AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a}, Unit)
local notation "scale" => allocatedActiveIntegerGridScale U basis R S.value
local notation "join" => forecastActiveCoordinateJoin (I := I) U basis S.value

theorem forecastActive_density_test_integral_comparison
    {Spatial : Type*} [Fintype Spatial]
    (hR : ∀ j, 0 < R j) {H radius : ℝ} (hH : 0 ≤ H)
    (q : ℕ) [NeZero q] (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (hradius : 0 ≤ radius) (hmesh : (q : ℝ) * H / S.value ≤ 1)
    (density : ((Spatial → ℝ) × (Output → ℝ)) → ℝ)
    (test : (IntActive → ZMod q) → ((Spatial → ℝ) × (Output → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hdensity : LipschitzWith L density)
    (hcap : ∀ y, |density y| ≤ C) (htest : ∀ r, LipschitzWith K (test r))
    (hbound : ∀ r y, ‖test r y‖ ≤ 1)
    (hsupport : ∀ y, radius < ‖y.2‖ → density y = 0)
    (spatial : Spatial → ℝ) :
    let f := fun (c : Cont → ℝ) (r : IntActive → ZMod q) (z : IntActive → ℝ) =>
      (density (spatial, join c z) : ℂ) * test r (spatial, join c z)
    ‖(∫ c, (∑' k : IntActive → ℤ,
        f c (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
          ((∏ a, scale a : ℝ) : ℂ)) -
      ∫ c, 𝔼 r : IntActive → ZMod q, ∫ z, f c r z‖ ≤
      (2 * (2 * radius + 2) ^ Fintype.card IntActive * ((L : ℝ) + C * K) *
        ((q : ℝ) * H / S.value)) * (2 * radius) ^ Fintype.card Cont := by
  intro f
  let F := fun (r : IntActive → ZMod q) (p : (Cont → ℝ) × (IntActive → ℝ)) => f p.1 r p.2
  have hcmap : Continuous (fun p : (Cont → ℝ) × (IntActive → ℝ) =>
      (spatial, join p.1 p.2)) :=
    continuous_const.prodMk (forecastActiveCoordinateJoin_joint_continuous (I := I) U basis S.value)
  have hf (r : IntActive → ZMod q) : Continuous (F r) :=
    (Complex.continuous_ofReal.comp (hdensity.continuous.comp hcmap)).mul
      ((htest r).continuous.comp hcmap)
  have hs (r : IntActive → ZMod q) (p : (Cont → ℝ) × (IntActive → ℝ))
      (hp : radius < ‖p‖) : F r p = 0 := by
    have hj : radius < ‖join p.1 p.2‖ := by
      rw [forecastActiveCoordinateJoin_norm]
      exact hp
    have hg := hsupport (spatial, join p.1 p.2) hj
    simp only [F, f, hg, Complex.ofReal_zero, zero_mul]
  have he := integral_partialPeriodicGrid_sub_reference q F hf scale
    (allocatedActiveIntegerGridScale_pos U basis hR S.value) radius hs
  have hmain := forecastActive_density_test_grid_quadrature U basis B S hR hH q hRinv
    hradius hmesh density test C L K hdensity hcap htest hbound hsupport spatial
  change ‖∫ c, ((∑' k : IntActive → ℤ,
    f c (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
      ((∏ a, scale a : ℝ) : ℂ) - 𝔼 r : IntActive → ZMod q, ∫ z, f c r z)‖ ≤ _ at hmain
  rw [he] at hmain
  exact hmain

theorem forecastActive_density_test_reference_comparison
    {Spatial : Type*} [Fintype Spatial]
    (hR : ∀ j, 0 < R j) {H radius : ℝ} (hH : 0 ≤ H)
    (q : ℕ) [NeZero q] (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (hradius : 0 ≤ radius) (hmesh : (q : ℝ) * H / S.value ≤ 1)
    (density : ((Spatial → ℝ) × (Output → ℝ)) → ℝ)
    (test : (IntActive → ZMod q) → ((Spatial → ℝ) × (Output → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hdensity : LipschitzWith L density)
    (hcap : ∀ y, |density y| ≤ C) (htest : ∀ r, LipschitzWith K (test r))
    (hbound : ∀ r y, ‖test r y‖ ≤ 1)
    (hsupport : ∀ y, radius < ‖y.2‖ → density y = 0)
    (spatial : Spatial → ℝ) :
    let f := fun (c : Cont → ℝ) (r : IntActive → ZMod q) (z : IntActive → ℝ) =>
      (density (spatial, join c z) : ℂ) * test r (spatial, join c z)
    ‖(∫ c, (∑' k : IntActive → ℤ,
        f c (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
          ((∏ a, scale a : ℝ) : ℂ)) -
      𝔼 r : IntActive → ZMod q, ∫ y,
        (density (spatial, y) : ℂ) * test r (spatial, y)‖ ≤
      (2 * (2 * radius + 2) ^ Fintype.card IntActive * ((L : ℝ) + C * K) *
        ((q : ℝ) * H / S.value)) * (2 * radius) ^ Fintype.card Cont := by
  intro f
  let F := fun (r : IntActive → ZMod q) (y : Output → ℝ) =>
    (density (spatial, y) : ℂ) * test r (spatial, y)
  have hcmap : Continuous (fun y : Output → ℝ => (spatial, y)) :=
    continuous_const.prodMk continuous_id
  have hF (r : IntActive → ZMod q) : Integrable (F r) := by
    apply compactBox_complex_integrable _
      ((Complex.continuous_ofReal.comp (hdensity.continuous.comp hcmap)).mul
        ((htest r).continuous.comp hcmap)) radius
    intro y hy
    change (density (spatial, y) : ℂ) * test r (spatial, y) = 0
    rw [hsupport (spatial, y) hy, Complex.ofReal_zero, zero_mul]
  have hjoin (r : IntActive → ZMod q) :
      Integrable (fun c : Cont → ℝ => ∫ z : IntActive → ℝ, F r (join c z)) :=
    ((forecastActiveCoordinateJoin_integrable_iff (I := I) U basis S.value (F r)).mpr
      (hF r)).integral_prod_left
  have he : (∫ c : Cont → ℝ, 𝔼 r : IntActive → ZMod q, ∫ z, f c r z) =
      𝔼 r : IntActive → ZMod q, ∫ y, F r y := by
    change (∫ c : Cont → ℝ, 𝔼 r : IntActive → ZMod q, ∫ z, F r (join c z)) = _
    simp only [Finset.expect_eq_sum_div_card]
    rw [integral_div, integral_finsetSum _ (fun r _ => hjoin r)]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    exact (forecastActiveCoordinateJoin_iterated_integral (I := I) U basis S.value (F r) (hF r)).symm
  have hmain := forecastActive_density_test_integral_comparison U basis B S hR hH q hRinv
    hradius hmesh density test C L K hdensity hcap htest hbound hsupport spatial
  change ‖(∫ c, (∑' k : IntActive → ℤ,
    f c (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
      ((∏ a, scale a : ℝ) : ℂ)) -
    ∫ c, 𝔼 r : IntActive → ZMod q, ∫ z, f c r z‖ ≤ _ at hmain
  rw [he] at hmain
  exact hmain

end Erdos3.VectorPolynomial

end

end OAI
