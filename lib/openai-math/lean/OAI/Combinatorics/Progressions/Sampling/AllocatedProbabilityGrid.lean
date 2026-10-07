import OAI.Combinatorics.Progressions.Estimates.AllocatedFrozenBlockPMF
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedGridAxisScale : {a // grid a} → ℝ≥0
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => basisAxisScale (b j) i

theorem allocatedGridAxisScale_bounds (a : {a // grid a}) :
    1 ≤ allocatedGridAxisScale B U b S a ∧
      allocatedGridAxisScale B U b S a ≤ (S.value : ℝ≥0) ^ (layerTailDegree m + 1) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · constructor
    · change (1 : ℝ≥0) ≤ (basisAxisScale (b j) i : ℝ≥0)
      exact_mod_cast Nat.succ_le_of_lt (basisAxisScale_pos (b j) i)
    · change (basisAxisScale (b j) i : ℝ≥0) ≤ _
      change basisAxisScale (b j) i ≤ S.value ^ (layerTailDegree m + 1) at ha
      exact_mod_cast ha

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

noncomputable def allocatedGridNormalizedRows (z : AllocatedFrozenJetRows B U b S O) :
    ∀ a : {a // grid a}, O a.val.1 → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => fun t => (z ⟨⟨j, .inr i⟩, ha⟩ t : ℝ) / basisAxisScale (b j) i

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedGridJetFactorInterpolation :
    ∀ a : {a // grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => integerRowMassInterpolation (basisAxisScale (b j) i)
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v))
        (j.val + 1) (rows j)) (allocatedLayerIntegerPMFs B U b hR hσ S j i))

noncomputable def allocatedGridJetInterpolation (z : ∀ a : {a // grid a}, O a.val.1 → ℝ) : ℝ :=
  ∏ a, allocatedGridJetFactorInterpolation B U b S hR hσ x u v rows a (z a)

theorem allocatedGridJetFactorInterpolation_grid (z : AllocatedFrozenJetRows B U b S O)
    (a : {a // grid a}) :
    allocatedGridJetFactorInterpolation B U b S hR hσ x u v rows a
        (allocatedGridNormalizedRows B U b S z a) =
      (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1) *
        allocatedGridJetFactor B U b hR hσ S x u v rows a (z a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact integerRowMassInterpolation_grid (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) _ _

theorem allocatedGridJetInterpolation_grid (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridJetInterpolation B U b S hR hσ x u v rows (allocatedGridNormalizedRows B U b S z) =
      (∏ a : {a // grid a}, (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)) *
        allocatedGridJetDensity B U b hR hσ S x u v rows z := by
  simp only [allocatedGridJetInterpolation, allocatedGridJetFactorInterpolation_grid,
    Finset.prod_mul_distrib, allocatedGridJetDensity]

theorem allocatedGridJetFactorInterpolation_bounds (a : {a // grid a}) :
    (∀ z, 0 ≤ allocatedGridJetFactorInterpolation B U b S hR hσ x u v rows a z ∧
      allocatedGridJetFactorInterpolation B U b S hR hσ x u v rows a z ≤
        (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)) ∧
    LipschitzWith (Fintype.card (O a.val.1) * (2 * allocatedGridAxisScale B U b S a ^ 2) *
      allocatedGridAxisScale B U b S a ^ Fintype.card (O a.val.1))
      (allocatedGridJetFactorInterpolation B U b S hR hσ x u v rows a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ⟨fun z => integerRowMassInterpolation_range (Nat.cast_nonneg _) _ z,
      integerRowMassInterpolation_lipschitz _
        (allocatedGridAxisScale_bounds B U b S ⟨⟨j, .inr i⟩, ha⟩).1 _⟩

theorem allocatedGridJetInterpolation_bounds (K : ℝ≥0) (D : ℕ) (hK : 1 ≤ K)
    (hscale : ∀ a : {a // grid a}, allocatedGridAxisScale B U b S a ≤ K)
    (hD : ∀ a : {a // grid a}, Fintype.card (O a.val.1) ≤ D) :
    (∀ z, 0 ≤ allocatedGridJetInterpolation B U b S hR hσ x u v rows z ∧
      allocatedGridJetInterpolation B U b S hR hσ x u v rows z ≤
        ((K : ℝ) ^ D) ^ Fintype.card {a // grid a}) ∧
    LipschitzWith (Fintype.card {a // grid a} * (D * (2 * K ^ 2) * K ^ D) *
      (K ^ D) ^ Fintype.card {a // grid a})
      (allocatedGridJetInterpolation B U b S hR hσ x u v rows) := by
  let f := fun a : {a // grid a} => allocatedGridJetFactorInterpolation B U b S hR hσ x u v rows a
  have hbounds := allocatedGridJetFactorInterpolation_bounds B U b S hR hσ x u v rows
  have hp (a : {a // grid a}) :
      allocatedGridAxisScale B U b S a ^ Fintype.card (O a.val.1) ≤ K ^ D := by
    exact (pow_le_pow_left' (hscale a) _).trans (pow_le_pow_right₀ hK (hD a))
  have hl (a : {a // grid a}) : LipschitzWith (D * (2 * K ^ 2) * K ^ D) (f a) := by
    apply (hbounds a).2.weaken
    apply mul_le_mul _ (hp a) (by positivity) (by positivity)
    exact mul_le_mul (Nat.cast_le.mpr (hD a))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left' (hscale a) 2) (by positivity))
      (by positivity) (by positivity)
  have hcoord (a : {a // grid a}) :
      LipschitzWith (D * (2 * K ^ 2) * K ^ D)
        (fun z : ∀ a : {a // grid a}, O a.val.1 → ℝ => f a (z a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    exact ((hl a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist z w a) (NNReal.coe_nonneg _))
  obtain ⟨hcap, hLip⟩ := bounded_lipschitz_real_prod _ (one_le_pow₀ hK) hcoord
    (fun a z => by
      rw [abs_of_nonneg ((hbounds a).1 (z a)).1]
      exact ((hbounds a).1 (z a)).2.trans (by exact_mod_cast hp a))
  refine ⟨fun z => ⟨Finset.prod_nonneg (fun a _ => ((hbounds a).1 (z a)).1), ?_⟩, hLip⟩
  exact (le_abs_self _).trans (by simpa only [NNReal.coe_pow, f, allocatedGridJetInterpolation] using hcap z)

theorem allocatedGridJetInterpolation_uniform_bounds :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    (∀ z, 0 ≤ allocatedGridJetInterpolation B U b S hR hσ x u v rows z ∧
      allocatedGridJetInterpolation B U b S hR hσ x u v rows z ≤
        ((K : ℝ) ^ D) ^ Fintype.card {a // grid a}) ∧
    LipschitzWith (Fintype.card {a // grid a} * (D * (2 * K ^ 2) * K ^ D) *
      (K ^ D) ^ Fintype.card {a // grid a})
      (allocatedGridJetInterpolation B U b S hR hσ x u v rows) := by
  apply allocatedGridJetInterpolation_bounds B U b S hR hσ x u v rows
  · exact one_le_pow₀ (by exact_mod_cast Nat.succ_le_of_lt S.positive)
  · exact fun a => (allocatedGridAxisScale_bounds B U b S a).2
  · intro a
    apply Fintype.card_le_of_injective (fun t : O a.val.1 => (⟨a.val, t⟩ : Σ c : LayerSamplerAxis I n, O c.1))
    intro t w h
    exact eq_of_heq (Sigma.mk.inj h).2

theorem allocatedGridJetInterpolation_counting_mass :
    let scale := ∏ a : {a // grid a},
      (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)
    Integrable (fun z =>
      allocatedGridJetInterpolation B U b S hR hσ x u v rows (allocatedGridNormalizedRows B U b S z) / scale)
      (allocatedFrozenJetReference B U b S O) ∧
    (∫ z, allocatedGridJetInterpolation B U b S hR hσ x u v rows
      (allocatedGridNormalizedRows B U b S z) / scale ∂allocatedFrozenJetReference B U b S O) = 1 := by
  intro scale
  have hs : 0 < scale := Finset.prod_pos (fun a _ => pow_pos
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast (allocatedGridAxisScale_bounds B U b S a).1)) _)
  have he : (fun z => allocatedGridJetInterpolation B U b S hR hσ x u v rows
      (allocatedGridNormalizedRows B U b S z) / scale) =
      allocatedGridJetDensity B U b hR hσ S x u v rows := by
    funext z
    rw [allocatedGridJetInterpolation_grid]
    change scale * _ / scale = _
    field_simp [hs.ne']
  rw [he]
  exact allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

abbrev JetAmbientIndex {m : ℕ} (O J : Fin m → Type*) := Σ j, O j × J j

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedJetAmbientPoint
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : JetAmbientIndex O J → ℝ :=
  fun a => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
    (orthonormalMixedChart (o a.1) (mixedArrayRegroup _ _ _ (z a.1) a.2.1)) a.2.2

noncomputable def allocatedGridAmbientCoordinates (z : JetAmbientIndex O J → ℝ) :
    ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, O a.val.1 → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => fun t => (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))).2 i

omit [∀ j, Fintype (O j)] in
theorem allocatedGridAmbientCoordinates_point
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedGridAmbientCoordinates B U b S o (mixedJetAmbientPoint U b o z) =
      allocatedGridNormalizedRows B U b S (fun a => coefficientJetAxisEquiv O I n z a.val) := by
  funext a t
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm ((EuclideanSpace.equiv (J j) ℝ)
        (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) t)))))).2 i = _
    rw [ContinuousLinearEquiv.symm_apply_apply, mixedRealCoordinates_integer]
    rfl

theorem allocatedGridAmbientCoordinates_lipschitz (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖) :
    LipschitzWith (∑ j, C j * Fintype.card (J j)) (allocatedGridAmbientCoordinates B U b S (O := O) o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U j)) (b j) (o j) (hC j)).comp
        (euclideanFromCoordinates_lipschitz (D := J j))).dist_le_mul
          (fun k => z ⟨j, t, k⟩) (fun k => w ⟨j, t, k⟩)
    have hin : dist (fun k => z ⟨j, t, k⟩) (fun k => w ⟨j, t, k⟩) ≤ dist z w :=
      (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨j, t, k⟩)
    let pz := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))
    let pw := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => w ⟨j, t, k⟩))
    have hout : dist (pz.2 i) (pw.2 i) ≤ dist pz pw :=
      (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
    have hc : C j * Fintype.card (J j) ≤ ∑ j, C j * Fintype.card (J j) :=
      Finset.single_le_sum (f := fun k => C k * Fintype.card (J k))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    exact (hout.trans hrow).trans ((mul_le_mul_of_nonneg_right
      (by exact_mod_cast hc) (dist_nonneg (x := z) (y := w))).trans'
        (mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedNormalizedGridFactor :
    ∀ a : {a // grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => normalizedIntegerRowInterpolation (basisAxisScale (b j) i)
      (allocatedFrozenBlockPMF B U b hR hσ S u rows ⟨⟨j, .inr i⟩, ha⟩)

noncomputable def allocatedNormalizedGridInterpolation
    (z : ∀ a : {a // grid a}, O a.val.1 → ℝ) : ℝ :=
  ∏ a, allocatedNormalizedGridFactor B U b hR hσ S u rows a (z a)

theorem allocatedNormalizedGridFactor_bounds (a : {a // grid a}) :
    (∀ z, allocatedNormalizedGridFactor B U b hR hσ S u rows a z ∈ Set.Icc (0 : ℝ) 1) ∧
    LipschitzWith (Fintype.card (O a.val.1) * (2 * allocatedGridAxisScale B U b S a ^ 2))
      (allocatedNormalizedGridFactor B U b hR hσ S u rows a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ⟨normalizedIntegerRowInterpolation_range (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) _,
      normalizedIntegerRowInterpolation_lipschitz _ (allocatedGridAxisScale_bounds B U b S ⟨⟨j, .inr i⟩, ha⟩).1 _⟩

theorem allocatedNormalizedGridInterpolation_bounds (K : ℝ≥0) (D : ℕ)
    (hscale : ∀ a : {a // grid a}, allocatedGridAxisScale B U b S a ≤ K)
    (hD : ∀ a : {a // grid a}, Fintype.card (O a.val.1) ≤ D) :
    (∀ z, allocatedNormalizedGridInterpolation B U b hR hσ S u rows z ∈ Set.Icc (0 : ℝ) 1) ∧
    LipschitzWith (Fintype.card {a // grid a} * (D * (2 * K ^ 2)))
      (allocatedNormalizedGridInterpolation B U b hR hσ S u rows) := by
  have hb := allocatedNormalizedGridFactor_bounds B U b hR hσ S u rows
  have hl (a : {a // grid a}) : LipschitzWith (D * (2 * K ^ 2))
      (allocatedNormalizedGridFactor B U b hR hσ S u rows a) := by
    apply (hb a).2.weaken
    exact mul_le_mul (Nat.cast_le.mpr (hD a))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left' (hscale a) 2) (by positivity))
      (by positivity) (by positivity)
  have hc (a : {a // grid a}) : LipschitzWith (D * (2 * K ^ 2))
      (fun z : ∀ a : {a // grid a}, O a.val.1 → ℝ =>
        allocatedNormalizedGridFactor B U b hR hσ S u rows a (z a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    exact ((hl a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist z w a) (NNReal.coe_nonneg _))
  obtain ⟨hbound, hLip⟩ := bounded_lipschitz_real_prod _ (B := 1) le_rfl hc
    (fun a z => by rw [abs_of_nonneg ((hb a).1 (z a)).1]; exact ((hb a).1 (z a)).2)
  refine ⟨fun z => ⟨Finset.prod_nonneg (fun a _ => ((hb a).1 (z a)).1), ?_⟩, ?_⟩
  · exact (le_abs_self _).trans (by
      simpa only [allocatedNormalizedGridInterpolation, NNReal.coe_one, one_pow] using hbound z)
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [allocatedNormalizedGridInterpolation, one_pow, mul_one] using hLip.dist_le_mul z w

theorem allocatedNormalizedGridInterpolation_grid
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S O) :
    allocatedNormalizedGridInterpolation B U b hR hσ S u rows
        (allocatedGridNormalizedRows B U b S z) =
      allocatedGridJetDensity B U b hR hσ S x u v rows z := by
  rw [allocatedGridJetDensity_frozen_blocks B U b hR hσ S u rows x v z]
  unfold allocatedNormalizedGridInterpolation
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact normalizedIntegerRowInterpolation_grid (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

noncomputable def allocatedProbabilityGridDensity (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, (p a (z a)).toReal

omit [∀ j, Fintype (O j)] in
theorem allocatedProbabilityGridDensity_nonneg (z : AllocatedFrozenJetRows B U b S O) :
    0 ≤ allocatedProbabilityGridDensity B U b S p z :=
  Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)

theorem allocatedProbabilityGridDensity_mass :
    Integrable (allocatedProbabilityGridDensity B U b S p) (allocatedFrozenJetReference B U b S O) ∧
      (∫ z, allocatedProbabilityGridDensity B U b S p z ∂allocatedFrozenJetReference B U b S O) = 1 := by
  have hp (a : {a // grid a}) :
      Integrable (fun z => (p a z).toReal) (coefficientJetAxisReference O a.val) ∧
        (∫ z, (p a z).toReal ∂coefficientJetAxisReference O a.val) = 1 := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · let : Countable (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) :=
        inferInstanceAs (Countable (O j → ℤ))
      let : MeasurableSingletonClass (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) :=
        inferInstanceAs (MeasurableSingletonClass (O j → ℤ))
      exact ⟨pmf_real_integrable _, pmf_real_integral_count _⟩
  refine ⟨Integrable.fintype_prod_dep (fun a => (hp a).1), ?_⟩
  change (∫ z, (∏ a, (p a (z a)).toReal)
    ∂Measure.pi (fun a : {a // grid a} => coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod (f := fun a z => (p a z).toReal)]
  simp only [(hp _).2, Finset.prod_const_one]

noncomputable def allocatedProbabilityGridFactor :
    ∀ a : {a // grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => integerRowMassInterpolation (basisAxisScale (b j) i)
      (p ⟨⟨j, .inr i⟩, ha⟩)

noncomputable def allocatedProbabilityGridInterpolation (z : ∀ a : {a // grid a}, O a.val.1 → ℝ) : ℝ :=
  ∏ a, allocatedProbabilityGridFactor B U b S p a (z a)

theorem allocatedProbabilityGridFactor_grid (z : AllocatedFrozenJetRows B U b S O)
    (a : {a // grid a}) :
    allocatedProbabilityGridFactor B U b S p a
        (allocatedGridNormalizedRows B U b S z a) =
      (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1) *
        (p a (z a)).toReal := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact integerRowMassInterpolation_grid (Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)) _ _

theorem allocatedProbabilityGridInterpolation_grid (z : AllocatedFrozenJetRows B U b S O) :
    allocatedProbabilityGridInterpolation B U b S p (allocatedGridNormalizedRows B U b S z) =
      (∏ a : {a // grid a}, (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)) *
        allocatedProbabilityGridDensity B U b S p z := by
  simp only [allocatedProbabilityGridInterpolation, allocatedProbabilityGridFactor_grid,
    Finset.prod_mul_distrib, allocatedProbabilityGridDensity]

theorem allocatedProbabilityGridFactor_bounds (a : {a // grid a}) :
    (∀ z, 0 ≤ allocatedProbabilityGridFactor B U b S p a z ∧
      allocatedProbabilityGridFactor B U b S p a z ≤
        (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)) ∧
    LipschitzWith (Fintype.card (O a.val.1) * (2 * allocatedGridAxisScale B U b S a ^ 2) *
      allocatedGridAxisScale B U b S a ^ Fintype.card (O a.val.1))
      (allocatedProbabilityGridFactor B U b S p a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ⟨fun z => integerRowMassInterpolation_range (Nat.cast_nonneg _) _ z,
      integerRowMassInterpolation_lipschitz _
        (allocatedGridAxisScale_bounds B U b S ⟨⟨j, .inr i⟩, ha⟩).1 _⟩

theorem allocatedProbabilityGridInterpolation_bounds (K : ℝ≥0) (D : ℕ) (hK : 1 ≤ K)
    (hscale : ∀ a : {a // grid a}, allocatedGridAxisScale B U b S a ≤ K)
    (hD : ∀ a : {a // grid a}, Fintype.card (O a.val.1) ≤ D) :
    (∀ z, 0 ≤ allocatedProbabilityGridInterpolation B U b S p z ∧
      allocatedProbabilityGridInterpolation B U b S p z ≤
        ((K : ℝ) ^ D) ^ Fintype.card {a // grid a}) ∧
    LipschitzWith (Fintype.card {a // grid a} * (D * (2 * K ^ 2) * K ^ D) *
      (K ^ D) ^ Fintype.card {a // grid a})
      (allocatedProbabilityGridInterpolation B U b S p) := by
  let f := fun a : {a // grid a} => allocatedProbabilityGridFactor B U b S p a
  have hbounds := allocatedProbabilityGridFactor_bounds B U b S p
  have hp (a : {a // grid a}) :
      allocatedGridAxisScale B U b S a ^ Fintype.card (O a.val.1) ≤ K ^ D := by
    exact (pow_le_pow_left' (hscale a) _).trans (pow_le_pow_right₀ hK (hD a))
  have hl (a : {a // grid a}) : LipschitzWith (D * (2 * K ^ 2) * K ^ D) (f a) := by
    apply (hbounds a).2.weaken
    apply mul_le_mul _ (hp a) (by positivity) (by positivity)
    exact mul_le_mul (Nat.cast_le.mpr (hD a))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left' (hscale a) 2) (by positivity))
      (by positivity) (by positivity)
  have hcoord (a : {a // grid a}) :
      LipschitzWith (D * (2 * K ^ 2) * K ^ D)
        (fun z : ∀ a : {a // grid a}, O a.val.1 → ℝ => f a (z a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    exact ((hl a).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist z w a) (NNReal.coe_nonneg _))
  obtain ⟨hcap, hLip⟩ := bounded_lipschitz_real_prod _ (one_le_pow₀ hK) hcoord
    (fun a z => by
      rw [abs_of_nonneg ((hbounds a).1 (z a)).1]
      exact ((hbounds a).1 (z a)).2.trans (by exact_mod_cast hp a))
  refine ⟨fun z => ⟨Finset.prod_nonneg (fun a _ => ((hbounds a).1 (z a)).1), ?_⟩, hLip⟩
  exact (le_abs_self _).trans (by simpa only [NNReal.coe_pow, f, allocatedProbabilityGridInterpolation] using hcap z)

theorem allocatedProbabilityGridInterpolation_uniform_bounds :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    (∀ z, 0 ≤ allocatedProbabilityGridInterpolation B U b S p z ∧
      allocatedProbabilityGridInterpolation B U b S p z ≤
        ((K : ℝ) ^ D) ^ Fintype.card {a // grid a}) ∧
    LipschitzWith (Fintype.card {a // grid a} * (D * (2 * K ^ 2) * K ^ D) *
      (K ^ D) ^ Fintype.card {a // grid a})
      (allocatedProbabilityGridInterpolation B U b S p) := by
  apply allocatedProbabilityGridInterpolation_bounds B U b S p
  · exact one_le_pow₀ (by exact_mod_cast Nat.succ_le_of_lt S.positive)
  · exact fun a => (allocatedGridAxisScale_bounds B U b S a).2
  · intro a
    apply Fintype.card_le_of_injective (fun t : O a.val.1 => (⟨a.val, t⟩ : Σ c : LayerSamplerAxis I n, O c.1))
    intro t w h
    exact eq_of_heq (Sigma.mk.inj h).2

theorem allocatedProbabilityGridInterpolation_counting_mass :
    let scale := ∏ a : {a // grid a},
      (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)
    Integrable (fun z =>
      allocatedProbabilityGridInterpolation B U b S p (allocatedGridNormalizedRows B U b S z) / scale)
      (allocatedFrozenJetReference B U b S O) ∧
    (∫ z, allocatedProbabilityGridInterpolation B U b S p
      (allocatedGridNormalizedRows B U b S z) / scale ∂allocatedFrozenJetReference B U b S O) = 1 := by
  intro scale
  have hs : 0 < scale := Finset.prod_pos (fun a _ => pow_pos
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast (allocatedGridAxisScale_bounds B U b S a).1)) _)
  have he : (fun z => allocatedProbabilityGridInterpolation B U b S p
      (allocatedGridNormalizedRows B U b S z) / scale) =
      allocatedProbabilityGridDensity B U b S p := by
    funext z
    rw [allocatedProbabilityGridInterpolation_grid]
    change scale * _ / scale = _
    field_simp [hs.ne']
  rw [he]
  exact allocatedProbabilityGridDensity_mass B U b S p

end Erdos3.VectorPolynomial

end

end OAI
