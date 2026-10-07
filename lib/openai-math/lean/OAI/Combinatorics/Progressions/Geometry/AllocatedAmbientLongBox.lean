/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.JetAxisReference
import OAI.Combinatorics.Progressions.Lattices.AllocatedIntegerSupport
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

section Box

variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedLongJetRowBox (T : ℝ) :
    ∀ a : {a // ¬grid a}, Set (CoefficientJetAxisRow O a.val)
  | ⟨⟨j, .inl _⟩, _⟩ => (Metric.closedBall (0 : O j → ℝ) T : Set (O j → ℝ))
  | ⟨⟨j, .inr i⟩, _⟩ =>
      (rectangularWeightIndices (fun _ => 0) (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T : Set (O j → ℤ))

noncomputable def allocatedLongJetBox (T : ℝ) : Set (AllocatedLongJetRows B U basis S O) :=
  Set.univ.pi (allocatedLongJetRowBox B U basis S O T)

theorem allocatedLongJetRowBox_measurable (T : ℝ) (a : {a // ¬grid a}) :
    MeasurableSet (allocatedLongJetRowBox B U basis S O T a) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change MeasurableSet (Metric.closedBall (0 : O j → ℝ) T)
    exact measurableSet_closedBall
  | inr i =>
    change MeasurableSet (rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T : Set (O j → ℤ))
    exact Finset.measurableSet _

theorem allocatedLongJetBox_measurable (T : ℝ) :
    MeasurableSet (allocatedLongJetBox B U basis S O T) :=
  MeasurableSet.univ_pi (allocatedLongJetRowBox_measurable B U basis S O T)

end Box

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α] [DecidableEq G]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "box" => allocatedLongJetBox B U basis S O T

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedLongJetFactor_zero_off_box
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val)
    (hz : z ∉ allocatedLongJetRowBox B U basis S O T a) :
    allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z = 0 := by
  have hv : ‖principalTupleNormalized lengths v‖ ≤ 1 :=
    principalTupleNormalized_norm_le (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) lengths
      (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩) v
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change O j → ℝ at z
    apply allocatedContinuousKernelDensity_zero_off_box B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 j i _ hv z
    change ¬dist z (0 : O j → ℝ) ≤ T at hz
    rw [dist_zero_right] at hz
    exact lt_of_not_ge hz
  | inr i =>
    change (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha) z).toReal = 0
    rw [allocatedIntegerKernelPMF_zero_off_box B U basis hR hσ S x u v rows j i (hσ1 j)
      (Nat.lt_of_not_ge ha) hP (hRP j) z hz, ENNReal.toReal_zero]

theorem allocatedLongJetDensity_zero_off_box
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (z : AllocatedLongJetRows B U basis S O) (hz : z ∉ box) :
    allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z = 0 := by
  have ha : ∃ a, z a ∉ allocatedLongJetRowBox B U basis S O T a := by
    simpa only [allocatedLongJetBox, Set.mem_univ_pi, not_forall] using hz
  obtain ⟨a, ha⟩ := ha
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (allocatedLongJetFactor_zero_off_box B U basis S hR hσ x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1 v a (z a) ha)

include hσ1 in
theorem allocatedLongJetTarget_zero_off_box
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val)
    (hz : z ∉ allocatedLongJetRowBox B U basis S O T a) :
    allocatedLongJetTarget B U basis S x u rows s hA y a z = 0 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change O j → ℝ at z
    apply allocatedContinuousKernelDensity_zero_off_box B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 j i y hy z
    change ¬dist z (0 : O j → ℝ) ≤ T at hz
    rw [dist_zero_right] at hz
    exact lt_of_not_ge hz
  | inr i =>
    exact allocatedIntegerKernelDensity_zero_off_box B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 j i y hy z hz

include hσ1 in
theorem allocatedLongJetTarget_integral_zero_off_box
    (z : AllocatedLongJetRows B U basis S O) (hz : z ∉ box) :
    (∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
      ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)) = 0 := by
  have ha : ∃ a, z a ∉ allocatedLongJetRowBox B U basis S O T a := by
    simpa only [allocatedLongJetBox, Set.mem_univ_pi, not_forall] using hz
  obtain ⟨a, ha⟩ := ha
  apply integral_eq_zero_of_ae
  filter_upwards [jointBooleanSource_ae_closedBall (fun a : {a // ¬grid a} => B a.val)
    (fun a => layerSamplerDegree I n a.val)] with y hy
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (allocatedLongJetTarget_zero_off_box B U basis S hR hσ x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1
      y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy) a (z a) ha)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedLongJetRowBox_measure_lt_top (T : ℝ) (a : {a // ¬grid a}) :
    coefficientJetAxisReference O a.val (allocatedLongJetRowBox B U basis S O T a) < ∞ := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change volume (Metric.closedBall (0 : O j → ℝ) T) < ∞
    exact (isCompact_closedBall (0 : O j → ℝ) T).measure_lt_top
  | inr i =>
    change Measure.count (↑(rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T) : Set (O j → ℤ)) < ∞
    rw [Measure.count_apply_finset]
    simp

theorem allocatedLongJetBox_measure_lt_top (T : ℝ) :
    allocatedLongJetReference B U basis S O (allocatedLongJetBox B U basis S O T) < ∞ := by
  unfold allocatedLongJetReference allocatedLongJetBox
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun a _ => allocatedLongJetRowBox_measure_lt_top B U basis S O T a)

theorem allocatedLongJetRowBox_measure_bound {T : ℝ} (hT : 0 ≤ T) (a : {a // ¬grid a}) :
    (coefficientJetAxisReference O a.val).real (allocatedLongJetRowBox B U basis S O T a) ≤
      (2*T+1)^Fintype.card (O a.val.1) * allocatedLongJetOutputScale B U basis S (O := O) a := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change volume.real (Metric.closedBall (0 : O j → ℝ) T) ≤ (2*T+1)^Fintype.card (O j)*1
    rw [mul_one, measureReal_def, Real.volume_pi_closedBall 0 hT, ENNReal.toReal_ofReal (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  | inr i =>
    change (Measure.count : Measure (O j → ℤ)).real
      (↑(rectangularWeightIndices (fun _ : O j => 0) (fun _ => (basisAxisScale (basis j) i : ℝ)) T) : Set (O j → ℤ)) ≤
        (2*T+1)^Fintype.card (O j) * (basisAxisScale (basis j) i : ℝ)^Fintype.card (O j)
    rw [measureReal_def, Measure.count_apply_finset, ENNReal.toReal_natCast]
    have hH : (1 : ℝ) ≤ basisAxisScale (basis j) i := by
      exact_mod_cast Nat.succ_le_of_lt (basisAxisScale_pos (basis j) i)
    simpa only [Finset.prod_const, Finset.card_univ] using
      rectangularWeightIndices_card_le (fun _ : O j => 0) (fun _ => (basisAxisScale (basis j) i : ℝ))
        (fun _ => hH) hT

theorem allocatedLongJetBox_measure_bound {T : ℝ} (hT : 0 ≤ T) :
    (allocatedLongJetReference B U basis S O).real (allocatedLongJetBox B U basis S O T) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a := by
  have hc : Fintype.card (Σ a : {a // ¬grid a}, O a.val.1) ≤
      Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
    apply Fintype.card_le_of_injective
      (fun z : Σ a : {a // ¬grid a}, O a.val.1 => (⟨z.1.val, z.2⟩ : Σ a : LayerSamplerAxis I n, O a.1))
    intro a b hab
    rcases a with ⟨⟨a, ha⟩, x⟩
    rcases b with ⟨⟨b, hb⟩, y⟩
    cases hab
    rfl
  have hs : (∑ a : {a // ¬grid a}, Fintype.card (O a.val.1)) ≤
      Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
    simpa only [Fintype.card_sigma] using hc
  calc
    _ = ∏ a : {a // ¬grid a},
        (coefficientJetAxisReference O a.val).real (allocatedLongJetRowBox B U basis S O T a) := by
      simp only [measureReal_def, allocatedLongJetReference, allocatedLongJetBox, Measure.pi_pi, ENNReal.toReal_prod]
    _ ≤ ∏ a : {a // ¬grid a},
        ((2*T+1)^Fintype.card (O a.val.1) * allocatedLongJetOutputScale B U basis S (O := O) a) :=
      Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg)
        (fun a _ => allocatedLongJetRowBox_measure_bound B U basis S O hT a)
    _ = (2*T+1)^(∑ a : {a // ¬grid a}, Fintype.card (O a.val.1)) *
        ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith) hs)
      (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U basis S a).le))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O Q : Fin m → Type*) [∀ j, Fintype (O j)] (d : ℕ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem allocatedChart_long_rows_box {C : Fin m → ℝ} {T : ℝ}
    (hC : ∀ j, 0 ≤ C j) (hT : 0 ≤ T)
    (hchart : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hCT : ∀ j, C j * ((Fintype.card (J j) : ℝ) + 1) ≤ T)
    (z : MixedCoveredJetSource I O Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))) :
    (coefficientJetAxisSplit O I n (allocatedGridAxis (I := I) U b S.value) z.1).2 ∈
      allocatedLongJetBox B U b S O T := by
  have hc (j : Fin m) (t : O j) :
      ‖(orthonormalChart (o j) (fun i => (z.1 j).1 i t),
        fun i => ((z.1 j).2 i t : ℝ) / (basisAxisScale (b j) i : ℝ))‖ ≤ T := by
    let p := normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalChart (o j) (fun i => (z.1 j).1 i t), fun i => (z.1 j).2 i t)
    have hp : p ∈ standardLatticeClosedQuarterBox (J j) := (hz j (mem_univ _) t (mem_univ _)).1
    have hn : ‖p‖ ≤ (Fintype.card (J j) : ℝ) + 1 := by
      calc
        _ ≤ ∑ i, |p i| := euclidean_norm_le_sum_abs p
        _ ≤ ∑ _i : J j, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hp i).trans (by norm_num))
        _ ≤ _ := by simp
    have h := (hchart j p).trans ((mul_le_mul_of_nonneg_left hn (hC j)).trans (hCT j))
    change ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j))
      ((normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm _)‖ ≤ T at h
    rwa [ContinuousLinearEquiv.apply_symm_apply] at h
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change (z.1 j).1 i ∈ Metric.closedBall (0 : O j → ℝ) T
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro t
    have h := (orthonormalChart_symm_norm_le (o j)
      (orthonormalChart (o j) (fun i => (z.1 j).1 i t))).trans ((norm_fst_le _).trans (hc j t))
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    exact (norm_le_pi_norm (fun i => (z.1 j).1 i t) i).trans h
  · change (z.1 j).2 i ∈ rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (b j) i : ℝ)) T
    apply mem_rectangularWeightIndices_zero_of_norm_le _ (fun _ => basisAxisScale_cast_pos (b j) i)
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro t
    exact (norm_le_pi_norm (fun i => ((z.1 j).2 i t : ℝ) / (basisAxisScale (b j) i : ℝ)) i).trans
      ((norm_snd_le _).trans (hc j t))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem allocatedAmbient_long_rows_box {C : Fin m → ℝ} {T : ℝ}
    (hC : ∀ j, 0 ≤ C j) (hT : 0 ≤ T)
    (hchart : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hCT : ∀ j, C j * ((Fintype.card (J j) : ℝ) + 1) ≤ T)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (hz : ∀ a, |mixedJetAmbientPoint U b o z a| ≤ 1) :
    (coefficientJetAxisSplit O I n (allocatedGridAxis (I := I) U b S.value) z).2 ∈
      allocatedLongJetBox B U b S O T := by
  have hc (j : Fin m) (t : O j) :
      ‖(orthonormalChart (o j) (fun i => (z j).1 i t),
        fun i => ((z j).2 i t : ℝ) / (basisAxisScale (b j) i : ℝ))‖ ≤ T := by
    let p := normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalChart (o j) (fun i => (z j).1 i t), fun i => (z j).2 i t)
    have hn : ‖p‖ ≤ (Fintype.card (J j) : ℝ) + 1 := by
      calc
        _ ≤ ∑ i, |p i| := euclidean_norm_le_sum_abs p
        _ ≤ ∑ _i : J j, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hz ⟨j, t, i⟩)
        _ ≤ _ := by simp
    have h := (hchart j p).trans ((mul_le_mul_of_nonneg_left hn (hC j)).trans (hCT j))
    change ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j))
      ((normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm _)‖ ≤ T at h
    rwa [ContinuousLinearEquiv.apply_symm_apply] at h
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change (z j).1 i ∈ Metric.closedBall (0 : O j → ℝ) T
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro t
    have h := (orthonormalChart_symm_norm_le (o j)
      (orthonormalChart (o j) (fun i => (z j).1 i t))).trans ((norm_fst_le _).trans (hc j t))
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    exact (norm_le_pi_norm (fun i => (z j).1 i t) i).trans h
  · change (z j).2 i ∈ rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (b j) i : ℝ)) T
    apply mem_rectangularWeightIndices_zero_of_norm_le _ (fun _ => basisAxisScale_cast_pos (b j) i)
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro t
    exact (norm_le_pi_norm (fun i => ((z j).2 i t : ℝ) / (basisAxisScale (b j) i : ℝ)) i).trans
      ((norm_snd_le _).trans (hc j t))

end Erdos3.VectorPolynomial

end

end OAI
