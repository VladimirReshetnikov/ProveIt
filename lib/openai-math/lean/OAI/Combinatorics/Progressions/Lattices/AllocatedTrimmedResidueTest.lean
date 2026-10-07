import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_site_mass_bound {K X Y : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (T : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (S : Finset Y) (φ : T → Y → ℂ) {A E B C : ℝ}
    (hA : 0 < A) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hφ : ∀ a v, v ∈ S → ‖φ a v‖ ≤ B) (hcard : (S.card : ℝ) ≤ C * A) :
    (∑ a : T, selectedResidueCellWeight q T V a * ((E / A) * ∑ v ∈ S, ‖φ a v‖)) ≤
      B * E * C := by
  have hpart (a : T) : (E / A) * (∑ v ∈ S, ‖φ a v‖) ≤ B * E * C := by
    have hs : (∑ v ∈ S, ‖φ a v‖) ≤ B * S.card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
        Finset.sum_le_sum (fun v hv => hφ a v hv)
    calc
      _ ≤ (E / A) * (B * S.card) := mul_le_mul_of_nonneg_left hs (div_nonneg hE hA.le)
      _ ≤ (E / A) * (B * (C * A)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcard hB) (div_nonneg hE hA.le)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ a : T, selectedResidueCellWeight q T V a * (B * E * C) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpart a)
        (selectedResidueCellWeight_nonneg q T V a))
    _ = (∑ a : T, selectedResidueCellWeight q T V a) * (B * E * C) := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [selectedResidueCellWeight_sum q T V hV hmass, one_mul]

theorem physicalCenteredResidueMixture_site_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d)
    (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (he : ∀ v ∈ centeredPhysicalCubeWindow root D (residueProfileWidth q V),
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D)) v).toReal : ℝ) : ℂ) -
        ψ v‖ ≤ E) :
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let window := centeredPhysicalCubeWindow root D Q
    let F := fun r : T => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative q r.val) q
    ‖(∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
          φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F r v)) / (Z : ℂ)‖ ≤
      (∑ r : T, selectedResidueCellWeight q T V r *
        ((E / A) * ∑ v ∈ window, ‖φ (F r v)‖)) / Z := by
  classical
  intro Q hQ window F
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg q T V r)]
  exact mul_le_mul_of_nonneg_left
    (smoothPhysicalResidue_site_error root D base (boundedColumnResidueRepresentative q r.val)
      q Q hQ ψ φ hA he) (selectedResidueCellWeight_nonneg q T V r)

theorem physicalSelectedResidue_site_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d)
    (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z B : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B)
    (he : ∀ v ∈ centeredPhysicalCubeWindow root D (residueProfileWidth q V),
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D)) v).toReal : ℝ) : ℂ) -
        ψ v‖ ≤ E) :
    let window := centeredPhysicalCubeWindow root D (residueProfileWidth q V)
    let F := fun r : T => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative q r.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F r v)) / (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : Option K × X, (q z.2 : ℝ) / V z)) / Z +
      (∑ r : T, selectedResidueCellWeight q T V r *
        ((E / A) * ∑ v ∈ window, ‖φ (F r v)‖)) / Z := by
  intro window F
  have hrec := physicalSelectedResidue_recenter_test root D base q hq T V hV hmass hlarge φ hB hφ hZ
  have hsite := physicalCenteredResidueMixture_site_error root D base q hq T V hV ψ φ hA hZ he
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hrec hsite)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_coefficient_tail {K X Y : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (window : Finset Y) (ψ : Y → ℂ) (test : cells → Y → ℂ)
    (error : cells → Y → ℝ) {A C E Cwin : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hψ : ∀ v ∈ window, ‖ψ v‖ ≤ C) (htest : ∀ a v, ‖test a v‖ ≤ 1)
    (herror : ∀ a v, error a v ≤ E) (hcard : (window.card : ℝ) ≤ Cwin * A) :
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test t.1 t.2.val‖ * error t.1 t.2.val) ≤ C * E * Cwin := by
  have hφ (a : cells) (v : Y) (hv : v ∈ window) : ‖ψ v * test a v‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul (hψ v hv) (htest a v) (norm_nonneg _) hC).trans_eq (mul_one _)
  calc
    _ ≤ ∑ t : cells × window,
        ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
          test t.1 t.2.val‖ * E :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (herror t.1 t.2.val) (norm_nonneg _))
    _ = ∑ a : cells, selectedResidueCellWeight stride cells V a *
        ((E / A) * ∑ v ∈ window, ‖ψ v * test a v‖) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_coe_sort window (fun v => ‖ψ v * test a v‖),
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [norm_mul, norm_div, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (selectedResidueCellWeight_nonneg stride cells V a), abs_of_pos hA]
      ring
    _ ≤ _ := selectedResidue_site_mass_bound stride cells V hV hmass window
      (fun a v => ψ v * test a v) hA hE hC hφ hcard

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_coefficient_tail_of_window_mass {K X Y : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (window : Finset Y) (ψ : Y → ℂ) (test : cells → Y → ℂ)
    (error : cells → Y → ℝ) {A C E : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ C) (htest : ∀ a w, ‖test a w‖ ≤ 1)
    (herror : ∀ a w, 0 ≤ error a w)
    (hmass : ∀ a, (∑ w ∈ window, error a w) ≤ E * A) :
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test t.1 t.2.val‖ * error t.1 t.2.val) ≤ C * E := by
  have hcell (a : cells) :
      (∑ w : window, ‖(selectedResidueCellWeight stride cells V a : ℂ) *
        (ψ w.val / (A : ℂ)) * test a w.val‖ * error a w.val) ≤
      selectedResidueCellWeight stride cells V a * (C * E) := by
    let w := selectedResidueCellWeight stride cells V a
    have hw : 0 ≤ w := selectedResidueCellWeight_nonneg stride cells V a
    have hn (v : window) :
        ‖(w : ℂ) * (ψ v.val / (A : ℂ)) * test a v.val‖ ≤ w / A * C := by
      have ht : ‖ψ v.val‖ * ‖test a v.val‖ ≤ C :=
        (mul_le_mul (hψ v.val v.property) (htest a v.val) (norm_nonneg _) hC).trans_eq (mul_one C)
      calc
        _ = w / A * (‖ψ v.val‖ * ‖test a v.val‖) := by
          simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hw, abs_of_pos hA]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ht (div_nonneg hw hA.le)
    calc
      _ ≤ ∑ v : window, (w / A * C) * error a v.val :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (hn v) (herror a v.val))
      _ = (w / A * C) * ∑ v ∈ window, error a v := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort]
      _ ≤ (w / A * C) * (E * A) :=
        mul_le_mul_of_nonneg_left (hmass a) (mul_nonneg (div_nonneg hw hA.le) hC)
      _ = w * (C * E) := by field_simp [hA.ne']
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V a * (C * E) :=
      Finset.sum_le_sum (fun a _ => hcell a)
    _ = _ := by rw [← Finset.sum_mul, selectedResidueCellWeight_sum stride cells V hV hZ, one_mul]

theorem referenceErrorVolumeFactor_bound (q : ℕ) (X : Type*) [Fintype X]
    {W L D : ℝ} (hW : 0 ≤ W) (hL : 1 ≤ L) (hWL : W ≤ D * L) :
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
        (((1 + W) / L) ^ q) ^ Fintype.card X ≤
      (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
        ((1 + D) ^ q) ^ Fintype.card X := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hratio : (1 + W) / L ≤ 1 + D := (div_le_iff₀ hL0).mpr (by nlinarith)
  have hratio0 : 0 ≤ (1 + W) / L := div_nonneg (by linarith) hL0.le
  have hprofile := smoothProbabilityProfile_pos_zero
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (pow_nonneg hratio0 q) (pow_le_pow_left₀ hratio0 hratio q) _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedTrimmedSpatial_selected_site_test (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * (1 + W))
    (hprincipalDir : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * S.value)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (hr : 0 < r) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (trimmedSpatialWidths W τ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {Cφ Z : ℝ}
    (hCφ : 0 ≤ Cφ) (hφ : ∀ v, ‖φ v‖ ≤ Cφ) (hZ : 0 < Z) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := trimmedSpatialWidths (K := vars) W τ N
    let hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
    let Q := residueProfileWidth q V
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ d,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix cols modulus))) modulus f (H d) 3 r (v d)
    let A := ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let E := Fintype.card X * (E₀ + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
      (1 + G₀ * anisotropicSpatialDensityCap selection κ + E₀) ^ Fintype.card X
    let Cwin := 7 ^ Fintype.card (X × (Unit ⊕ α)) *
      (((1 + W) / (S.value : ℝ)) ^ Fintype.card α) ^ Fintype.card X
    let window := centeredPhysicalCubeWindow root dirs Q
    let F := fun a : cells => physicalResidueReconstruction root dirs base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      Cφ * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option vars × X) / ρ + E * Cwin) / Z := by
  classical
  intro H T V hV Q hpivot f ψ A E₀ G₀ E Cwin window F
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hA : 0 < A := Finset.prod_pos (fun d _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hH d) (hT d) (Nat.cast_pos.mpr S.positive) i))
  have hwindow (v) (hv : v ∈ window) :=
    allocatedTrimmedSpatial_window_bound B U basis S c x y N q hN hq hW hτ hbudget v hv
  have he (v) (hv : v ∈ window) :
      ‖((A * (((smoothProductPMF Q (residueProfileWidth_pos q V hq hV)).map
        (centeredPhysicalCubeMap root dirs)) v).toReal : ℝ) : ℂ) - ψ v‖ ≤ E :=
    allocatedTrimmedSpatial_vector_site_error B U basis S c x y selection N q hN hq
      hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ0 hξ1 hprincipalRoot hprincipalDir hsize hmesh
      modulus hperiod (by norm_num : (0 : ℝ) < 3) hr v (hwindow v hv)
  have hρ1 : 1 ≤ ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hcard : (window.card : ℝ) ≤ Cwin * A :=
    spatialStarWindow_card_anisotropic window H T
      (fun d => hρ1.trans (trimmedSpatial_scale_lower hW hρ.le N q d (hq d) (hsize d)).1)
      (Nat.cast_ne_zero.mpr S.positive.ne') (fun d => trimmedSpatial_scale_ratio hW N q d) hwindow
  have hE₀ : 0 ≤ E₀ := anisotropicSpatialError_nonneg selection _ M hκ.le
    (zero_le_one.trans hC₀) hρ.le hξ0
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ.le
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ.le
  have hE : 0 ≤ E := by dsimp only [E, G₀]; positivity
  have hmassBound := selectedResidue_site_mass_bound q cells V hV hmass window
    (fun a v => φ (F a v)) hA hE hCφ (fun _ _ _ => hφ _) hcard
  have hrec := physicalSelectedResidue_trimmed_recenter root dirs base q N hq hN cells
    hW hτ hρ8 hsize hmass φ hCφ hφ hZ
  have hsite := physicalCenteredResidueMixture_site_error root dirs base q hq cells V hV ψ φ hA hZ he
  have h := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hrec (hsite.trans (div_le_div_of_nonneg_right hmassBound hZ.le)))
  exact h.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
