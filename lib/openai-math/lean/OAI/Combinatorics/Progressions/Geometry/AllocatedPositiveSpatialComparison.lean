import OAI.Combinatorics.Progressions.Lattices.CoveredResidueDensityComparison
import OAI.Combinatorics.Progressions.Linear.AllocatedFixedDensityProjection
import OAI.Combinatorics.Progressions.Linear.AllocatedSpatialProjectionBudget
import OAI.Combinatorics.Progressions.Linear.PositivePhysicalProjectionError
import OAI.Combinatorics.Progressions.Probability.PhysicalDensityNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [DecidableEq (LayerSamplerVariables G I n B)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
variable (selection : α ↪ G)
variable {X : Type*} (W τ : ℝ) (N q : X → ℕ) (d : X)
variable (r : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)

local notation "vars" => LayerSamplerVariables G I n B
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "sel" => selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
local notation "A₀" => trimmedSpatialRootScale τ N q d
local notation "R₀" => trimmedSpatialSlopeScale W τ N q d
local notation "inp" => physicalSpatialInputScale (LayerSamplerVariables G I n B) A₀ R₀
local notation "out" => physicalSpatialOutputScale α A₀ R₀ (LayerSamplerScale.value S)
local notation "center" => (fun k : Option (LayerSamplerVariables G I n B) =>
  residueProfileCenter (boundedColumnResidueRepresentative q r) q (k, d))
local notation "C₀" => allocatedPhysicalEntryBudget B U basis S c

theorem allocatedTrimmedSpatial_comparison {κ ρ : ℝ} {M : ℕ}
    (hκ : 0 < κ) (hx : GoodScalarKernelTuple selection κ M x)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hN : 0 < N d) (hq : ∀ e, 0 < q e)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W) (hρ : 1 ≤ ρ)
    (hsize : 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
    (hmesh : physicalSpatialMeshCost sel C₀ 2 (affineProductProfileLip (Option vars) 1) ≤ ρ) :
    ∃ (hi : ∀ k, 0 < inp k) (ho : ∀ i, 0 < out i)
      (hp : ((physicalCubeCoefficient root dirs).submatrix id (physicalCubePivotIndex sel)).det ≠ 0)
      (hZ : 0 < shiftedSmoothProductMass center inp),
      ∀ v, |(∏ i, out i) *
          (((shiftedSmoothProductPMF center inp hi hZ).map
            (fun z => physicalCubeCoefficient root dirs *ᵥ z)) v).toReal -
        coefficientImageMask (physicalCubeCoefficient root dirs) out
          (Erdos3.selectedCoefficientDensity (physicalCubeCoefficient root dirs) (physicalCubePivotIndex sel)
            hp inp out hi ho (shiftedUnitProfile center inp)) v| ≤
        physicalSpatialErrorConstant sel M κ C₀ 2 1 (affineProductProfileLip (Option vars) 1) / ρ := by
  have hpos := trimmedSpatial_scales_pos hW hτ N q d hN (hq d)
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hlow := trimmedSpatial_scale_lower hW hρ0.le N q d (hq d) hsize
  have hL : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hr : ∀ k, |(root k : ℝ)| * R₀ ≤ A₀ := fun k =>
    trimmedSpatial_root_control hW hτ N q d hN (hq d) root
      ((allocatedPhysicalCube_root_sum B U basis S c x y).trans hbudget) k
  have hd := allocatedPhysicalCube_directions_bound B U basis S x y
  have hkernel := allocatedPhysicalCube_good_kernel B U basis S x y selection hx
  have hcenter : ∀ k, |center k| ≤ inp k := by
    intro k
    have hb := boundedColumnResidueRepresentative_bounds q hq r (k, d)
    have hq0 : (0 : ℝ) < q d := by exact_mod_cast hq d
    have hb0 : (0 : ℝ) ≤ boundedColumnResidueRepresentative q r (k, d) := by exact_mod_cast hb.1
    have ha : |center k| ≤ 1 := by
      change |-(boundedColumnResidueRepresentative q r (k, d) : ℝ) / (q d : ℝ)| ≤ 1
      rw [abs_div, abs_neg, abs_of_pos hq0, abs_of_nonneg hb0]
      apply (div_le_one hq0).mpr
      exact_mod_cast hb.2.le
    apply ha.trans (hρ.trans ?_)
    cases k
    · exact hlow.1
    · exact hlow.2
  have hctrl := physicalCube_pivot_control root dirs sel hpos.1 hpos.2 hL hκ hr hd hkernel.1
  obtain ⟨hZ, he⟩ := physicalCube_shifted_comparison root dirs sel hpos.1 hpos.2 hL hκ hρ0
    (allocatedPhysicalEntryBudget_one_le B U basis S c) hlow.1 hlow.2 hr hd
    (allocatedPhysicalCube_root_entry_bound B U basis S c x y)
    (allocatedPhysicalCube_direction_entry_bound B U basis S c x y) hkernel.1 hkernel.2 center hcenter hmesh
  exact ⟨physicalSpatialInputScale_pos vars hpos.1 hpos.2,
    physicalSpatialOutputScale_pos α hpos.1 hpos.2 hL, hctrl.1, hZ, he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [DecidableEq (LayerSamplerVariables G I n B)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
variable (selection : α ↪ G)
variable {X : Type*} (W τ : ℝ) (N q : X → ℕ) (d : X)
variable (r : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)

local notation "vars" => LayerSamplerVariables G I n B
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "sel" => selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
local notation "inp" => physicalSpatialInputScale (LayerSamplerVariables G I n B)
  (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d)
local notation "out" => physicalSpatialOutputScale α
  (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d) (LayerSamplerScale.value S)
local notation "center" => (fun k : Option (LayerSamplerVariables G I n B) =>
  residueProfileCenter (boundedColumnResidueRepresentative q r) q (k, d))
local notation "C₀" => allocatedPhysicalEntryBudget B U basis S c

omit [DecidableEq G] [DecidableEq (LayerSamplerVariables G I n B)] in
theorem allocatedPhysicalEntryBudget_le_exp {b : ℝ} (hb : 0 ≤ b)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hW : W ≤ Real.exp b) (hL : (S.value : ℝ) ≤ Real.exp b) :
    C₀ ≤ Real.exp (b + 2) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp b := by
      unfold allocatedPhysicalEntryBudget
      linarith [Real.one_le_exp hb]
    _ ≤ Real.exp b * Real.exp 2 := by nlinarith [Real.exp_nonneg b]
    _ = _ := (Real.exp_add _ _).symm

theorem allocatedTrimmedSpatial_tolerance {κ ε b : ℝ} {M : ℕ}
    (hb : 0 ≤ b) (hκ : 0 < κ) (hε : 0 < ε) (hx : GoodScalarKernelTuple selection κ M x)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hq : ∀ e, 0 < q e)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hWexp : W ≤ Real.exp b) (hLexp : (S.value : ℝ) ≤ Real.exp b)
    (hMexp : (M : ℝ) ≤ Real.exp b) (hκexp : κ⁻¹ ≤ Real.exp b)
    (hqexp : (q d : ℝ) ≤ Real.exp b) (hτexp : τ⁻¹ ≤ Real.exp b) (hεexp : ε⁻¹ ≤ Real.exp b)
    (hsize : Real.exp (physicalSpatialLogAllowance sel (b + 2) + 4 * b + 12) ≤ (N d : ℝ)) :
    ∃ (hi : ∀ k, 0 < inp k) (ho : ∀ i, 0 < out i)
      (hp : ((physicalCubeCoefficient root dirs).submatrix id (physicalCubePivotIndex sel)).det ≠ 0)
      (hZ : 0 < shiftedSmoothProductMass center inp),
      ∀ v, |(∏ i, out i) *
          (((shiftedSmoothProductPMF center inp hi hZ).map
            (fun z => physicalCubeCoefficient root dirs *ᵥ z)) v).toReal -
        coefficientImageMask (physicalCubeCoefficient root dirs) out
          (Erdos3.selectedCoefficientDensity (physicalCubeCoefficient root dirs) (physicalCubePivotIndex sel)
            hp inp out hi ho (shiftedUnitProfile center inp)) v| ≤ ε := by
  let E := physicalSpatialLogAllowance sel (b + 2)
  let ρ := Real.exp (E + b + 2)
  have hb' : 0 ≤ b + 2 := by linarith
  have hbb : Real.exp b ≤ Real.exp (b + 2) := Real.exp_le_exp.mpr (by linarith)
  have hC := allocatedPhysicalEntryBudget_le_exp B U basis S c W hb hbudget hWexp hLexp
  have hconstants := physicalSpatial_constants_le_exp sel hb' hκ
    (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c))
    (hMexp.trans hbb) (hκexp.trans hbb) hC
  have hnumerics := physicalSpatial_tolerance_numerics hb
    (physicalSpatialLogAllowance_nonneg sel hb') hW (Nat.cast_nonneg (q d))
    hτ hWexp hqexp hτexp hεexp hsize
  have hρ : 0 < ρ := Real.exp_pos _
  have htolerance := enormousCoefficient_tolerance_arithmetic (Real.exp_nonneg E) hρ hε hnumerics.2.1
  have hN : 0 < N d := by
    exact_mod_cast (Real.exp_pos (E + 4 * b + 12)).trans_le hsize
  obtain ⟨hi, ho, hp, hZ, he⟩ := allocatedTrimmedSpatial_comparison B U basis S c x y selection
    W τ N q d r hκ hx hW hτ hN hq hbudget hnumerics.1 hnumerics.2.2
    (hconstants.1.trans htolerance.1)
  refine ⟨hi, ho, hp, hZ, fun v => (he v).trans ?_⟩
  exact (div_le_div_of_nonneg_right hconstants.2 hρ.le).trans htolerance.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [DecidableEq (LayerSamplerVariables G I n B)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
variable (selection : α ↪ G)
variable {X : Type*} [Fintype X] (W τ : ℝ) (N q : X → ℕ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "sel" => selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
local notation "V" => trimmedSpatialWidths (K := vars) W τ N
local notation "width" => residueProfileWidth q V
local notation "out" => (fun d => physicalSpatialOutputScale α
  (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d) (LayerSamplerScale.value S))
local notation "center" => (fun r => residueProfileCenter (boundedColumnResidueRepresentative q r) q)
local notation "mat" => physicalCubeCoefficient root dirs
local notation "pivot" => physicalCubePivotIndex sel

theorem allocatedTrimmedSpatial_product_data {κ ε b : ℝ} {M : ℕ}
    (hb : 0 ≤ b) (hκ : 0 < κ) (hε : 0 < ε) (hx : GoodScalarKernelTuple selection κ M x)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hq : ∀ d, 0 < q d)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hWexp : W ≤ Real.exp b) (hLexp : (S.value : ℝ) ≤ Real.exp b)
    (hMexp : (M : ℝ) ≤ Real.exp b) (hκexp : κ⁻¹ ≤ Real.exp b)
    (hqexp : ∀ d, (q d : ℝ) ≤ Real.exp b) (hτexp : τ⁻¹ ≤ Real.exp b) (hεexp : ε⁻¹ ≤ Real.exp b)
    (hsize : ∀ d, Real.exp (physicalSpatialLogAllowance sel (b + 2) + 4 * b + 12) ≤ (N d : ℝ)) :
    ∃ (hV : ∀ z, 0 < V z) (hP : ∀ d i, 0 < out d i) (hp : ((mat).submatrix id pivot).det ≠ 0),
      (∀ d i, 1 ≤ out d i) ∧
      (∀ r z, |center r z| ≤ width z) ∧
      (∀ d i k, |normalizedIntegerColumns mat (fun k => width (k, d)) (out d) i k| ≤ 1) ∧
      ∀ r, ∃ hc : 0 < shiftedSmoothProductMass (center r) width,
        ∀ d v, |(∏ i, out d i) *
          (((shiftedSmoothProductPMF (fun k => center r (k, d)) (fun k => width (k, d))
            (fun k => residueProfileWidth_pos q V hq hV (k, d))
            (shiftedSmoothProductMass_slice_pos (center r) width
              (residueProfileWidth_pos q V hq hV) hc d)).map (fun z => mat *ᵥ z)) v).toReal -
          coefficientImageMask mat (out d)
            (Erdos3.selectedCoefficientDensity mat pivot hp (fun k => width (k, d)) (out d)
              (fun k => residueProfileWidth_pos q V hq hV (k, d)) (hP d)
              (shiftedUnitProfile (fun k => center r (k, d)) (fun k => width (k, d)))) v| ≤ ε := by
  have hN (d) : 0 < N d := by
    exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
  have hscales (d) := trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)
  have hL : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hL1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hP (d) := physicalSpatialOutputScale_pos α (hscales d).1 (hscales d).2 hL
  have hroot (k) : |(root k : ℝ)| * 1 ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U basis S c x y k).trans hbudget
    linarith
  have hp := (physicalCube_pivot_control root dirs sel (by linarith : 0 < 1 + W) zero_lt_one hL hκ
    hroot (allocatedPhysicalCube_directions_bound B U basis S x y)
    (allocatedPhysicalCube_good_kernel B U basis S x y selection hx).1).1
  have hlower (d) : 1 ≤ trimmedSpatialRootScale τ N q d ∧ 1 ≤ trimmedSpatialSlopeScale W τ N q d := by
    have hn := physicalSpatial_tolerance_numerics hb
      (physicalSpatialLogAllowance_nonneg sel (by linarith : 0 ≤ b + 2)) hW (Nat.cast_nonneg (q d))
      hτ hWexp (hqexp d) hτexp hεexp (hsize d)
    have hl := trimmedSpatial_scale_lower hW (zero_le_one.trans hn.1) N q d (hq d) hn.2.2
    exact ⟨hn.1.trans hl.1, hn.1.trans hl.2⟩
  have hw1 (z : Option vars × X) : 1 ≤ width z := by
    have he := congrFun (trimmedSpatial_residue_scale (K := vars) W τ N q z.2) z.1
    rw [he]
    cases z.1
    · exact (hlower z.2).1
    · exact (hlower z.2).2
  have hlocal (r) (d) := allocatedTrimmedSpatial_tolerance B U basis S c x y selection W τ N q d r
    hb hκ hε hx hW hτ hq hbudget hWexp hLexp hMexp hκexp (hqexp d) hτexp hεexp (hsize d)
  refine ⟨hV, hP, hp, ?_, ?_, ?_, ?_⟩
  · intro d i
    cases i
    · exact (hlower d).1
    · exact one_le_mul_of_one_le_of_one_le hL1 (hlower d).2
  · intro r z
    have hr := boundedColumnResidueRepresentative_bounds q hq r z
    have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
    have hr0 : (0 : ℝ) ≤ boundedColumnResidueRepresentative q r z := by exact_mod_cast hr.1
    apply le_trans (b := 1) _ (hw1 z)
    change |-(boundedColumnResidueRepresentative q r z : ℝ) / (q z.2 : ℝ)| ≤ 1
    rw [abs_div, abs_neg, abs_of_pos hq0, abs_of_nonneg hr0]
    exact (div_le_one hq0).mpr (by exact_mod_cast hr.2.le)
  · intro d i k
    rw [trimmedSpatial_residue_scale]
    exact physicalCube_normalized_entry_bound root dirs (hscales d).1 (hscales d).2 hL
      (fun k => trimmedSpatial_root_control hW hτ N q d (hN d) (hq d) root
        ((allocatedPhysicalCube_root_sum B U basis S c x y).trans hbudget) k)
      (allocatedPhysicalCube_directions_bound B U basis S x y) i k
  · intro r
    have hc : 0 < shiftedSmoothProductMass (center r) width := by
      rw [shiftedSmoothProductMass_grouped _ _ (residueProfileWidth_pos q V hq hV)]
      apply Finset.prod_pos
      intro d _
      obtain ⟨_, _, _, hz, _⟩ := hlocal r d
      simpa only [trimmedSpatial_residue_scale] using hz
    refine ⟨hc, ?_⟩
    intro d v
    obtain ⟨hi, ho, hp', hz, he⟩ := hlocal r d
    have hden : Erdos3.selectedCoefficientDensity mat pivot hp (fun k => width (k, d)) (out d)
        (fun k => residueProfileWidth_pos q V hq hV (k, d)) (hP d) =
      Erdos3.selectedCoefficientDensity mat pivot hp'
        (physicalSpatialInputScale vars (trimmedSpatialRootScale τ N q d)
          (trimmedSpatialSlopeScale W τ N q d)) (out d) hi ho := by
      congr 1
      exact trimmedSpatial_residue_scale W τ N q d
    rw [hden]
    simp_rw [trimmedSpatial_residue_scale]
    exact he v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [DecidableEq (LayerSamplerVariables G I n B)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
variable (selection : α ↪ G)
variable {X : Type*} [Fintype X] (W τ : ℝ) (N q : X → ℕ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "sel" => selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
local notation "V" => trimmedSpatialWidths (K := vars) W τ N
local notation "width" => residueProfileWidth q V
local notation "out" => (fun d => physicalSpatialOutputScale α
  (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d) (LayerSamplerScale.value S))
local notation "center" => (fun r => residueProfileCenter (boundedColumnResidueRepresentative q r) q)
local notation "mat" => physicalCubeCoefficient root dirs
local notation "pivot" => physicalCubePivotIndex sel

theorem allocatedTrimmedSpatial_product_comparison {κ ε b : ℝ} {M : ℕ}
    (hb : 0 ≤ b) (hκ : 0 < κ) (hε : 0 < ε) (hx : GoodScalarKernelTuple selection κ M x)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hq : ∀ d, 0 < q d)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hWexp : W ≤ Real.exp b) (hLexp : (S.value : ℝ) ≤ Real.exp b)
    (hMexp : (M : ℝ) ≤ Real.exp b) (hκexp : κ⁻¹ ≤ Real.exp b)
    (hqexp : ∀ d, (q d : ℝ) ≤ Real.exp b) (hτexp : τ⁻¹ ≤ Real.exp b) (hεexp : ε⁻¹ ≤ Real.exp b)
    (hsize : ∀ d, Real.exp (physicalSpatialLogAllowance sel (b + 2) + 4 * b + 12) ≤ (N d : ℝ))
    (T : Finset (ColumnResiduePattern (Option vars) X q)) (hT : T.Nonempty)
    (base : X → ℤ)
    (hsmall : (∑ _d : X, shiftedMatrixCountFactor (Unit ⊕ α) (Option vars) * ε) ≤ 1)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ v, ‖φ v‖ ≤ C) :
    ∃ (hV : ∀ z, 0 < V z) (hP : ∀ d i, 0 < out d i)
      (hp : ((mat).submatrix id pivot).det ≠ 0)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) -
        ∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
          ∫ v, (shiftedProductGridProxy (fun _ : X => mat) (fun _ => pivot) (fun _ => hp)
            (center r.val) width out (residueProfileWidth_pos q V hq hV) hP v : ℂ) *
            φ (physicalResidueReconstruct root dirs base
              (boundedColumnResidueRepresentative q r.val) q v) ∂Measure.count‖ ≤
        C * (2 * ∑ _d : X, shiftedMatrixCountFactor (Unit ⊕ α) (Option vars) * ε) := by
  obtain ⟨hV, hP, hp, hP1, ha, hentry, hcells⟩ :=
    allocatedTrimmedSpatial_product_data B U basis S c x y selection W τ N q
      hb hκ hε hx hW hτ hq hbudget hWexp hLexp hMexp hκexp hqexp hτexp hεexp hsize
  choose hc he using hcells
  have hmass (r : T) : 0 < ∑' z,
      residueSmoothWeight (columnResidueRepresentative q r.val) q V z := by
    rw [← residueSmoothWeight_mass _ q hq V hV,
      residueSmoothMass_congr _ _ q hq V hV (boundedColumnResidueRepresentative_congr q r.val)]
    exact hc r.val
  have hZ := selectedResidueSmoothWeight_mass_pos q T hT V hV hmass
  refine ⟨hV, hP, hp, hZ, ?_⟩
  have h := selectedResidue_physical_product_test_error root dirs base pivot hp q hq T V hV hZ
    (fun r => hc r.val) out hP hP1 (fun r => ha r.val) hentry (fun _ _ => ε)
    (fun r => he r.val) (fun _ => hsmall) φ hC hφ
  simpa only [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators

theorem exists_allocated_positive_spatial_comparison (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W κ : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P) (_hW : 0 ≤ W)
    (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (selection : Fin q ↪ G) (_hκ : 0 < κ) {M : ℕ}
    (_hx : GoodScalarKernelTuple selection κ M x) (_hMP : (M : ℝ) ≤ Real.exp P)
    (_hκP : κ⁻¹ ≤ Real.exp P)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ δ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P) (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    (_hsmall : (∑ _d : X, shiftedMatrixCountFactor (Unit ⊕ Fin q)
      (Option (LayerSamplerVariables G I n B)) * ε) ≤ 1)
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ) (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {cap : ℝ} (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) cap)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η) {Z : ℝ} (_hZnorm : 0 < Z),
    let V := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let sel := selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
    let out := fun d => physicalSpatialOutputScale (Fin q)
      (trimmedSpatialRootScale τ N stride d) (trimmedSpatialSlopeScale W τ N stride d) S.value
    ∀ (_hpositive : ∀ z : Option (LayerSamplerVariables G I n B) × X → ℤ,
      ‖affineCubeFourierProjection U root dirs frequency pa coeff (fun k d => (z (k, d) : ℝ)) -
        (f (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U pa hma D (fun k d => (z (k, d) : ℝ)))) : ℂ)‖ ≤ η),
    ∃ (hV : ∀ z, 0 < V z) (hOut : ∀ d i, 0 < out d i)
      (hpivot : ((physicalCubeCoefficient root dirs).submatrix id (physicalCubePivotIndex sel)).det ≠ 0)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑ r : T, (selectedResidueCellWeight stride T V r : ℂ) *
          ∫ v, (shiftedProductGridProxy (fun _ : X => physicalCubeCoefficient root dirs)
            (fun _ => physicalCubePivotIndex sel) (fun _ => hpivot)
            (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
            (residueProfileWidth stride V) out (residueProfileWidth_pos stride V hs hV) hOut v : ℂ) *
            physicalCubePositiveTest U D p hm f test
              (physicalResidueReconstruct root dirs base
                (boundedColumnResidueRepresentative stride r.val) stride v) ∂Measure.count) / (Z : ℂ)‖ ≤
          (2 * η + δ + cap * (2 * ∑ _d : X,
            shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option (LayerSamplerVariables G I n B)) * ε)) / Z := by
  classical
  obtain ⟨A₀, _, hprojection⟩ := exists_affine_cube_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((4 * Polynomial.X + Polynomial.C (q + 130 + A₀)) ^ A₀ + spatialProjectionBudget q Polynomial.X)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W κ hP hK hW hroot hWP hL
    selection hκ M hx hMP hκP y X _ _ hX hdim F _ frequency hfrequency
    coeff hcoeff p hp hm base stride hs hsP τ δ ε hτ hτP hδ hδP hε hεP
    N hsize hsmall rank hrank hRank test htest T hT density D f cap hcap η hη happrox Z hZnorm
    V root dirs pa hma sel out hpositive
  let Q := spatialSamplingBudget P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := by
    dsimp [Q, spatialSamplingBudget]
    linarith [Nat.cast_nonneg (α := ℝ) (q + 2)]
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hsiteQ : P + (q + 2 : ℕ) ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith
  have heval : Q + A₀ = 4 * P + (q + 130 + A₀ : ℕ) := by
    dsimp [Q, spatialSamplingBudget]
    push_cast
    ring
  have hsum : (Q + A₀) ^ A₀ + spatialProjectionBudget q P ≤ (P + A) ^ A := by
    rw [heval]
    simpa [spatialProjectionBudget, Polynomial.eval₂_pow] using hbudget P hP
  have hprojcost : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    linarith [spatialProjectionBudget_nonneg q hP]
  have hspatialcost : spatialProjectionBudget q P ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hQ (Nat.cast_nonneg A₀)) A₀]
  have hExp := Real.exp_le_exp.mpr hPQ
  obtain ⟨a, ha, _, hperiod⟩ := hx.2
  have hlin : LinearIndependent ℝ (fun i k => (dirs i k : ℝ)) :=
    linearIndependent_of_fixed_kernel_period (scalarCubeDifferenceMatrix x) dirs Sum.inl
      (fun _ _ => rfl) (by exact_mod_cast ha.ne') hperiod
  have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hra (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa j) :=
    (hasLayerSamplingRank_translate_iff (fun d => (base d : ℝ)) (j.val + 1)
      (fun d => (N d : ℝ)) rank (U j) (p j) (hp j)).mpr (hrank j)
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hV : ∀ z, 0 < V z := trimmedSpatialWidths_pos hW hτ N hN
  have hρP : 1 / spatialWidthFraction P τ ≤ Real.exp Q :=
    (spatialWidthFraction_inv_le hP hτ hτP).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  obtain ⟨hZ, hraw⟩ := hprojection hQ (hX.trans hPQ) (hdim.trans hPQ) U root dirs hlin
    (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
    (fun s k => (allocatedPhysicalCube_site_le_exp B U basis S c x y (hroot.trans hWP) hL s k).trans
      (Real.exp_le_exp.mpr hsiteQ)) frequency (fun a j d hd t => (hfrequency a j d hd t).trans hExp)
    coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans hExp) pa hpa hma stride hs
    (Real.exp_nonneg Q) le_rfl (spatialWidthFraction_pos P hτ) hδ hρP
    (by simpa only [one_div] using hδP.trans hExp) (fun d => (hsP d).trans hExp)
    (fun d => (N d : ℝ)) (fun d => (Real.exp_le_exp.mpr hprojcost).trans (hsize d)) hra
    ((Real.exp_le_exp.mpr hprojcost).trans hRank) 0 (by simp)
    (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun s u => htest s _)
    T hT V hV (spatialWidthFraction_le_allocated_width hP hW hWP hτ.le N)
  have hweight (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      layeredSiteWeight 0 (fun s => affineSite root dirs s)
        (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun k d => (z (k, d) : ℝ)) =
        physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) :=
    layeredSiteWeight_physicalCube root dirs base test z
  have hdirs : Matrix.of dirs = dirs := rfl
  have hfirst := selectedResidue_positive_density_projection_error U root dirs D p hp hm
    frequency coeff test htest base stride T V hV hZ density f hη happrox hpositive
    (by simpa only [hweight, hdirs, pa] using hraw)
  simp only [hdirs] at hfirst
  have hspatial (d) : Real.exp (physicalSpatialLogAllowance sel (P + 2) + 4 * P + 12) ≤ (N d : ℝ) :=
    (Real.exp_le_exp.mpr ((physicalSpatialLogAllowance_le_projection_budget sel hP hK).trans
      hspatialcost)).trans (hsize d)
  have hcap0 : 0 ≤ cap := (hcap 0).1.trans (hcap 0).2
  obtain ⟨hV', hOut, hpivot, hZ', hsecond⟩ :=
    allocatedTrimmedSpatial_product_comparison B U basis S c x y selection W τ N stride
      hP hκ hε hx hW hτ hs hroot hWP hL hMP hκP hsP hτP hεP hspatial T hT base hsmall
      (physicalCubePositiveTest U D p hm f test) hcap0
      (fun v => physicalCubePositiveTest_norm_le U D p hm f hcap test htest v)
  refine ⟨hV, hOut, hpivot, hZ, ?_⟩
  have h := (norm_sub_le_norm_sub_add_norm_sub _
    (∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
      physicalCubePositiveTest U D p hm f test (physicalCubeRootDifferences root dirs base z)) _).trans
        (add_le_add hfirst hsecond)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm]
  exact div_le_div_of_nonneg_right h hZnorm.le

end Erdos3.VectorPolynomial

end

end OAI
