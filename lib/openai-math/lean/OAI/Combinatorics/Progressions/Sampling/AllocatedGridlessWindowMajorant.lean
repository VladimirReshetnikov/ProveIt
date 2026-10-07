import OAI.Combinatorics.Progressions.Estimates.AllocatedWindowMajorant
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "covolumes" => (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

omit [Fintype α] in
theorem allocatedGridlessWindow_le_probability_majorant
    (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))
    (hW : ∀ a, selected a → (W a).Nonempty)
    (f : AllocatedLongJetRows B U b S O → ℝ)
    (E : ℝ) (hE : 0 ≤ E) (δ A : ℝ≥0)
    (hbudget : E * (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
      if selected a then ((W a).card : ℝ) else 1) ≤ δ)
    (hF : ∀ z (r : ∀ j, O j → Q j → ZMod d),
      coefficientDeckJetDensity root dirs rows d r * |f z| ≤ (A : ℝ) / longScale)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    E * |allocatedChartGridMultiplier B U b S O hb o bW d
        (allocatedGridWindowWeight B U b S O selected W p) y *
      allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y| ≤
      allocatedProbabilityMajorant B U b S o
        (allocatedGridWindowPMF B U b S O selected W p hW) δ A d y := by
  let weight := allocatedGridWindowWeight B U b S O selected W p
  let raw := fun z : MixedCoveredJetSource I O Q n d =>
    weight ((coefficientJetAxisSplit O I n grid z.1).1) *
      (E * A / longScale) / coveredJetArrayScale (O := O) U
  have hc := coveredJetArrayScale_pos (O := O) U
  have hraw : E * |allocatedChartGridMultiplier B U b S O hb o bW d weight y *
      allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y| ≤
      restrictedChartDensity chart region 1 raw y := by
    by_cases hy : y ∈ chart '' region
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [allocatedChartGridMultiplier_apply B U b S O hb o bW d weight z hz,
        allocatedGridlessCoveredProfile,
        restrictedChartDensity_apply chart region 1 _
          (mixedCoveredJetChart_injOn U o b hb bW d quarter
            (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
        restrictedChartDensity_apply chart region 1 raw
          (mixedCoveredJetChart_injOn U o b hb bW d quarter
            (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
        one_mul, one_mul]
      have hw := allocatedGridWindowWeight_nonneg B U b S O selected W p
        ((coefficientJetAxisSplit O I n grid z.1).1)
      have hd := coefficientDeckJetDensity_nonneg root dirs rows d z.2
      rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_div, abs_of_nonneg hd, abs_of_pos hc]
      calc
        _ = (E * weight ((coefficientJetAxisSplit O I n grid z.1).1)) *
            (coefficientDeckJetDensity root dirs rows d z.2 *
              |f ((coefficientJetAxisSplit O I n grid z.1).2)|) / coveredJetArrayScale (O := O) U := by ring
        _ ≤ (E * weight ((coefficientJetAxisSplit O I n grid z.1).1)) *
            ((A : ℝ) / longScale) / coveredJetArrayScale (O := O) U :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hF _ _) (mul_nonneg hE hw)) hc.le
        _ = raw z := by dsimp only [raw]; ring
    · rw [allocatedGridlessCoveredProfile,
        restrictedChartDensity_zero chart region 1 _ hy,
        restrictedChartDensity_zero chart region 1 raw hy, mul_zero, abs_zero, mul_zero]
  exact hraw.trans
    (allocatedGridWindowQuarter_le_majorant B U b S o p hb bW d
      selected W hW E δ A hbudget C V hC hV y)

end Erdos3.VectorPolynomial

end

end OAI
