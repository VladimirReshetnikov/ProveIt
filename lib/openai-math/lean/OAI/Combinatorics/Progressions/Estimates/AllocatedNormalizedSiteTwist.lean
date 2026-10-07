import OAI.Combinatorics.Progressions.Lattices.AllocatedGridResidueRefinement

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

def normalizedSiteTwistProduct {X Y : Type*} (f : X → ℂ) (g : Y → ℂ) (v : X × Y) : ℂ :=
  f v.1 * g v.2

theorem normalizedSiteTwistProduct_bounds {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℂ) (g : Y → ℂ) {Lf Lg : ℝ≥0}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hnf : ∀ x, ‖f x‖ ≤ 1) (hng : ∀ y, ‖g y‖ ≤ 1) :
    (∀ v, ‖normalizedSiteTwistProduct f g v‖ ≤ 1) ∧
      LipschitzWith (Lf + Lg) (normalizedSiteTwistProduct f g) := by
  have h1 : LipschitzWith Lf (fun v : X × Y => f v.1) := by
    simpa only [mul_one, Function.comp_def] using hf.comp LipschitzWith.prod_fst
  have h2 : LipschitzWith Lg (fun v : X × Y => g v.2) := by
    simpa only [mul_one, Function.comp_def] using hg.comp LipschitzWith.prod_snd
  refine ⟨?_, ?_⟩
  · intro v
    rw [normalizedSiteTwistProduct, norm_mul]
    exact (mul_le_mul (hnf _) (hng _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have h := lipschitz_mul_of_bounds _ _ h1 h2 (Bf := 1) (Bg := 1)
      (fun v => hnf v.1) (fun v => hng v.2)
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [normalizedSiteTwistProduct, one_mul, add_comm] using h.dist_le_mul v w

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {A α : Type*} [Fintype A] [Fintype α] (e : A → ScalarSiteExpansion (Finset α))
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (r : ℝ≥0) (hr : 0 < r) (k : ∀ a, (e a).Term) (s : Finset α)
variable (f : (LayerSamplerAxis I n → ℝ) → ℂ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j a, coefficients (p j) a ∈ U j) (u : X → ℤ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "base" => (fun w : MixedCoveredJetSource I single E n d =>
  fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit ((Prod.fst w) j) ())

variable {Ksp : Type*} [Fintype Ksp]
variable (root : Ksp → ℤ) (spatialD : Matrix α Ksp ℤ) (spatialBase : X → ℤ)
variable [Fintype X] (spatialResidue : Option Ksp × X → ℤ) (q : X → ℕ)
variable (box : ℝ) (mesh : ℝ≥0) (H N : X → ℝ) {spatialModulus : ℕ}
variable (t : X → SpatialSiteLabel α spatialModulus box mesh)
variable [∀ a, NeZero ((e a).period (k a))]

theorem allocatedPhysicalSiteTwist_normalized
    (g : (((Σ j, J j) → UnitAddCircle) → ℂ))
    (hg : ∀ (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g (fun a => ((((u₀ a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
          (fun a => ((w₀ (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (period : ℕ) (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d)
    (hw : w ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)))
    (hphysical : chart w = physicalSingleSiteValue U d p hm (fun x => (u x : ℝ)))
    (hN : ∀ x, N x ≠ 0) :
    let gridResidue : ∀ a, ZMod ((e a).period (k a)) :=
      fun a => ((base w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a)))
    let coord := allocatedFullMixedSiteValue (R := R) U b (base w)
    let smooth := physicalResidueSpatialSmooth root spatialD spatialBase spatialResidue q box mesh H N t s
    (physicalResidueSpatialSiteFactor root spatialD spatialBase spatialResidue q box mesh H t s u *
      g (fun a => (((eval (fun x => (u x : ℝ)) (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) *
      allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
        (physicalSingleSiteValue U d p hm (fun x => (u x : ℝ))) =
      (physicalResidueSpatialMask root spatialD spatialBase spatialResidue q box mesh t s u *
        (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0)) *
        ∑ gridLabel : ∀ a, ZMod ((e a).period (k a)),
          (if gridResidue = gridLabel then (1 : ℂ) else 0) *
            normalizedSiteTwistProduct smooth
              (allocatedNormalizedGridIdealFactor B U b S e selected r hr k s gridLabel f)
              ((fun x => (u x : ℝ) / N x), coord) := by
  intro gridResidue coord smooth
  have hsum : (∑ gridLabel : ∀ a, ZMod ((e a).period (k a)),
      (if gridResidue = gridLabel then (1 : ℂ) else 0) *
        normalizedSiteTwistProduct smooth
          (allocatedNormalizedGridIdealFactor B U b S e selected r hr k s gridLabel f)
          ((fun x => (u x : ℝ) / N x), coord)) =
      normalizedSiteTwistProduct smooth
        (allocatedNormalizedGridIdealFactor B U b S e selected r hr k s gridResidue f)
        ((fun x => (u x : ℝ) / N x), coord) := by simp
  rw [hsum, mul_assoc]
  rw [allocatedNormalizedGridIdealFactor_physical B U b S e selected r hr k s f
    o hb bW d p hm (fun x => (u x : ℝ)) g hg period label w hw hphysical]
  rw [physicalResidueSpatialSiteFactor_normalized root spatialD spatialBase spatialResidue q
    box mesh H N t s hN u]
  dsimp only [normalizedSiteTwistProduct, smooth, coord, gridResidue]
  ring

end Erdos3.VectorPolynomial

end

end OAI
