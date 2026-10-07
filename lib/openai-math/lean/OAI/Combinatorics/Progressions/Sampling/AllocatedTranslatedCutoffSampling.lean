import OAI.Combinatorics.Progressions.Estimates.PhysicalRowCoverCancellation
import OAI.Combinatorics.Progressions.Probability.AllocatedNormalizedCutoffMass

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

def PhysicalAmbientRowsKernelSampling.{uX, uJ, uF} (m dim K : ℕ) (O : Fin m → Type)
    [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset (Fin dim)) : Prop :=
    ∀ {X : Type uX} [Fintype X] [DecidableEq X]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] {F : Type uF} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → JetAmbientIndex O J → ℤ) (_hfreq : ∀ a i, |(frequency a i : ℝ)| ≤ C)
    (c : F → ℂ) {A : ℝ} (_hA : 0 ≤ A) (_hAP : A ≤ Real.exp P) (_hsum : (∑ a, ‖c a‖) ≤ A)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (V : Option (Fin dim) × X → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (_hg : Integrable (fun y => g (coveredJetAmbientTorus U 1 y))
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ y, ‖(g y : ℂ) - ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • y i)‖ ≤ η),
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      |selectedResidueDensityMass stride cells V
          (fun z => g (coveredJetAmbientTorus U d
            (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)))) -
        (∫ y, g (coveredJetAmbientTorus U 1 y)
          ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))| ≤ 2 * η + ε

theorem exists_physical_standard_kernel_sampling (m dim : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ PhysicalAmbientRowsKernelSampling m dim K
      (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) (fun _ => Subtype.val) := by
  obtain ⟨K, hK, htest⟩ := exists_physical_jet_integral_comparison m dim
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ F _ P hP hn hdim U _ _ _ μ _ _ ν _ _ C hC hCP frequency hfreq c A hA hAP hsum
    p hp hm d _ stride hs R S₀ ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
    g hg η hη happrox
  have hfreq' (a : F) (j : Fin m) (e : Fin dim →₀ ℕ) (he : e.degree ≤ j.val + 1) (i : J j) :
      |(standardJetFrequency 1 (frequency a) j e i : ℝ)| ≤ C := by
    simpa only [Nat.cast_one, mul_one] using standardJetFrequency_bound 1 (frequency a) (hfreq a) j e he i
  have happrox' (y : CoefficientTorus (K := Fin dim) U) :
      ‖(g (coveredJetAmbientTorus U 1 (standardPhysicalJetMap U y)) : ℂ) -
        coefficientTorusFourierSum U (fun a => standardJetFrequency 1 (frequency a)) c y‖ ≤ η := by
    change ‖(g (coveredJetAmbientTorus U 1 (standardPhysicalJetMap U y)) : ℂ) -
      ∑ a, c a * coefficientTorusCharacter U (standardJetFrequency 1 (frequency a)) y‖ ≤ η
    simpa only [standardJetFrequency_character] using
      happrox (coveredJetAmbientTorus U 1 (standardPhysicalJetMap U y))
  obtain ⟨hZ, hclose⟩ := htest hP hn hdim U μ ν hC hCP
    (fun a => standardJetFrequency 1 (frequency a)) hfreq' c hA hAP hsum p hp hm
    1 Nat.zero_lt_one (by simpa only [Nat.cast_one] using Real.one_le_exp hP) stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
    (fun y => g (coveredJetAmbientTorus U 1 y)) hg hη happrox'
  refine ⟨hZ, ?_⟩
  simpa only [physicalCubeRowSample_standard, coveredJetAmbientTorus_sample] using hclose

theorem exists_physical_ambient_rows_kernel_sampling (m dim : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ inst : ∀ j : Fin m,
      Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)},
      @PhysicalAmbientRowsKernelSampling m dim K
        (fun j => {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)})
        inst (fun _ => Subtype.val) := by
  obtain ⟨K, hK, htest⟩ := exists_physical_standard_kernel_sampling m dim
  refine ⟨K, hK, ?_⟩
  intro inst
  exact boundedBooleanJetRows_family_transport (fun j : Fin m => j.val + 1)
    (fun O _ rows => PhysicalAmbientRowsKernelSampling m dim K O rows) (@htest) inst

theorem physicalAmbientRowsKernelSampling_of_fourier.{uX, uJ}
    {m dim K : ℕ} {O : Fin m → Type} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K O rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    {F : Type} [Fintype F]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (hcells : cells.Nonempty)
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hg : Integrable (fun y => g (coveredJetAmbientTorus U 1 y))
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    {η L A M : ℝ} (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * A ≤ Real.exp P)
    (frequency : F → JetAmbientIndex O J → ℤ) (c : F → ℂ)
    (hfreq : ∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * L + 2) ^ 4))
    (hsum : (∑ a, ‖c a‖) ≤ Real.exp (2 * L * (2 * L + 2) ^ 4) * A)
    (happrox : ∀ y, ‖(g y : ℂ) - ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • y i)‖ ≤ η)
    (hmass : (∫ y, g (coveredJetAmbientTorus U 1 y)
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ M) :
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      selectedResidueDensityMass stride cells V
        (fun z => g (coveredJetAmbientTorus U d
          (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)))) ≤ M + 2 * η + ε := by
  obtain ⟨hZ, hclose⟩ := hSampling (X := X) (J := J) (F := F) (P := P) hP hn hdim U μ ν (Real.exp_nonneg _) hfreqP frequency hfreq c
    (mul_nonneg (Real.exp_nonneg _) hA) hcoeffP hsum
    p hp hm d stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
    g hg hη happrox
  refine ⟨hZ, ?_⟩
  have he := sub_le_iff_le_add.mp ((le_abs_self _).trans hclose)
  have hadd : (2 * η + ε) + M = M + 2 * η + ε :=
    (add_comm _ _).trans (add_assoc _ _ _).symm
  exact he.trans ((add_le_add (le_refl (2 * η + ε)) hmass).trans_eq hadd)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem physicalAmbientRowsKernelSampling_difference.{uX, uJ}
    {m dim K : ℕ} {O : Fin m → Type} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K O rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (hcells : cells.Nonempty)
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    {Kf Kg Cf Cg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ y, ‖f y‖ ≤ Cf) (hgb : ∀ y, ‖g y‖ ≤ Cg)
    {δ L E : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hambient : (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L)
    (hlip : ((Kf + Kg : ℝ≥0) : ℝ) ≤ Real.exp L) (hδL : δ⁻¹ ≤ Real.exp L)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    (hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - g (coveredJetAmbientTorus U 1 y)‖
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E) :
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      selectedResidueDensityMass stride cells V
        (fun z => ‖f (coveredJetAmbientTorus U d
          (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))) -
          g (coveredJetAmbientTorus U d
          (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * δ + ε := by
  let error := fun y => ‖f y - g y‖
  have hl : LipschitzWith (Kf + Kg) error := by
    simpa only [one_mul, Function.comp_def, Pi.sub_apply] using
      lipschitzWith_one_norm.comp (hf.sub hg)
  have hb (y) : error y ≤ (Cf + Cg : ℝ≥0) :=
    (norm_sub_le _ _).trans (add_le_add (hfb y) (hgb y))
  have hlc : LipschitzWith (Kf + Kg) (fun y => (error y : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Complex.isometry_ofReal.dist_eq]
    exact hl.dist_le_mul y z
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hsum, happrox⟩ :=
    exists_ambient_torus_fourier_approximation (fun y => (error y : ℂ)) (Kf + Kg) (Cf + Cg) hlc
      (fun y => by simpa only [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ error y from norm_nonneg _)] using hb y)
      hδ hL hambient hlip hδL
  let _ := inst
  have hi : Integrable (fun y => error (coveredJetAmbientTorus U 1 y))
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) := by
    apply Integrable.of_bound (C := (Cf + Cg : ℝ≥0))
    · exact (hl.continuous.comp (coveredJetAmbientTorus_continuous U 1)).measurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hb _)
  exact physicalAmbientRowsKernelSampling_of_fourier rows hSampling hP hn hdim U μ ν p hp hm d stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth error hi
    hδ.le (NNReal.coe_nonneg _) hfreqP hcoeffP frequency coeff hfreq hsum happrox hmass

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
variable (r : ℝ≥0) (hr : 0 < r) (hR₀ : ∀ j, 0 < R₀ j) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

variable (rowSets : Fin m → Finset (Finset (Fin dim)))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

variable (hbudgetRows : ∀ j, ((rowSets j).card + 1 : ℝ) *
  (Fintype.card (Finset (Fin dim)) * (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (r : ℝ) * R₀ j)))) ≤ 1 / 4)
include hR₀ hC hbudgetRows in
theorem allocatedNormalizedCutoff_pointBudget :
    ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R₀ j)) ≤ 1 / 4 := by
  intro j
  have hc : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R₀ j)) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR₀ j).le))
  have hsite : (1 : ℝ) ≤ Fintype.card (Finset (Fin dim)) := by
    exact_mod_cast (show 1 ≤ Fintype.card (Finset (Fin dim)) from Fintype.card_pos)
  have hfirst := mul_le_mul_of_nonneg_right hsite hc
  have hrow : (1 : ℝ) ≤ (rowSets j).card + 1 := by
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hsecond := mul_le_mul_of_nonneg_right hrow (mul_nonneg (Nat.cast_nonneg (Fintype.card (Finset (Fin dim)))) hc)
  simp only [one_mul] at hfirst hsecond
  exact hfirst.trans (hsecond.trans (hbudgetRows j))

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (κ : ℝ≥0) (hκ : ∀ j, (R₀ j)⁻¹ ≤ κ)

local notation "kernelLip" => (ampN * (Fintype.card (Finset (Fin dim)) *
  (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
    (κ * ∑ j, D j * Fintype.card (J j))) * ∑ j, (Finset.card (rowSets j) : ℝ≥0))))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets r *
  (2 * ((2 : ℝ) ^ dim * (2 * (r : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

include hR₀ hσ1 hC hchart hbudgetRows hb bW hD hκ in
theorem allocatedNormalizedCutoff_sampled {K : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K rowTypes rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (hcells : cells.Nonempty)
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L)
    (hamb : (Fintype.card (JetAmbientIndex rowTypes J) : ℝ) ≤ L)
    (hηL : η⁻¹ ≤ Real.exp L) (hLip : (kernelLip : ℝ) ≤ Real.exp L)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * amp ≤ Real.exp P) :
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      selectedResidueDensityMass stride cells V
        (fun z => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
          (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖) ≤
        massCap + 2 * η + ε := by
  have hpoint := allocatedNormalizedCutoff_pointBudget r hR₀ C hC rowSets hbudgetRows
  have hfour := exists_allocated_normalized_cutoff_fourier U b o r hr hR₀ C hC hchart hpoint rowSets B S D hD κ hκ
    hη hL hamb hLip hηL
  obtain ⟨F, inst, frequency, c, _hcard, hfreq, hsum, happrox⟩ := hfour
  let _ : Fintype F := inst
  let g := allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S
  have hmass := allocatedNormalizedProductTorusCutoff_mass U b o r hr hR₀ C hC hchart rowSets B S hb bW
    1 hbudgetRows ν hσ1
  have hmass' : (∫ y, g (coveredJetAmbientTorus U 1 y)
      ∂Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) ≤ massCap := by
    simpa only [g, Fintype.card_fin] using hmass.2
  obtain ⟨hZ, hbound⟩ := physicalAmbientRowsKernelSampling_of_fourier (X := X) (J := J) (F := F) rows hSampling hP hn hdim U μ ν
    p hp hm d stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
    g hmass.1 hη.le (norm_nonneg _) hfreqP hcoeffP frequency c hfreq hsum happrox hmass'
  refine ⟨hZ, ?_⟩
  have hfunction : (fun z => g (coveredJetAmbientTorus U d
      (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)))) =
      fun z => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
        (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖ :=
    funext (fun z => allocatedNormalizedProductTorusCutoff_pullback U b o r hr hR₀ C hC hchart hpoint
      rowSets B S hb bW d (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)))
  rw [← hfunction]
  exact hbound

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
variable (r : ℝ≥0) (hr : 0 < r) (hR₀ : ∀ j, 0 < R₀ j) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

variable (rowSets : Fin m → Finset (Finset (Fin dim)))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

variable (hbudgetRows : ∀ j, ((rowSets j).card + 1 : ℝ) *
  (Fintype.card (Finset (Fin dim)) * (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (r : ℝ) * R₀ j)))) ≤ 1 / 4)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (κ : ℝ≥0) (hκ : ∀ j, (R₀ j)⁻¹ ≤ κ)

local notation "kernelLip" => (ampN * (Fintype.card (Finset (Fin dim)) *
  (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
    (κ * ∑ j, D j * Fintype.card (J j))) * ∑ j, (Finset.card (rowSets j) : ℝ≥0))))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets r *
  (2 * ((2 : ℝ) ^ dim * (2 * (r : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

include hR₀ hσ1 hC hchart hbudgetRows hb bW hD hκ in
theorem allocatedNormalizedCutoff_sampled_translate {K : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K rowTypes rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (hcells : cells.Nonempty)
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L)
    (hamb : (Fintype.card (JetAmbientIndex rowTypes J) : ℝ) ≤ L)
    (hηL : η⁻¹ ≤ Real.exp L) (hLip : (kernelLip : ℝ) ≤ Real.exp L)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * amp ≤ Real.exp P)
    (base : X → ℤ) :
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      selectedResidueDensityMass stride cells V
        (fun z => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
          (physicalCubeRowSample U d rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤
        massCap + 2 * η + ε := by
  have hp' (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1)
      (translate (fun t => (base t : ℝ)) (p j)) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ _ (hp j)
  have hrank' (j : Fin m) : HasLayerSamplingRank (j.val + 1) H R
      (U j) (translate (fun t => (base t : ℝ)) (p j)) :=
    (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
  obtain ⟨hZ, hbound⟩ := allocatedNormalizedCutoff_sampled (X := X) (J := J) B U b o S r hr hR₀ hσ1 C hC hchart
    rowSets hbudgetRows hb bW D hD κ hκ hSampling hP hn hdim μ ν
    (fun j => translate (fun t => (base t : ℝ)) (p j)) hp'
    (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
    d stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank' hR cells hcells V hV hwidth
    hη hL hamb hηL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  have hfunction :
      (fun z => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
        (physicalCubeRowSample U d rows (fun j => translate (fun t => (base t : ℝ)) (p j))
          (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
          (standardPhysicalCubeOutput z))‖) =
      fun z => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
        (physicalCubeRowSample U d rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖ :=
    funext (fun z => congrArg
      (fun y => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y‖)
      (physicalCubeRowSample_translate U d rows p hm base (standardPhysicalCubeOutput z)))
  rw [hfunction] at hbound
  exact hbound

end Erdos3.BooleanCubeKernel

end

end OAI
