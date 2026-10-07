import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileErrorMajorant
import OAI.Combinatorics.Progressions.Fourier.AllocatedProfileErrorStandardFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeSmallBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O

include hb bW

theorem allocatedProfileErrorMajorant_lintegral_mass (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|)) reference) :
    (∫⁻ y, ENNReal.ofReal (allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d y) ∂haar) ≤
      ENNReal.ofReal ((A : ℝ) * ∫ z,
        allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let fg := allocatedGridJetDensity B U b hR hσ S x u v rows
  let k := fun z => (A : ℝ) * allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * k z.1.2 * (1 : ℝ)
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows
  have hfg0 (z) : 0 ≤ fg z := (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1
  have hk0 (z) : 0 ≤ k z := mul_nonneg A.coe_nonneg
    (div_nonneg (abs_nonneg _) (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le)))
  have hki : Integrable k reference := hi.const_mul A
  have hFi : Integrable F ((μf.prod reference).prod μd) := (hfg.1.mul_prod hki).mul_prod (integrable_const 1)
  have hF0 (z) : 0 ≤ F z := mul_nonneg (mul_nonneg (hfg0 _) (hk0 _)) zero_le_one
  have hone : (∫ _ : (∀ j, O j → Q j → ZMod d), (1 : ℝ) ∂μd) = 1 := by simp
  have hFm : (∫ z, F z ∂(μf.prod reference).prod μd) = (A : ℝ) * ∫ z,
      allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference := by
    dsimp only [F]
    rw [integral_prod_mul (μ := μf.prod reference) (ν := μd)
      (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => fg z.1 * k z.2)
      (fun _ : (∀ j, O j → Q j → ZMod d) => (1 : ℝ)),
      hone, integral_prod_mul (μ := μf) (ν := reference) fg k, hfg.2, one_mul, mul_one]
    exact integral_const_mul _ _
  have he : MeasurePreserving e μraw ((μf.prod reference).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  rw [allocatedProfileErrorMajorant_chart B U b S o hR hσ x u v rows hb bW d]
  rw [mixedCoveredJet_normalized_lintegral U o b hb bW d ν _
    (fun j _ => (standardLatticeSmallBox_isOpen (J j)).measurableSet) (fun _ _ => Subset.rfl)]
  calc
    _ ≤ ∫⁻ z in region, ENNReal.ofReal (F (e z)) ∂μraw := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      change fg ((split z.1).1) * ((A : ℝ) *
          |f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) -
            g (allocatedLongJetRealCoordinates B U b S ((split z.1).2))| / scale) *
          smallBoxCutoff (mixedJetAmbientPoint U b o z.1) ≤
        fg ((split z.1).1) * k ((split z.1).2) * 1
      calc
        _ = fg ((split z.1).1) * k ((split z.1).2) *
            smallBoxCutoff (mixedJetAmbientPoint U b o z.1) := by
          dsimp only [k, allocatedUnmaskedLongProfileDensity]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (smallBoxCutoff_range _).2
          (mul_nonneg (hfg0 _) (hk0 _))
    _ ≤ ∫⁻ z, ENNReal.ofReal (F (e z)) ∂μraw := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μf.prod reference).prod μd :=
      he.lintegral_comp_emb e.measurableEmbedding (fun z => ENNReal.ofReal (F z))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0), hFm]

theorem allocatedProfileErrorMajorant_integrable_mass (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|)) reference)
    {Cf Cg Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Integrable (allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d) haar ∧
    (∫ y, allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d y ∂haar) ≤
      (A : ℝ) * ∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference := by
  let majorant := allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d
  have hp := allocatedProfileErrorTorusKernel_bounds B U b S o hR hσ x u v rows A f g hf hg hfb hgb C V hC hV
  have hm0 (y) : 0 ≤ majorant y := (hp.1 (coveredJetAmbientTorus U d y)).1
  have hmc : Continuous majorant := hp.2.continuous.comp (coveredJetAmbientTorus_continuous U d)
  have hmi : Integrable majorant haar := by
    apply (integrable_const (allocatedProfileErrorCap B U b S (O := O) A Cf Cg V : ℝ)).mono'
      hmc.measurable.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hm0 y)]
    exact (hp.1 (coveredJetAmbientTorus U d y)).2
  refine ⟨hmi, ?_⟩
  have hmass := allocatedProfileErrorMajorant_lintegral_mass B U b S o hR hσ x u v rows hb bW d ν A f g hi
  change (∫⁻ y, ENNReal.ofReal (majorant y) ∂haar) ≤ _ at hmass
  rw [← ofReal_integral_eq_lintegral_ofReal hmi (Filter.Eventually.of_forall hm0)] at hmass
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hmass
  exact mul_nonneg A.coe_nonneg (integral_nonneg (fun z => div_nonneg (abs_nonneg _)
    (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_profile_error_sampled_mass (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin q) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j)
    {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    (rows : ∀ j : Fin m, BoundedBooleanJet (Fin q) (j.val + 1) → Finset α)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (_hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (_bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (A : ℝ≥0)
    (f g : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      BoundedBooleanJet (Fin q) ((Sigma.fst (Subtype.val a)).val + 1)) → ℝ) → ℝ)
    {Cf Cg Kf Kg : ℝ≥0} (_hf : LipschitzWith Kf f) (_hg : LipschitzWith Kg g)
    (_hfb : ∀ z, |f z| ≤ Cf) (_hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := O) A Cf Cg V ≤ Real.exp P →
    Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|))
      (allocatedLongJetReference B U b S O) →
    ∀ M : ℝ,
    (A : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z
      ∂allocatedLongJetReference B U b S O) ≤ M →
    let majorant := allocatedProfileErrorMajorant B U b S o hR₀ hσ x u v rows A f g d
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => majorant (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε ∧
      ∀ error : EuclideanJetLayers U O → ℝ, (∀ y, error y ≤ majorant y) →
      selectedResidueDensityMass stride cells W
        (fun z => error (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε := by
  obtain ⟨K, hK, htest⟩ := exists_physical_jet_integral_comparison m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    G _ I _ n B _ b R₀ σ S o hR₀ hσ α _ x u v rows _ hb Q _ bW
    A f g Cf Cg Kf Kg hf hg hfb hgb C V hC hV δ L hδ hL hamb hδL O
    hLip hfreqP hcoeffP hi M hM majorant
  obtain ⟨F, inst, frequency, c, _hcard, hfreq, hsum, happrox⟩ :=
    exists_allocated_profile_error_standard_fourier B U b S o hR₀ hσ x u v rows 1 A f g
      hf hg hfb hgb C V hC hV hδ hL hamb hLip hδL
  let _ : Fintype F := inst
  simp only [Nat.cast_one, mul_one] at hfreq
  let majorant₁ := allocatedProfileErrorMajorant B U b S o hR₀ hσ x u v rows A f g 1
  have hmass := allocatedProfileErrorMajorant_integrable_mass B U b S o hR₀ hσ x u v rows
    hb bW 1 ν A f g hi hf hg hfb hgb C V hC hV
  obtain ⟨hZ, hclose⟩ := htest hP hn hdim U μ ν (by positivity) hfreqP frequency hfreq c
    (by positivity) hcoeffP hsum p hp hm 1 Nat.zero_lt_one (by simpa only [Nat.cast_one] using Real.one_le_exp hP) stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth majorant₁ hmass.1 hδ.le happrox
  have hbound : selectedResidueDensityMass stride cells W
      (fun z => majorant (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε := by
    have he := (abs_le.mp hclose).2
    have hm' : (∫ y, majorant₁ y ∂(Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))) ≤ M :=
      hmass.2.trans hM
    dsimp only [majorant]
    simp_rw [allocatedProfileErrorMajorant_sample B U b S o hR₀ hσ x u v rows A f g d p hm]
    change selectedResidueDensityMass stride cells W
      (fun z => majorant₁ (physicalCubeEuclideanSample U 1 p hm (standardPhysicalCubeOutput z))) ≤ _
    linarith
  refine ⟨hZ, hbound, ?_⟩
  intro error herr
  exact (selectedResidueDensityMass_mono stride cells W hW hZ (fun z => herr _)).trans hbound

end Erdos3.BooleanCubeKernel

end

end OAI
