import OAI.Combinatorics.Progressions.Lattices.ForecastJointNativeResidue
import OAI.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
import OAI.Combinatorics.Progressions.Sampling.ForecastActiveGridIntegralComparison
import OAI.Combinatorics.Progressions.Sampling.ForecastActualPhysicalSourceContinuous

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*}

theorem forecastInactiveFixedOutput_congr_selected
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : ∀ a (b : B ⟨(selected a).1, Sum.inr (selected a).2⟩)
      (v : Fin ((selected a).1.val + 1)) (o : Option Empty),
      y ⟨⟨(selected a).1, Sum.inr (selected a).2⟩, b, v⟩ o =
        y' ⟨⟨(selected a).1, Sum.inr (selected a).2⟩, b, v⟩ o) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' := by
  funext a row
  have hmoderate := (hsmall a).trans (Nat.pow_le_pow_right S.positive
    ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  unfold forecastInactiveFixedOutput
  rw [allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
    hmoderate (c a) (hc a) x y,
    allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
      hmoderate (c a) (hc a) x' y']
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply congrArg (fun f => integerBooleanBlockJet f (row : Finset Empty))
  funext v o
  exact congrArg Subtype.val (hy a b v o)

theorem forecastInactiveFixedOutput_congr_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (P : LayerSamplerAxis I n → Prop)
    (hselected : ∀ a, P ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : principalAxisRestrict P y = principalAxisRestrict P y') :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' := by
  apply forecastInactiveFixedOutput_congr_selected B U basis S hR hσ
    selected hsmall c hc x x' y y'
  intro a b v o
  exact congrFun (congrFun hy ⟨⟨_, hselected a⟩, b, v⟩) o

theorem forecastInactiveFixedOutput_congr_short_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : principalAxisRestrict (allocatedShortAxis U basis S.value) y =
      principalAxisRestrict (allocatedShortAxis U basis S.value) y') :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' :=
  forecastInactiveFixedOutput_congr_restrict B U basis S hR hσ selected hsmall c hc
    (allocatedShortAxis U basis S.value) hsmall x x' y y' hy

theorem forecastInactiveFixedOutput_join_short_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (v : PrincipalAxisTuples (α := Empty) (fun a => ¬allocatedShortAxis U basis S.value a)
      (allocatedPrincipalSides B U basis S)) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x
        (principalAxisJoin (allocatedShortAxis U basis S.value)
          (principalAxisRestrict (allocatedShortAxis U basis S.value) y) v) := by
  apply forecastInactiveFixedOutput_congr_short_restrict B U basis S hR hσ
    selected hsmall c hc x x
  rw [principalAxisRestrict_join_left]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*}

noncomputable def forecastInactiveShortGrid
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (u : PrincipalAxisTuples (α := Empty) (allocatedShortAxis U basis S.value)
      (allocatedPrincipalSides B U basis S)) :
    A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ :=
  forecastInactiveFixedOutput B U basis S selected c
    (fun _ => integerScalarCubeBoxZero Empty S.value S.positive)
    (principalAxisJoin (allocatedShortAxis U basis S.value) u
      (fun j => integerScalarCubeBoxZero Empty
        (allocatedPrincipalSides B U basis S ⟨j.1.val, j.2⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)))

theorem forecastInactiveFixedOutput_eq_shortGrid
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S)) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveShortGrid B U basis S selected c
        (principalAxisRestrict (allocatedShortAxis U basis S.value) y) := by
  unfold forecastInactiveShortGrid
  apply forecastInactiveFixedOutput_congr_short_restrict B U basis S hR hσ
    selected hsmall c hc
  exact (principalAxisRestrict_join_left (allocatedShortAxis U basis S.value) _ _).symm

theorem forecastInactiveFixedOutput_eq_shortGrid_comp
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value) :
    forecastInactiveFixedOutput B U basis S selected c x =
      forecastInactiveShortGrid B U basis S selected c ∘
        principalAxisRestrict (allocatedShortAxis U basis S.value) := by
  funext y
  exact forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hsmall c hc x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

theorem forecastInactiveSampleGrid_integer_eval (a : A)
    (row : ((Finset.univ : Finset (Finset Empty)) : Type)) :
    forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x y a row =
    MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (∑ d, MvPolynomial.monomial d.val ((sample (selected a).1).2 (selected a).2 d)) := by
  change (integerJetMatrix
    (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) => MvPolynomial.monomial d.val (1 : ℤ))
    (integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y))
    (fun t : ((Finset.univ : Finset (Finset Empty)) : Type) => t.val) *ᵥ
    allocatedOriginalSampleInactiveCoefficients B selected sample a) row = _
  rw [integerJetMatrix_apply_coefficients]
  simp only [MvPolynomial.C_mul_monomial, mul_one,
    allocatedOriginalSampleInactiveCoefficients]
  rw [Subsingleton.elim (row.val : Finset Empty) ∅]
  have hv : integerAffineCube
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (∅ : Finset Empty) =
      allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y := by
    funext v
    simp [integerAffineCube]
  simp only [booleanCoefficient, Finset.powerset_empty, Finset.sum_singleton,
    Finset.sdiff_self, Finset.card_empty, pow_zero, one_mul, hv]

theorem forecastInactiveSampleGrid_real_eval (a : A)
    (row : ((Finset.univ : Finset (Finset Empty)) : Type)) :
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x y a row : ℝ) =
    MvPolynomial.eval (fun v =>
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y v : ℝ))
      (monomialArrayPolynomial Subtype.val
        (fun d => ((sample (selected a).1).2 (selected a).2 d : ℝ))) := by
  rw [forecastInactiveSampleGrid_integer_eval B U basis S selected sample x y a row]
  simp only [monomialArrayPolynomial, map_sum, MvPolynomial.eval_monomial,
    Finsupp.prod, Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]

theorem forecastInactiveSampleGrid_eq_physicalMixedValue :
    forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x y =
      fun a _ =>
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y (selected a).1).2
          (selected a).2 := by
  funext a row
  rw [forecastInactiveSampleGrid_integer_eval B U basis S selected sample x y a row,
    allocatedOriginalSamplePhysicalMixedValue_integer]

theorem forecastInactiveSampleShortGrid_eq_physicalMixedValue
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j)
      (sample j)) :
    forecastInactiveShortGrid B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample)
      (principalAxisRestrict (allocatedShortAxis U basis S.value) y) =
      fun a _ =>
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y (selected a).1).2
          (selected a).2 := by
  rw [← forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hsmall
    (allocatedOriginalSampleInactiveCoefficients B selected sample)
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs) x y]
  exact forecastInactiveSampleGrid_eq_physicalMixedValue B U basis S selected sample x y

theorem forecastInactiveSampleShortGrid_real_eval
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j)
      (sample j))
    (a : A) (row : ((Finset.univ : Finset (Finset Empty)) : Type)) :
    (forecastInactiveShortGrid B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample)
      (principalAxisRestrict (allocatedShortAxis U basis S.value) y) a row : ℝ) =
    MvPolynomial.eval (fun v =>
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y v : ℝ))
      (monomialArrayPolynomial Subtype.val
        (fun d => ((sample (selected a).1).2 (selected a).2 d : ℝ))) := by
  rw [← forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hsmall
    (allocatedOriginalSampleInactiveCoefficients B selected sample)
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs) x y]
  exact forecastInactiveSampleGrid_real_eval B U basis S selected sample x y a row

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

def forecastShortGridSheet (grid : Grid) :
    ∀ j, {i : Fin (n j) // short ⟨j, .inr i⟩} → ℤ :=
  fun j i => grid ⟨⟨j, i.val⟩, i.property⟩ ⟨∅, Finset.mem_univ _⟩

noncomputable def forecastShortGridNormalized (R : Fin m → ℝ) (grid : Grid) :
    {a : LayerSamplerAxis I n // short a} → ℝ := fun a =>
  let i := (allocatedShortIntegerAxisEquiv (I := I) U b Lsize).symm a
  (grid i ⟨∅, Finset.mem_univ _⟩ : ℝ) / basisAxisScale (b i.val.1) i.val.2 / R i.val.1

omit [∀ j, Fintype (I j)] in
theorem forecastShortGridSheet_of_mixed
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastShortGridSheet (I := I) U b Lsize (fun a _ => (w a.val.1).2 a.val.2) =
      fun j i => (w j).2 i.val := rfl

omit [∀ j, Fintype (I j)] in
theorem forecastShortGridNormalized_of_mixed (R : Fin m → ℝ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastShortGridNormalized U b Lsize R (fun a _ => (w a.val.1).2 a.val.2) =
      fun a => allocatedFullMixedSiteValue (R := R) U b w a.val := by
  funext a
  rcases a with ⟨⟨j, i⟩, ha⟩
  cases i with
  | inl i => exact False.elim ha
  | inr i => rfl

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

noncomputable def forecastShortGridTest (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) : Domain → ℂ :=
  W.forecastResidueTest U b hb o bW R short q hm hperiod hcover
    (forecastShortGridSheet U b Lsize grid)
    (forecastShortGridNormalized U b Lsize R grid) center τ out

theorem forecastShortGridTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out y‖ ≤ 1) ∧
      LipschitzWith (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out) :=
  W.forecastResidueTest_bounds U b hb o bW R short q hm hperiod hcover _ _ center τ out

theorem forecastShortGridTest_eq_eval (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hR : ∀ j, R j ≠ 0) (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (poly j) a ∈ U j)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ j, BooleanCubeKernel.physicalSingleSiteValue U W.cover poly hmem (fun x => (u x : ℝ)) j () =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) W.cover
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) W.cover (deck j))) :
    W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover
      (fun x => (base x : ℝ) / N x) τ (fun a _ => (w a.val.1).2 a.val.2)
      (fun a => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (w j).2 (deck j)) a : ZMod q))
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      W.eval N poly u := by
  unfold forecastShortGridTest
  rw [forecastShortGridSheet_of_mixed, forecastShortGridNormalized_of_mixed]
  exact W.forecastResidueTest_eq_eval U b hb o bW R short q hm hperiod hcover
    hR base u N hN hτ w deck poly hmem hchart

end NormalizedPolynomialTwist

section OriginalSample
variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (v : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S))

include hR hσ hs in
theorem forecastShortGridSheet_originalSample :
    forecastShortGridSheet (I := I) U b S.value
      (forecastInactiveShortGrid B U b S (allocatedShortIntegerSelection U b S.value)
        (allocatedOriginalSampleInactiveCoefficients B (allocatedShortIntegerSelection U b S.value) sample)
        (principalAxisRestrict (allocatedShortAxis U b S.value) v)) =
      fun j i => (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v j).2 i.val := by
  rw [forecastInactiveSampleShortGrid_eq_physicalMixedValue B U b S
    (allocatedShortIntegerSelection U b S.value) sample x v hR hσ
    (allocatedShortIntegerSelection_small U b S.value) hs]
  rfl

include hR hσ hs in
theorem forecastShortGridNormalized_originalSample :
    forecastShortGridNormalized U b S.value R
      (forecastInactiveShortGrid B U b S (allocatedShortIntegerSelection U b S.value)
        (allocatedOriginalSampleInactiveCoefficients B (allocatedShortIntegerSelection U b S.value) sample)
        (principalAxisRestrict (allocatedShortAxis U b S.value) v)) =
      fun a => allocatedFullMixedSiteValue (R := R) U b
        (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v) a.val := by
  rw [forecastInactiveSampleShortGrid_eq_physicalMixedValue B U b S
    (allocatedShortIntegerSelection U b S.value) sample x v hR hσ
    (allocatedShortIntegerSelection_small U b S.value) hs]
  exact forecastShortGridNormalized_of_mixed U b S.value R
    (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

include hR hσ hs in

theorem forecastShortGridTest_originalSample_eq_eval
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0) (deck : ∀ j, E j → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (poly j) a ∈ U j)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ j, BooleanCubeKernel.physicalSingleSiteValue U W.cover poly hmem (fun x => (u x : ℝ)) j () =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) W.cover
          (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v j),
            integerResidueMap (E j) W.cover (deck j))) :
    W.forecastShortGridTest U b S.value hb o bW R q hm hperiod hcover
      (fun z => (base z : ℝ) / N z) τ
      (forecastInactiveShortGrid B U b S (allocatedShortIntegerSelection U b S.value)
        (allocatedOriginalSampleInactiveCoefficients B (allocatedShortIntegerSelection U b S.value) sample)
        (principalAxisRestrict (allocatedShortAxis U b S.value) v))
      (fun a => (forecastCongruenceOutput (R := ℤ) (allocatedShortAxis (I := I) U b S.value) u
        (fun j => Sum.elim (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v j).2
          (deck j)) a : ZMod q))
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : (Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) =>
          allocatedFullMixedSiteValue (R := R) U b
            (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v) a.1.val) =
      W.eval N poly u := by
  rw [forecastInactiveSampleShortGrid_eq_physicalMixedValue B U b S
    (allocatedShortIntegerSelection U b S.value) sample x v hR hσ
    (allocatedShortIntegerSelection_small U b S.value) hs]
  exact W.forecastShortGridTest_eq_eval U b S.value hb o bW R q hm hperiod hcover
    (fun j => (hR j).ne') base u N hN hτ
    (allocatedOriginalSamplePhysicalMixedValue B U b S sample x v) deck poly hmem hchart

end NormalizedPolynomialTwist
end OriginalSample
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

private theorem real_divisor_nsmul_circle (N d : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hdiv : d ∣ N) (a : ℝ) :
    (N / d) • ((a / N : ℝ) : UnitAddCircle) = ((a / d : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((N / d : ℕ) : ℝ) * d = N := by exact_mod_cast Nat.div_mul_cancel hdiv
  rw [← mul_div_assoc]
  apply (div_eq_div_iff hn hd0).mpr
  calc
    ((N / d : ℕ) : ℝ) * a * d = a * (((N / d : ℕ) : ℝ) * d) := by ring
    _ = a * N := by rw [he]

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem forecastNativeCoveredChart_commonCover_ambient
    (N d : ℕ) [NeZero N] (hd : 0 < d) (hdiv : d ∣ N)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ)
    (a : Σ j, J j) :
    coveredJetAmbientTorus U (N / d)
      (fun j (_ : Unit) => normalizedCoveredChart (euclideanSubspace (U j))
        (basis j) (hb j) (bW j) N
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) N (deck j)))
      ⟨a.1, (), a.2⟩ =
      (((normalizedLatticePoint (euclideanSubspace (U a.1)) (basis a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 +
          (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (basis a.1) (hb a.1)
            (w a.1).2 (deck a.1) a.2 : ℝ)) / d : ℝ) : UnitAddCircle) := by
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    ((N / d) • normalizedCoveredChart (euclideanSubspace (U a.1)) (basis a.1) (hb a.1)
      (bW a.1) N (orthonormalMixedChart (o a.1) (w a.1), integerResidueMap (E a.1) N (deck a.1)))) a.2 = _
  rw [map_nsmul, map_nsmul, Pi.smul_apply,
    forecastNativeCoveredChart_ambient U basis o hb bW N w deck a]
  exact real_divisor_nsmul_circle N d (Nat.pos_of_ne_zero (NeZero.ne N)) hd hdiv _

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

theorem nativeSingleSiteCoverObservable_mixed_eq_forecastShortGridTest
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (Lsize : ℕ) (R : Fin m → ℝ) (hR : ∀ j, R j ≠ 0)
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (base u : X → ℤ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {τ : ℝ} (hτ : τ ≠ 0) (N : ℕ) [NeZero N] (hWN : W.cover ∣ N)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ) :
    nativeSingleSiteCoverObservable U W physicalN u N
      (fun j (_ : Unit) => normalizedCoveredChart (euclideanSubspace (U j))
        (basis j) (hb j) (bW j) N
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) N (deck j))) =
    W.forecastShortGridTest U basis Lsize hb o bW R q hm hperiod hcover
      (fun x => (base x : ℝ) / physicalN x) τ
      (fun a _ => (w a.val.1).2 a.val.2)
      (fun output => (forecastCongruenceOutput (R := ℤ)
        (allocatedShortAxis (I := I) U basis Lsize) u
          (fun j => Sum.elim (w j).2 (deck j)) output : ZMod q))
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        fun a => allocatedFullMixedSiteValue (R := R) U basis w a.1.val) := by
  unfold forecastShortGridTest forecastResidueTest
  rw [forecastShortGridSheet_of_mixed, forecastShortGridNormalized_of_mixed,
    forecastNativeSpatialResidue_reduction, forecastNativeAmbientDeckResidue_reduction,
    W.forecastPullback_mixed U basis o R _ hR base u physicalN hN hτ]
  simp only [nativeSingleSiteCoverObservable, frozenTorus]
  congr 2
  apply Prod.ext
  · rfl
  · funext a
    exact forecastNativeCoveredChart_commonCover_ambient U basis hb o bW N W.cover
      W.cover_pos hWN w deck a

theorem nativeSingleSiteCoverObservable_normalized_raw_point
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (Lsize : ℕ) (R : Fin m → ℝ) (hR : ∀ j, R j ≠ 0)
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (base u : X → ℤ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {τ : ℝ} (hτ : τ ≠ 0) (N : ℕ) [NeZero N] (hWN : W.cover ∣ N)
    (v : (Σ j, I j) → ℝ)
    (ks : AllocatedShortIntegerAxis U basis Lsize → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis Lsize → ℤ)
    (deck : ForecastSingleDeckResidues E N) :
    nativeSingleSiteCoverObservable U W physicalN u N
      (mixedCoveredJetChart U o basis hb bW N
        (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
          (forecastIntegerAxisMerge U basis Lsize ks ka) deck)) =
      W.forecastShortGridTest U basis Lsize hb o bW R q hm hperiod hcover
        (fun x => (base x : ℝ) / physicalN x) τ (fun a _ => ks a)
        (forecastJointNativeResidue (I := I) U basis Lsize
          (fun j e => (((deck j () e).val : ℤ) : ZMod q))
          (Sum.elim (fun x => (u x : ZMod q)) (fun a => (ka a : ZMod q))))
        ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
          forecastActiveCoordinateJoin U basis Lsize v
            (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R Lsize a)) := by
  let w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun j => (fun i => R j * v ⟨j, i⟩,
      fun i => forecastIntegerAxisMerge U basis Lsize ks ka ⟨j, i⟩)
  let deckInt : ∀ j, E j → ℤ := fun j e => ((deck j () e).val : ℤ)
  have hchart : mixedCoveredJetChart U o basis hb bW N
      (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis Lsize ks ka) deck) =
      fun j (_ : Unit) => normalizedCoveredChart (euclideanSubspace (U j))
        (basis j) (hb j) (bW j) N
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) N (deckInt j)) := by
    funext j t
    cases t
    change normalizedCoveredChart _ _ _ _ _ (_, deck j ()) = _
    congr 1
    apply Prod.ext
    · rfl
    · funext e
      change deck j () e = (((deck j () e).val : ℤ) : ZMod N)
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hgrid : (fun a : AllocatedShortIntegerAxis U basis Lsize =>
      fun _ : (Finset.univ : Finset (Finset Empty)) => (w a.val.1).2 a.val.2) =
      (fun a _ => ks a) := by
    funext a t
    exact forecastIntegerAxisMerge_short U basis Lsize ks ka a
  have hcoord : (fun a => allocatedFullMixedSiteValue (R := R) U basis w a.1.val) =
      forecastActiveCoordinateJoin U basis Lsize v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R Lsize a) := by
    change forecastNormalizedActiveCoordinates (allocatedShortAxis (I := I) U basis Lsize)
      (allocatedFullMixedSiteValue (R := R) U basis w) = _
    rw [forecastActiveCoordinateJoin_mixed]
    congr 1
    · funext a
      exact mul_div_cancel_left₀ (v a) (hR a.1)
    · funext a
      change ((forecastIntegerAxisMerge U basis Lsize ks ka a.val : ℤ) : ℝ) / _ = _
      rw [forecastIntegerAxisMerge_active]
  rw [hchart, W.nativeSingleSiteCoverObservable_mixed_eq_forecastShortGridTest
    U basis hb o bW Lsize R hR q hm hperiod hcover base u physicalN hN hτ N hWN w deckInt,
    hgrid, hcoord, forecastJointNativeResidue_integer]

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)

local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Cont" => (Σ j : Fin m, I j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U b Lsize

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

theorem forecastShortGridJointTest_bounds
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) (c : Cont → ℝ) :
    (∀ z, ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
      (forecastJointCoordinateJoin U b Lsize c z)‖ ≤ 1) ∧
    LipschitzWith (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
      (fun z => W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
        (forecastJointCoordinateJoin U b Lsize c z)) := by
  have h := W.forecastShortGridTest_bounds U b Lsize hb o bW R q hm hperiod hcover center τ grid out
  refine ⟨fun z => h.1 _, ?_⟩
  have hj : LipschitzWith 1 (forecastJointCoordinateJoin (X := X) U b Lsize c) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have he := (forecastJointCoordinateJoin_isometry (X := X) U b Lsize).dist_eq (c, z) (c, w)
    simpa only [NNReal.coe_one, one_mul, Prod.dist_eq, dist_self,
      max_eq_right (dist_nonneg)] using he.le
  simpa only [mul_one, Function.comp_def] using h.2.comp hj

theorem forecastShortGridJointTest_early_bounds
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) (c : Cont → ℝ)
    {p : ℝ} (hp : 0 ≤ p) (hmP : (m : ℝ) ≤ p) (hnP : ∀ j, (n j : ℝ) ≤ p)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ p)
    (hbP : ∀ j i, ‖b j i‖ ≤ Real.exp p) (hR : ∀ j, ‖R j‖ ≤ 1)
    (hLip : (Lip : ℝ) ≤ Real.exp p) (hτ : |τ| ≤ 8) :
    (∀ z, ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
      (forecastJointCoordinateJoin U b Lsize c z)‖ ≤ 1) ∧
    LipschitzWith (Real.toNNReal (Real.exp (5 * p + 4)))
      (fun z => W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
        (forecastJointCoordinateJoin U b Lsize c z)) := by
  have h := W.forecastShortGridJointTest_bounds U b Lsize hb o bW R q hm hperiod hcover center τ grid out c
  refine ⟨h.1, h.2.weaken ?_⟩
  have hamb := forecastNativeAmbientLip_le_exp U b o R hp hmP hnP hIP hbP hR
  have ht : ‖τ / 8‖ ≤ (1 : ℝ) := by
    rw [norm_div, Real.norm_eq_abs, show ‖(8 : ℝ)‖ = 8 by norm_num]
    exact (div_le_one (by norm_num)).mpr hτ
  have hmax : max ‖τ / 8‖ (forecastNativeAmbientLip U b o R : ℝ) ≤ Real.exp (4 * (p + 1)) := by
    apply max_le
    · exact ht.trans (Real.one_le_exp_iff.mpr (by positivity))
    · exact hamb
  apply (NNReal.coe_le_coe).mp
  rw [NNReal.coe_mul, NNReal.coe_max, coe_nnnorm,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  calc
    (Lip : ℝ) * max ‖τ / 8‖ (forecastNativeAmbientLip U b o R : ℝ)
        ≤ Real.exp p * Real.exp (4 * (p + 1)) :=
      mul_le_mul hLip hmax (le_trans (norm_nonneg _) (le_max_left _ _)) (Real.exp_pos _).le
    _ = Real.exp (5 * p + 4) := by rw [← Real.exp_add]; congr 1; ring

theorem forecastShortGridFullJointTest_bounds
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) :
    (∀ z : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
      ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
        (forecastJointCoordinateJoin U b Lsize z.1 z.2)‖ ≤ 1) ∧
    LipschitzWith (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
      (fun z : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
        W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
          (forecastJointCoordinateJoin U b Lsize z.1 z.2)) := by
  have h := W.forecastShortGridTest_bounds U b Lsize hb o bW R q hm hperiod hcover center τ grid out
  refine ⟨fun z => h.1 _, ?_⟩
  simpa only [mul_one, Function.comp_def] using
    h.2.comp (forecastJointCoordinateJoin_lipschitz (X := X) U b Lsize)

theorem forecastShortGridFullJointTest_early_bounds
    (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q)
    {p : ℝ} (hp : 0 ≤ p) (hmP : (m : ℝ) ≤ p) (hnP : ∀ j, (n j : ℝ) ≤ p)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ p)
    (hbP : ∀ j i, ‖b j i‖ ≤ Real.exp p) (hR : ∀ j, ‖R j‖ ≤ 1)
    (hLip : (Lip : ℝ) ≤ Real.exp p) (hτ : |τ| ≤ 8) :
    (∀ z : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ), ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
      (forecastJointCoordinateJoin U b Lsize z.1 z.2)‖ ≤ 1) ∧
    LipschitzWith (Real.toNNReal (Real.exp (5 * p + 4)))
      (fun z : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) => W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out
        (forecastJointCoordinateJoin U b Lsize z.1 z.2)) := by
  have h := W.forecastShortGridFullJointTest_bounds U b Lsize hb o bW R q hm hperiod hcover center τ grid out
  refine ⟨h.1, h.2.weaken ?_⟩
  have hamb := forecastNativeAmbientLip_le_exp U b o R hp hmP hnP hIP hbP hR
  have ht : ‖τ / 8‖ ≤ (1 : ℝ) := by
    rw [norm_div, Real.norm_eq_abs, show ‖(8 : ℝ)‖ = 8 by norm_num]
    exact (div_le_one (by norm_num)).mpr hτ
  have hmax : max ‖τ / 8‖ (forecastNativeAmbientLip U b o R : ℝ) ≤ Real.exp (4 * (p + 1)) := by
    apply max_le
    · exact ht.trans (Real.one_le_exp_iff.mpr (by positivity))
    · exact hamb
  apply (NNReal.coe_le_coe).mp
  rw [NNReal.coe_mul, NNReal.coe_max, coe_nnnorm,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  calc
    (Lip : ℝ) * max ‖τ / 8‖ (forecastNativeAmbientLip U b o R : ℝ)
        ≤ Real.exp p * Real.exp (4 * (p + 1)) :=
      mul_le_mul hLip hmax (le_trans (norm_nonneg _) (le_max_left _ _)) (Real.exp_pos _).le
    _ = Real.exp (5 * p + 4) := by rw [← Real.exp_add]; congr 1; ring

theorem native_joint_modulus {N : ℕ} (hm : W.modulus ∣ N) (hc : W.cover ∣ N)
    {p : ℝ} (hmodulus : (W.modulus : ℝ) ≤ Real.exp p)
    (hcover : (W.cover : ℝ) ≤ Real.exp p) :
    0 < Nat.lcm W.modulus W.cover ∧
      W.modulus ∣ Nat.lcm W.modulus W.cover ∧
      W.cover ∣ Nat.lcm W.modulus W.cover ∧
      Nat.lcm W.modulus W.cover ∣ N ∧
      (Nat.lcm W.modulus W.cover : ℝ) ≤ Real.exp (2 * p) := by
  refine ⟨Nat.lcm_pos W.modulus_pos W.cover_pos, Nat.dvd_lcm_left _ _, Nat.dvd_lcm_right _ _,
    Nat.lcm_dvd hm hc, ?_⟩
  calc
    (Nat.lcm W.modulus W.cover : ℝ) ≤ (W.modulus * W.cover : ℕ) := by
      exact_mod_cast Nat.lcm_le_mul W.modulus_pos W.cover_pos
    _ = (W.modulus : ℝ) * W.cover := Nat.cast_mul _ _
    _ ≤ Real.exp p * Real.exp p := mul_le_mul hmodulus hcover (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
