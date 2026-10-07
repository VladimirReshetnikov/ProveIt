/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
import OAI.Combinatorics.Progressions.Lattices.ForecastBufferedIntegerDeckFactor
import OAI.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
import OAI.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

theorem allocatedShortIntegerSelection_exhaustive (a : LayerSamplerAxis I n)
    (ha : allocatedShortAxis U b L a) :
    ∃ i : AllocatedShortIntegerAxis U b L,
      (⟨(allocatedShortIntegerSelection U b L i).1,
        Sum.inr (allocatedShortIntegerSelection U b L i).2⟩ : LayerSamplerAxis I n) = a := by
  obtain ⟨i, hi⟩ := (allocatedShortIntegerAxisEquiv (I := I) U b L).surjective ⟨a, ha⟩
  exact ⟨i, congrArg Subtype.val hi⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v,
  ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j,
  C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

include hR hC hchart hbudget in
theorem forecastBufferedPhysicalChartCutoff_eq
    (z : MixedCoveredJetSource I single E n d) (hz : z ∈ region) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr
        (coveredJetAmbientTorus U d (chart z)) =
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
        (allocatedFullMixedSiteValue (R := R) U b
          (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ i, |mixedJetAmbientPoint U b o z.1 i| < 1 / 2 := by
    rintro ⟨j, t, i⟩
    exact ((hz j (mem_univ j) t (mem_univ t)).1 i).trans_lt (by norm_num)
  rw [allocatedBufferedTorusCutoff_local U b o r hr hR C hC hchart hbudget _ hsmall]
  unfold allocatedBufferedAmbientCutoff
  rw [allocatedFullAmbientSiteCoordinates_point]

include hR hC hchart hbudget in
theorem forecastBufferedPhysicalChartCutoff_eq_one
    (z : MixedCoveredJetSource I single E n d) (hz : z ∈ region)
    (hcut : normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
      (allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) = 1) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr
      (coveredJetAmbientTorus U d (chart z)) = 1 :=
  (forecastBufferedPhysicalChartCutoff_eq U b o r hr hR C hC hchart hbudget hb bW d z hz).trans hcut

include hR hC hchart hbudget in
theorem forecastBufferedPhysicalChartCutoff_eq_one_of_box
    (z : MixedCoveredJetSource I single E n d) (hz : z ∈ region)
    (hbox : ∀ a, |allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()) a| ≤ (r : ℝ)) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr
      (coveredJetAmbientTorus U d (chart z)) = 1 :=
  forecastBufferedPhysicalChartCutoff_eq_one U b o r hr hR C hC hchart hbudget hb bW d z hz
    ((normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.1 _ hbox)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem integerMatrix_mulVec_scaled_bound {O K : Type*} [Fintype K]
    (A : Matrix O K ℤ) (z : K → ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    {H M R : ℝ} (hM : 0 ≤ M)
    (hA : ∀ o k, |(A o k : ℝ)| / T k ≤ M)
    (hz : ∀ k, |(z k : ℝ) / H| * T k ≤ R) (o : O) :
    |((A *ᵥ z) o : ℝ) / H| ≤ (Fintype.card K : ℝ) * M * R := by
  calc
    _ = |∑ k, (A o k : ℝ) * ((z k : ℝ) / H)| := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
        Finset.sum_div, mul_div_assoc]
    _ ≤ ∑ k, |(A o k : ℝ) * ((z k : ℝ) / H)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : K, M * R := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      calc
        _ ≤ (M * T k) * |(z k : ℝ) / H| :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ (hT k)).mp (hA o k)) (abs_nonneg _)
        _ = M * (|(z k : ℝ) / H| * T k) := by ring
        _ ≤ M * R := mul_le_mul_of_nonneg_left (hz k) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem rationalInactiveForecast_eq_zero_of_not_mem_range
    {I Ω Z J : Type*} [Fintype I] [Fintype Ω] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights Ω)
    (gridPoint : I → Z) (Y : I → Ω → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (b : J → ZMod N)
    (hz : ∀ i, gridPoint i ≠ z) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  simp [rationalInactiveForecast, FiniteProbabilityWeights.fiberMean, hz,
    FiniteProbabilityWeights.mean]

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*}

theorem forecastInactiveFixedOutput_scaled_bound
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (a : A) (row : (Finset.univ : Finset (Finset Empty))) :
    |(forecastInactiveFixedOutput B U b S selected c x y a row : ℝ) /
      basisAxisScale (b (selected a).1) (selected a).2| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
        ((selected a).1.val + 1)) : ℝ) * R (selected a).1 := by
  let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y
  let dirs := allocatedPhysicalCubeDirections B U b S x y
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  have hroot (k) : |(root k : ℝ) / layerSamplerBox B U b S k| ≤ 1 := by
    simpa only [allocatedPhysicalRootAllowance_zero] using
      allocatedPhysicalCube_root_normalized B U b S x y (fun _ => 0) k
  have hmat : ∀ o e,
      |(boundedCoefficientJetMatrix root dirs ((selected a).1.val + 1)
        (fun t : (Finset.univ : Finset (Finset Empty)) => (t : Finset Empty)) o e : ℝ)| /
        monomialScale (layerSamplerBox B U b S) e.val ≤ 1 := by
    intro o e
    simpa using boundedCoefficientJetMatrix_scaled_entry_bound root dirs
      (layerSamplerBox B U b S) hT hroot
      (allocatedPhysicalCube_directions_normalized B U b S x y) _ _ o e
  have hbound := integerMatrix_mulVec_scaled_bound _ (c a)
    (fun e : BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) => monomialScale (layerSamplerBox B U b S) e.val)
    (fun e => monomialScale_pos _ hT e.val) zero_le_one hmat
    (fun e => allocatedLayerIntegerCoefficient_scaled_bound B U b hR hσ S
      (selected a).1 (hσ1 a) (selected a).2 e (c a e) (hc a e)) row
  simpa only [forecastInactiveFixedOutput, root, dirs, mul_one] using hbound

theorem forecastInactiveFixedOutput_normalized_bound
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (a : A) (row : (Finset.univ : Finset (Finset Empty))) :
    |(forecastInactiveFixedOutput B U b S selected c x y a row : ℝ) /
      basisAxisScale (b (selected a).1) (selected a).2 / R (selected a).1| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
        ((selected a).1.val + 1)) : ℝ) := by
  rw [abs_div, abs_of_pos (hR _), div_le_iff₀ (hR _)]
  exact forecastInactiveFixedOutput_scaled_bound B U b S hR hσ selected c hc hσ1 x y a row

theorem forecastInactiveFixed_rational_eq_zero_of_outside
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (x : G → IntegerScalarCubeBox Empty S.value)
    {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
    (law : FiniteProbabilityWeights
      (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)))
    (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S) → FiniteProbabilityWeights Ω)
    (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S) → Ω → Out → ℤ)
    (N : ℕ) [NeZero N] (volume : ℝ) (z : A → ℤ) (out : Out → ZMod N)
    (a : A)
    (hz : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
        ((selected a).1.val + 1)) : ℝ) <
      |(z a : ℝ) / basisAxisScale (b (selected a).1) (selected a).2 / R (selected a).1|) :
    rationalInactiveForecast law active (forecastInactiveFixedOutput B U b S selected c x)
      Y N volume (fun a _ => z a) out = 0 := by
  apply rationalInactiveForecast_eq_zero_of_not_mem_range
  intro y heq
  let row : (Finset.univ : Finset (Finset Empty)) := ⟨∅, Finset.mem_univ _⟩
  have hb := forecastInactiveFixedOutput_normalized_bound B U b S hR hσ
    selected c hc hσ1 x y a row
  rw [heq] at hb
  exact (not_lt_of_ge hb) hz

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

variable {A : Type*}
variable (selected : A → Σ j : Fin m, Fin (n j))

variable (c : ∀ a : A, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
  ((selected a).1.val + 1) → ℤ)
variable (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
  (selected a).1 (selected a).2 d).support)
variable (hσ1 : ∀ a : A, σ (selected a).1 ≤ 1)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S))) (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S)) → FiniteProbabilityWeights Ω)
variable (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S)) → Ω → Out → ℤ) (N : ℕ) [NeZero N]
variable (volume : ℝ) (out : Out → ZMod N)
variable (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))

include hR hσ hc hσ1

theorem forecastOriginalSource_coordinates_bound
    (hexhaustive : ∀ a, (allocatedShortAxis (I := I) U b S.value) a → ∃ i, (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    {r : ℝ}
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (hactive : ∀ a, ¬(allocatedShortAxis (I := I) U b S.value) a → |(allocatedFullMixedSiteValue (R := R) U b w) a| ≤ r)
    (hf : (rationalInactiveForecast law active
  (forecastInactiveFixedOutput B U b S selected c x) Y N volume
  (fun a _ => Prod.snd (w (Sigma.fst (selected a))) (Sigma.snd (selected a))) out) ≠ 0) : ∀ a, |(allocatedFullMixedSiteValue (R := R) U b w) a| ≤ r := by
  intro a
  by_cases ha : (allocatedShortAxis (I := I) U b S.value) a
  · obtain ⟨i, haxis⟩ := hexhaustive a ha
    rw [← haxis]
    change |((w (selected i).1).2 (selected i).2 : ℝ) /
      basisAxisScale (b (selected i).1) (selected i).2 / R (selected i).1| ≤ r
    by_contra hn
    have hlarge := lt_of_le_of_lt (hradius (selected i).1) (lt_of_not_ge hn)
    exact hf (forecastInactiveFixed_rational_eq_zero_of_outside B U b S hR hσ selected c hc
      hσ1 x law active Y N volume (fun a => (w (selected a).1).2 (selected a).2) out i hlarge)
  · exact hactive a ha

include hR hσ hc hσ1

theorem forecastOriginalSource_cutoff_eq_one
    (hexhaustive : ∀ a, (allocatedShortAxis (I := I) U b S.value) a → ∃ i, (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (r : ℝ≥0) (hr : 0 < r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (hactive : ∀ a, ¬(allocatedShortAxis (I := I) U b S.value) a → |(allocatedFullMixedSiteValue (R := R) U b w) a| ≤ r)
    (hf : (rationalInactiveForecast law active
  (forecastInactiveFixedOutput B U b S selected c x) Y N volume
  (fun a _ => Prod.snd (w (Sigma.fst (selected a))) (Sigma.snd (selected a))) out) ≠ 0) : normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr (allocatedFullMixedSiteValue (R := R) U b w) = 1 :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.1 (allocatedFullMixedSiteValue (R := R) U b w)
    (forecastOriginalSource_coordinates_bound B U b S hR hσ selected c hc hσ1 x law active Y N volume
      out w hexhaustive hradius hactive hf)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

variable {A : Type*}
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
variable (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
variable (hσ1 : ∀ a : A, σ (selected a).1 ≤ 1)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)) → FiniteProbabilityWeights Ω)
variable (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)) → Ω → Out → ℤ) (N : ℕ) [NeZero N]
variable (volume : ℝ) (out : Out → ZMod N)
variable (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
variable (y : (Σ _ : X, Unit ⊕ Empty) → ℝ)
include hR hσ hδ hw hl hs hroot hwidth hσ1 in

theorem allocatedOriginalSampleSource_cutoff
    (hexhaustive : ∀ a, allocatedShortAxis (I := I) U basis S.value a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r) :
    let coords := allocatedFullMixedSiteValue (R := R) U basis w
    let density := allocatedOriginalSampleForecastDensity (X := X)
      B U basis S s root D hp hW hL hB lower width
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    let forecast := rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x) Y N volume
      (fun a _ => (w (selected a).1).2 (selected a).2) out
    let source := density sample
      (y, forecastNormalizedActiveCoordinates (allocatedShortAxis (I := I) U basis S.value) coords) * forecast
    (source ≠ 0 → normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr coords = 1) ∧
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr coords * source = source ∧
      (normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr coords : ℂ) *
        (source : ℂ) = (source : ℂ) := by
  intro coords density law forecast source
  have hone : source ≠ 0 →
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr coords = 1 := by
    intro hsource
    have hparts := mul_ne_zero_iff.mp hsource
    have hactive := allocatedOriginalSampleForecastDensity_nonzero_active_bounds (X := X)
      B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl
      sample hs hroot hwidth y coords hparts.1
    exact forecastOriginalSource_cutoff_eq_one B U basis S hR hσ selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample)
      (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
      hσ1 x law active Y N volume out w hexhaustive r hr hradius
      (fun a ha => (hactive ⟨a, ha⟩).trans hr3) hparts.2
  have hmul : normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr coords * source = source := by
    by_cases hsource : source = 0
    · rw [hsource, mul_zero]
    · rw [hone hsource, one_mul]
  exact ⟨hone, hmul, by
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hmul⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

noncomputable def forecastDensityPhysicalDeckSource (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ) : ℂ := by
  exact (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
    forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
  (rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume (fun a _ => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) : ℂ)

local notation "deckSource" => forecastDensityPhysicalDeckSource B U basis S density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastDensityPhysicalChartSource (u : X → ℤ)
    (z : MixedCoveredJetSource I single Eout n N) : ℂ :=
  deckSource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastDensityPhysicalTarget
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) : ℂ :=
  restrictedComplexChartDensity chart region 1 (chartSource u)
    (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)))

local notation "target" => forecastDensityPhysicalTarget B U basis S density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastDensityPhysicalTarget_integer_deck
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    target poly hpoly u = deckSource u w deck := by
  let z : MixedCoveredJetSource I single Eout n N :=
    (fun j => (fun i _ => (w j).1 i, fun i _ => (w j).2 i),
      fun j _ => integerResidueMap (Eout j) N (deck j))
  have hz : z ∈ region := by
    intro j _ t _
    exact ⟨hquarter j, Set.mem_univ _⟩
  have hchart : chart z = physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)) := by
    funext j t
    cases t
    rw [physicalSingleSiteValue_eq_mk]
    exact (normalizedCoveredChart_of_integer_deck (euclideanSubspace (U j))
      (bW j) (basis j) (hb j) N _ (orthonormalMixedChart (o j) (w j))
      (deck j) (hdeck j)).symm
  unfold forecastDensityPhysicalTarget
  rw [← hchart, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o basis hb bW N _
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
    Complex.ofReal_one, one_mul]
  have houtput : (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (fun i => (((deck j i : ZMod N).val : ℕ) : ℤ)))
        output : ZMod N)) =
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) := by
    funext output
    rcases output with ⟨j, a | a | a⟩
    · rfl
    · simpa only [forecastCongruenceOutput, Sum.elim_inr, Int.cast_natCast]
        using ZMod.natCast_zmod_val (deck j a : ZMod N)
    · rfl
  change deckSource u w (fun j i => ((deck j i : ZMod N).val : ℤ)) = _
  unfold forecastDensityPhysicalDeckSource
  rw [houtput]

theorem forecastDensityPhysicalDeckSource_cutoff
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hnonzero : deckSource u w deck ≠ 0) :
    normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
      (allocatedFullMixedSiteValue (R := R) U basis w) = 1 := by
  unfold forecastDensityPhysicalDeckSource at hnonzero
  have hparts := mul_ne_zero_iff.mp hnonzero
  have hd : density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) ≠ 0 := by
    exact_mod_cast hparts.1
  apply forecastOriginalSource_cutoff_eq_one B U basis S hR hσ selected
    (allocatedOriginalSampleInactiveCoefficients B selected sample)
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
    hσ1 x law active Y N volume _ w hexhaustive r hr hradius
  · intro a ha
    exact ((hactive _ hd) ⟨⟨a, ha⟩, ()⟩).trans hr3
  · exact_mod_cast hparts.2

theorem forecastDensityPhysicalTarget_cutoff
    (hR : ∀ j, 0 < R j) (r : ℝ≥0) (hr : 0 < r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hsource : ∀ u w deck, deckSource u w deck ≠ 0 →
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
        (allocatedFullMixedSiteValue (R := R) U basis w) = 1)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  have hinj := mixedCoveredJetChart_injOn U o basis hb bW N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hmem : physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)) ∈ chart '' region := by
    by_contra hn
    exact hnonzero (restrictedComplexChartDensity_zero chart region 1 (chartSource u) hn)
  obtain ⟨z, hz, hvalue⟩ := hmem
  have hznonzero : chartSource u z ≠ 0 := by
    intro hzero
    apply hnonzero
    unfold forecastDensityPhysicalTarget
    rw [← hvalue, restrictedComplexChartDensity_apply chart region 1 (chartSource u) hinj hz,
      hzero, mul_zero]
  have hc := hsource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ)) hznonzero
  have hcut := forecastBufferedPhysicalChartCutoff_eq_one U basis o r hr
    hR C hC hchart hbudget hb bW N z hz hc
  rw [hvalue, physicalSingleSiteValue_ambient] at hcut
  exact hcut

theorem forecastDensityPhysicalTarget_cutoff_of_active_support
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  apply forecastDensityPhysicalTarget_cutoff B U basis S density selected sample x
    active Y N volume base physicalN τ o hb bW hR r hr C hC hchart hbudget
    (fun u w deck => forecastDensityPhysicalDeckSource_cutoff B U basis S density selected sample x
      active Y N volume base physicalN τ hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius u w deck)
    poly hpoly u hnonzero

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastDensityPhysicalChartSource_normalized_raw_point
    (hR : ∀ j, 0 < R j)
    (hselected : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (u : X → ℤ) (v : (Σ j, I j) → ℝ)
    (ks : AllocatedShortIntegerAxis U basis S.value → ℤ)
    (ka : AllocatedActiveIntegerAxis U basis S.value → ℤ)
    (deck : ForecastSingleDeckResidues Eout N) :
    forecastDensityPhysicalChartSource B U basis S density selected sample x
      active Y N volume base physicalN τ u
      (forecastSingleMixedRawPoint I Eout n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis S.value ks ka) deck) =
    (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastActiveCoordinateJoin U basis S.value v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a)) : ℂ) *
    (rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => ks ⟨selected a, hselected a⟩)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
          (fun i => ((deck j () i).val : ℤ))) output : ZMod N)) : ℂ) := by
  let w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun j => (fun i => R j * v ⟨j, i⟩,
      fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
  have hactive : forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis w) =
      forecastActiveCoordinateJoin U basis S.value v
        (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a) := by
    rw [forecastActiveCoordinateJoin_mixed]
    congr 1
    · funext a
      change R a.1 * v a / R a.1 = v a
      exact mul_div_cancel_left₀ (v a) (hR a.1).ne'
    · funext a
      change ((forecastIntegerAxisMerge U basis S.value ks ka a.val : ℤ) : ℝ) / _ = _
      rw [forecastIntegerAxisMerge_active]
  have hgrid : (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
      forecastIntegerAxisMerge U basis S.value ks ka (selected a)) =
      (fun a (_ : (Finset.univ : Finset (Finset Empty))) => ks ⟨selected a, hselected a⟩) := by
    funext a t
    exact forecastIntegerAxisMerge_short U basis S.value ks ka ⟨selected a, hselected a⟩
  change (density (_, forecastNormalizedActiveCoordinates short
    (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) * _ = _
  rw [hactive]
  congr 2
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastDensityPhysicalChartSource_measurable
    (hdensity : Measurable density) (u : X → ℤ) :
    Measurable (forecastDensityPhysicalChartSource B U basis S density selected sample x
      active Y N volume base physicalN τ u) := by
  let source := MixedCoveredJetSource I single Eout n N
  let w : source → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun z j => mixedArrayRegroup _ _ _ (z.1 j) ()
  have hw : Measurable w := by
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply ()).comp
      ((mixedArrayRegroup _ _ _).measurable.comp
        ((measurable_pi_apply j).comp measurable_fst))
  have hcoord : Measurable (fun z : source =>
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis (w z))) :=
    (forecastNormalizedActiveCoordinates_lipschitz short).continuous.measurable.comp
      ((allocatedFullMixedSiteValue_continuous (I := I) (R := R) U basis).measurable.comp hw)
  have hreal : Measurable (fun z : source => density
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastNormalizedActiveCoordinates short
          (allocatedFullMixedSiteValue (R := R) U basis (w z)))) :=
    hdensity.comp (measurable_const.prodMk hcoord)
  let integerData : source → (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) :=
    fun z => (fun j i => (z.1 j).2 i (), fun j i => ((z.2 j () i).val : ℤ))
  have hdata : Measurable integerData := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro j
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply ()).comp ((measurable_pi_apply i).comp
        (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst)))
    · exact (measurable_of_finite
        (fun v : ∀ j, Unit → Eout j → ZMod N => fun j i => ((v j () i).val : ℤ))).comp
        measurable_snd
  let rational : (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) → ℝ :=
    fun v => rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => v.1 (selected a).1 (selected a).2)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (v.1 j) (v.2 j)) output : ZMod N))
  have hrational : Measurable rational := measurable_of_countable rational
  exact hreal.complex_ofReal.mul ((hrational.comp hdata).complex_ofReal)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N

theorem forecastDensityPhysicalChartSource_weighted_haar_integral
    (hdensity : Measurable density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test) :
    (∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y * test y ∂haar) =
      (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z in region, chartSource u z * test (chart z) ∂raw := by
  exact mixedCoveredJet_weighted_complex_integral U o basis hb bW N ν _
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (chartSource u)
    (forecastDensityPhysicalChartSource_measurable B U basis S density selected sample x
      active Y N volume base physicalN τ hdensity u) test htest

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

local notation "deckSource" => forecastDensityPhysicalDeckSource B U basis S density selected sample x
  active Y N volume base physicalN τ

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

local notation "target" => forecastDensityPhysicalTarget B U basis S density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastDensityPhysicalTarget_norm_le
    {M : ℝ} (hM : 0 ≤ M)
    (hsource : ∀ (z : A → ℤ) (outPoint : Out → ZMod N)
        (y : (Spatial → ℝ) × (Active → ℝ)),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        Y N volume (fun a _ => z a) outPoint : ℂ)‖ ≤ M)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
    ‖target poly hpoly u‖ ≤ M := by
  have hinj := mixedCoveredJetChart_injOn U o basis hb bW N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hbound (z : MixedCoveredJetSource I single Eout n N) :
      ‖chartSource u z‖ ≤ M := by
    exact hsource _ _ _
  have h := restrictedComplexChartDensity_norm_le chart region hinj (chartSource u)
    hM hbound (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)))
  simpa only [forecastDensityPhysicalTarget] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastDensityPhysicalChartSource_continuous
    (hdensity : Continuous density) (u : X → ℤ) :
    Continuous (forecastDensityPhysicalChartSource B U basis S density selected sample x
      active Y N volume base physicalN τ u) := by
  let source := MixedCoveredJetSource I single Eout n N
  let w : source → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun z j => mixedArrayRegroup _ _ _ (z.1 j) ()
  have hw : Continuous w := by
    change Continuous (fun z : source => fun j =>
      ((fun i => (z.1 j).1 i ()), (fun i => (z.1 j).2 i ())))
    dsimp only [source]
    fun_prop
  have hcoord : Continuous (fun z : source =>
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis (w z))) :=
    (forecastNormalizedActiveCoordinates_lipschitz short).continuous.comp
      ((allocatedFullMixedSiteValue_continuous (I := I) (R := R) U basis).comp hw)
  have hreal : Continuous (fun z : source => density
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastNormalizedActiveCoordinates short
          (allocatedFullMixedSiteValue (R := R) U basis (w z)))) :=
    hdensity.comp (continuous_const.prodMk hcoord)
  let integerData : source → (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) :=
    fun z => (fun j i => (z.1 j).2 i (), fun j i => ((z.2 j () i).val : ℤ))
  have hdata : Continuous integerData := by
    apply Continuous.prodMk
    · change Continuous (fun z : source => fun j i => (z.1 j).2 i ())
      dsimp only [source]
      fun_prop
    · exact (continuous_of_discreteTopology
        (f := fun v : ∀ j, Unit → Eout j → ZMod N => fun j i => ((v j () i).val : ℤ))).comp
        continuous_snd
  let rational : (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) → ℝ :=
    fun v => rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => v.1 (selected a).1 (selected a).2)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (v.1 j) (v.2 j)) output : ZMod N))
  have hrational : Continuous rational := continuous_of_discreteTopology
  exact (Complex.continuous_ofReal.comp hreal).mul
    (Complex.continuous_ofReal.comp (hrational.comp hdata))

end Erdos3.VectorPolynomial

end

end OAI
