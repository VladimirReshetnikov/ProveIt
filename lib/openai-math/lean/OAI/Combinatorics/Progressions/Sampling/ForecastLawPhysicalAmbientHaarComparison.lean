import OAI.Combinatorics.Progressions.Dynamics.NormalizedTwistUniformAmbientBudget
import OAI.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem nativeFiniteExpansion_mean_comparison {Ω T : Type*} [Fintype T]
    (s : Finset Ω) (hs : s.Nonempty) (w H : Ω → ℂ) (f : T → Ω → ℂ)
    (c ref : T → ℂ) {δ ε M : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ x ∈ s, ‖w x‖ ≤ 1)
    (happ : ∀ x ∈ s, ‖H x - ∑ i, c i * f i x‖ ≤ δ)
    (hcomp : ∀ i, ‖(𝔼 x ∈ s, w x * f i x) - ref i‖ ≤ ε)
    (hmass : ∑ i, ‖c i‖ ≤ M) :
    ‖(𝔼 x ∈ s, w x * H x) - ∑ i, c i * ref i‖ ≤ δ + M * ε := by
  have hexpand (x : Ω) : w x * (∑ i, c i * f i x) =
      ∑ i, c i * (w x * f i x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have happmean : ‖(𝔼 x ∈ s, w x * H x) -
      (𝔼 x ∈ s, ∑ i, c i * (w x * f i x))‖ ≤ δ := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le hs
    intro x hx
    rw [← hexpand, ← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hw x hx) (norm_nonneg _)).trans
      (by simpa only [one_mul] using happ x hx)
  have hsum : ‖(∑ i, c i * (𝔼 x ∈ s, w x * f i x)) -
      ∑ i, c i * ref i‖ ≤ M * ε := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖c i * (𝔼 x ∈ s, w x * f i x) - c i * ref i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hcomp i) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hε
  have hlinear : (𝔼 x ∈ s, ∑ i, c i * (w x * f i x)) =
      ∑ i, c i * (𝔼 x ∈ s, w x * f i x) := by
    rw [Finset.expect_sum_comm]
    simp only [Finset.mul_expect]
  rw [hlinear] at happmean
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add happmean hsum)

 theorem exists_nativeForecast_ambient_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
      {T : Type} [Fintype T]
      (V : T → NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
      (c : T → ℂ) (H : (X → ℤ) → ℂ)
      {P E Rrank δ M : ℝ}, 0 ≤ P → 0 ≤ E →
      (Fintype.card X : ℝ) ≤ P → (Fintype.card (Σ j, J j) : ℝ) ≤ P →
      ((Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P →
      (∀ i, ((W.cover * (V i).cover : ℕ) : ℝ) ≤ Real.exp P) →
      (∀ i, ((W.modulus * (V i).modulus : ℕ) : ℝ) ≤ Real.exp P) →
      (∑ i, ‖c i‖) ≤ M → ∀ (N : X → ℕ),
      (∀ i, Real.exp ((max P E + A) ^ A) ≤ (N i : ℝ)) →
      Real.exp ((max P E + A) ^ A) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ x ∈ integerBox N, ‖H x - ∑ i, c i * (V i).eval N poly x‖ ≤ δ) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x * H x) -
        ∑ i, c i * (𝔼 x ∈ integerBox N,
          (W.productUniform (V i)).frozenSingleSiteHaarReference U ν
            (fun a => (x a : ZMod (W.productUniform (V i)).modulus))
            (fun a => (x a : ℝ) / N a))‖ ≤ δ + M * Real.exp (-E) := by
  obtain ⟨A, hA, hcomp⟩ := exists_normalizedTwist_uniform_ambient_haar_budget m
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm pw cw pv cv Lw Lv W T _ V c H
    P E Rrank δ M hP hE hX hdim hLip hcover hmod hmass N hlarge hRrank hrank happ
  have hN (x : X) : 0 < N x := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge x)
  let : ∀ x, NeZero (N x) := fun x => ⟨(hN x).ne'⟩
  let F := fun i => W.productUniform (V i)
  let ref := fun i => 𝔼 x ∈ integerBox N, (F i).frozenSingleSiteHaarReference U ν
    (fun a => (x a : ZMod (F i).modulus)) (fun a => (x a : ℝ) / N a)
  have hone (i : T) : ‖(𝔼 x ∈ integerBox N, (F i).eval N poly x) - ref i‖ ≤ Real.exp (-E) := by
    exact hcomp U ν poly hp hm (F i) hP hE hX hdim hLip (hcover i) (hmod i)
      N hlarge hRrank hrank
  apply nativeFiniteExpansion_mean_comparison (integerBox N) (integerBox_nonempty N)
    (fun x => W.eval N poly x) H (fun i x => (V i).eval N poly x) c ref
    (Real.exp_pos _).le (fun x _ => W.norm_eval_le N poly x) happ _ hmass
  intro i
  simpa only [F, NormalizedPolynomialTwist.productUniform_eval] using hone i

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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
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

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

theorem forecastDensityPhysicalTarget_nativeHaarExpansion
    (hdensity : Measurable density)
    {T : Type*} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastDensityPhysicalTarget B U basis S density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (u : X → ℤ) :
    ‖(∫ y, κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) -
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j)‖ ≤ δ := by
  let : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit)) := hcompact
  apply nativePhysicalHaarExpansion (X := X) (m := m) (J := J) U ν W F c κ δ physicalN u N
    (Nat.pos_of_ne_zero (NeZero.ne N)) hWN
  · apply mixedCoveredJet_restrictedComplexDensity_measurable U o basis hb bW N
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
      (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    exact forecastDensityPhysicalChartSource_measurable B U basis S density selected sample x
      active Y N volume base physicalN τ hdensity u
  · intro poly hm
    exact happrox poly hm u

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
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

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

noncomputable def nativeForecastAmbientExponent (m : ℕ) : ℕ :=
  Classical.choose (exists_nativeForecast_ambient_comparison m)

theorem nativeForecastAmbientExponent_ge_two (m : ℕ) :
    2 ≤ nativeForecastAmbientExponent m :=
  (Classical.choose_spec (exists_nativeForecast_ambient_comparison m)).1

include hcompact in

theorem forecastDensityPhysicalTarget_ambientHaarComparison
    (hdensity : Measurable density)
    {T : Type} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastDensityPhysicalTarget B U basis S density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcover : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmod : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j)) :
    ‖(𝔼 u ∈ integerBox physicalN, W.eval physicalN poly u *
        (κ * forecastDensityPhysicalTarget B U basis S density selected sample x
          active Y N volume base physicalN τ o hb bW poly hm u)) -
      (𝔼 u ∈ integerBox physicalN, ∫ y,
        κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar)‖ ≤
        2 * δ + M * Real.exp (-E) := by
  have hN (i : X) : 0 < physicalN i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  let : ∀ i, NeZero (physicalN i) := fun i => ⟨(hN i).ne'⟩
  let ref (u : X → ℤ) := ∑ i, c i *
    (W.productUniform (F i)).frozenSingleSiteHaarReference U ν
      (fun j => (u j : ZMod (W.productUniform (F i)).modulus))
      (fun j => (u j : ℝ) / physicalN j)
  have hfirst := (Classical.choose_spec (exists_nativeForecast_ambient_comparison m)).2
    U ν poly hp hm W F c
      (fun u => κ * forecastDensityPhysicalTarget B U basis S density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u)
      hP hE hX hdim hLip hcover hmod hmass physicalN hlarge hRrank hrank
      (fun u _ => happrox poly hm u)
  have hpoint (u : X → ℤ) :
      ‖(∫ y, κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) - ref u‖ ≤ δ := by
    exact forecastDensityPhysicalTarget_nativeHaarExpansion B U basis S density selected sample x
      active Y N volume base physicalN τ o hb bW ν hdensity W F c κ δ hWN happrox u
  have hlast : ‖(𝔼 u ∈ integerBox physicalN, ref u) -
      (𝔼 u ∈ integerBox physicalN, ∫ y,
        κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar)‖ ≤ δ := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (integerBox_nonempty physicalN)
    intro u _
    rw [norm_sub_rev]
    exact hpoint u
  have hlinear : (𝔼 u ∈ integerBox physicalN, ref u) =
      ∑ i, c i * (𝔼 u ∈ integerBox physicalN,
        (W.productUniform (F i)).frozenSingleSiteHaarReference U ν
          (fun j => (u j : ZMod (W.productUniform (F i)).modulus))
          (fun j => (u j : ℝ) / physicalN j)) := by
    unfold ref
    rw [Finset.expect_sum_comm]
    simp only [Finset.mul_expect]
  rw [← hlinear] at hfirst
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hfirst hlast).trans_eq (by ring))

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
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

theorem forecastLawDensityPhysicalTarget_nativeHaarExpansion
    (hdensity : Measurable density)
    {T : Type*} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (u : X → ℤ) :
    ‖(∫ y, κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) -
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j)‖ ≤ δ := by
  let : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit)) := hcompact
  apply nativePhysicalHaarExpansion (X := X) (m := m) (J := J) U ν W F c κ δ physicalN u N
    (Nat.pos_of_ne_zero (NeZero.ne N)) hWN
  · apply mixedCoveredJet_restrictedComplexDensity_measurable U o basis hb bW N
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
      (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    exact forecastLawDensityPhysicalChartSource_measurable B U basis S law density selected sample x
      active Y N volume base physicalN τ hdensity u
  · intro poly hm
    exact happrox poly hm u

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact in

theorem forecastLawDensityPhysicalTarget_ambientHaarComparison
    (hdensity : Measurable density)
    {T : Type} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcover : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmod : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j)) :
    ‖(𝔼 u ∈ integerBox physicalN, W.eval physicalN poly u *
        (κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
          active Y N volume base physicalN τ o hb bW poly hm u)) -
      (𝔼 u ∈ integerBox physicalN, ∫ y,
        κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar)‖ ≤
        2 * δ + M * Real.exp (-E) := by
  have hN (i : X) : 0 < physicalN i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  let : ∀ i, NeZero (physicalN i) := fun i => ⟨(hN i).ne'⟩
  let ref (u : X → ℤ) := ∑ i, c i *
    (W.productUniform (F i)).frozenSingleSiteHaarReference U ν
      (fun j => (u j : ZMod (W.productUniform (F i)).modulus))
      (fun j => (u j : ℝ) / physicalN j)
  have hfirst := (Classical.choose_spec (exists_nativeForecast_ambient_comparison m)).2
    U ν poly hp hm W F c
      (fun u => κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u)
      hP hE hX hdim hLip hcover hmod hmass physicalN hlarge hRrank hrank
      (fun u _ => happrox poly hm u)
  have hpoint (u : X → ℤ) :
      ‖(∫ y, κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) - ref u‖ ≤ δ := by
    exact forecastLawDensityPhysicalTarget_nativeHaarExpansion B U basis S law density selected sample x
      active Y N volume base physicalN τ o hb bW ν hdensity W F c κ δ hWN happrox u
  have hlast : ‖(𝔼 u ∈ integerBox physicalN, ref u) -
      (𝔼 u ∈ integerBox physicalN, ∫ y,
        κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U W physicalN u N y ∂haar)‖ ≤ δ := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (integerBox_nonempty physicalN)
    intro u _
    rw [norm_sub_rev]
    exact hpoint u
  have hlinear : (𝔼 u ∈ integerBox physicalN, ref u) =
      ∑ i, c i * (𝔼 u ∈ integerBox physicalN,
        (W.productUniform (F i)).frozenSingleSiteHaarReference U ν
          (fun j => (u j : ZMod (W.productUniform (F i)).modulus))
          (fun j => (u j : ℝ) / physicalN j)) := by
    unfold ref
    rw [Finset.expect_sum_comm]
    simp only [Finset.mul_expect]
  rw [← hlinear] at hfirst
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hfirst hlast).trans_eq (by ring))

end Erdos3.VectorPolynomial

end

end OAI
