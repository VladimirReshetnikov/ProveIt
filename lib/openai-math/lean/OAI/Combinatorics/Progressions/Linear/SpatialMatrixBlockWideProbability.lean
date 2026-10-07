import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
import OAI.Combinatorics.Progressions.Linear.SmoothMatrixBlockBudget

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

noncomputable def spatialRankExponent {K : Type*} : Option K → K →₀ ℕ
  | none => 0
  | some k => Finsupp.single k 1

noncomputable def spatialRankPolynomial {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) : MvPolynomial K R :=
  ∑ e, monomial (spatialRankExponent e) (c e)

theorem spatialRankPolynomial_degree {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) : (spatialRankPolynomial c).totalDegree ≤ 1 := by
  unfold spatialRankPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  apply (totalDegree_monomial_le _ _).trans
  cases e <;> simp [spatialRankExponent]

theorem spatialRankPolynomial_eq {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) :
    spatialRankPolynomial c = C (c none) + ∑ k, C (c (some k)) * X k := by
  rw [spatialRankPolynomial, Fintype.sum_option]
  simp only [spatialRankExponent, monomial_zero', C_mul_X_eq_monomial]

theorem spatialRankPolynomial_actual_eval {K X : Type*} [Fintype K]
    (base : X → ℤ) (noise : Option K × X → ℤ) (x : X) (t : K → ℤ) :
    MvPolynomial.eval t (C (base x) + spatialRankPolynomial (fun e => noise (e,x))) =
      BooleanCubeKernel.jointIntegerPhysicalSite t (base, noise) x := by
  rw [spatialRankPolynomial_eq]
  simp only [map_add, eval_C, map_sum, map_mul, eval_X]
  simp only [BooleanCubeKernel.jointIntegerPhysicalSite, Pi.add_apply,
    BooleanCubeKernel.integerPhysicalSite]
  congr 1
  simp only [mul_comm]

theorem spatialRankPolynomial_top {K R : Type*} [Fintype K] [CommRing R]
    (base : R) (c : Option K → R) :
    homogeneousComponent 1 (C base + spatialRankPolynomial c) =
      ∑ k, C (c (some k)) * X k := by
  rw [spatialRankPolynomial_eq, map_add, map_add, map_sum]
  have hc (r : R) : homogeneousComponent 1 (C r : MvPolynomial K R) = 0 :=
    homogeneousComponent_eq_zero 1 (C r) (by simp)
  simp only [hc, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [C_mul_X_eq_monomial]
  exact homogeneousComponent_eq_self (isHomogeneous_monomial _ (by simp))

def spatialKernelRankSlot {G P A : Type*} (e : A ↪ G) (a : A) : Option (G ⊕ P) :=
  some (.inl (e a))

theorem spatialKernelRankSlot_injective {G P A : Type*} (e : A ↪ G) :
    Function.Injective (spatialKernelRankSlot (P := P) e) := by
  intro a b hab
  exact e.injective (Sum.inl.inj (Option.some.inj hab))

private theorem spatial_kernel_selected_sum {G P A R : Type*}
    [Fintype A] [CommRing R] (e : A ↪ G) (c : A → R) :
    (∑ a, monomial (spatialRankExponent (spatialKernelRankSlot (P := P) e a)) (c a) :
      MvPolynomial (G ⊕ P) R) = ∑ a, c a • X (.inl (e a)) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_C_mul, C_mul_X_eq_monomial]
  rfl

private theorem spatial_kernel_selected_raw {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed) =
      (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
        monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, monomial (spatialRankExponent (spatialKernelRankSlot (P := P) e a)) (c a) := by
  unfold spatialRankPolynomial
  convert modularMonomialArrayPolynomial_selected (E := Option (G ⊕ P))
    (K := G ⊕ P) (R := R) (A := A) spatialRankExponent
    (spatialKernelRankSlot e) (spatialKernelRankSlot_injective (P := P) e) fixed c using 1
  congr 1
  apply Finset.sum_congr
  · congr 1
  · intro d _
    rfl

theorem spatialRankPolynomial_kernel_selected {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed) =
      (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
        monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [spatial_kernel_selected_raw e fixed c, spatial_kernel_selected_sum e c]

theorem spatialRankPolynomial_kernel_selected_top {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    homogeneousComponent 1 (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed)) =
      homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
          monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [spatialRankPolynomial_kernel_selected e fixed c, map_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_C_mul, C_mul_X_eq_monomial]
  exact homogeneousComponent_eq_self (isHomogeneous_monomial _ (by simp))

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {D G A R : Type*} {B : D → Type*} [CommRing R]

theorem samplerLong_killCompl_common (inactive : D → Prop) (h : D → ℕ) (g : G) :
    killCompl (samplerLongEmbedding (B := B) inactive h).injective
      (X (.inl g) : MvPolynomial (SamplerTupleIndex G B h) R) = X (.inl g) := by
  change killCompl (samplerLongEmbedding (B := B) inactive h).injective
    (X (samplerLongEmbedding inactive h (.inl g))) = _
  rw [← rename_X, killCompl_rename_app]

theorem spatialRankPolynomial_kernel_selected_long
    [Fintype D] [Fintype G] [∀ d, Fintype (B d)] [Fintype A]
    (inactive : D → Prop) (h : D → ℕ) (e : A ↪ G)
    (fixed : Option (SamplerTupleIndex G B h) → R) (c : A → R)
    (v : SamplerTupleIndex G B h → R) :
    homogeneousComponent 1
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed))) =
      killCompl (samplerLongEmbedding inactive h).injective
        (homogeneousComponent 1
          (∑ d ∈ Finset.univ.filter
            (fun d => d ∉ Set.range (spatialKernelRankSlot (P := PrincipalTupleIndex B h) e)),
            MvPolynomial.monomial (spatialRankExponent d) (fixed d))) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (SamplerLongVariables inactive G B h) R) := by
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v 1
    (spatialRankPolynomial_degree _), spatialRankPolynomial_kernel_selected_top, map_add]
  apply congrArg₂ (fun P Q => P + Q)
  · apply congrArg (killCompl (samplerLongEmbedding inactive h).injective)
    apply congrArg (homogeneousComponent 1)
    apply Finset.sum_congr
    · exact Finset.filter_congr_decidable _ _ _
    · intro d _
      rfl
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul, samplerLong_killCompl_common]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedSpatialRankPolynomial_kernel_selected_long
    [∀ j, Fintype (I j)] [Fintype G] [∀ d, Fintype (B d)] [Fintype A]
    (inactive : LayerSamplerAxis I n → Prop) (e : A ↪ G)
    (fixed : Option (LayerSamplerVariables G I n B) → R) (c : A → R)
    (v : LayerSamplerVariables G I n B → R) :
    homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed))) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent 1
          (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
            (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) e)),
            MvPolynomial.monomial (spatialRankExponent d) (fixed d))) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (LayerSamplerLongVariables inactive G B) R) := by
  convert spatialRankPolynomial_kernel_selected_long inactive (layerSamplerDegree I n) e fixed c v using 1
  · rfl
  · apply congrArg₂ (fun P Q => P + Q)
    · apply congrArg (killCompl (allocatedLongEmbedding inactive).injective)
      apply congrArg (homogeneousComponent 1)
      apply Finset.sum_congr
      · congr 1
      · intro d _
        rfl
    · rfl

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

def spatialNoiseRankSlot {G P A X : Type*} (e : A ↪ G) :
    A × X → Option (G ⊕ P) × X :=
  fun ax => (spatialKernelRankSlot e ax.1, ax.2)

theorem spatialNoiseRankSlot_injective {G P A X : Type*} (e : A ↪ G) :
    Function.Injective (spatialNoiseRankSlot (P := P) (X := X) e) := by
  intro a b hab
  apply Prod.ext
  · exact spatialKernelRankSlot_injective e (congrArg (fun z : Option (G ⊕ P) × X => z.1) hab)
  · exact congrArg (fun z : Option (G ⊕ P) × X => z.2) hab

noncomputable def resampleSpatialRankNoise {G P A X R : Type*} (e : A ↪ G)
    (fixed : Option (G ⊕ P) × X → R) (c : X → A → R) :
    Option (G ⊕ P) × X → R :=
  Function.extend (spatialNoiseRankSlot e) (fun ax => c ax.2 ax.1) fixed

theorem resampleSpatialRankNoise_coordinate {G P A X R : Type*} (e : A ↪ G)
    (fixed : Option (G ⊕ P) × X → R) (c : X → A → R) (x : X) :
    (fun d => resampleSpatialRankNoise e fixed c (d,x)) =
      Function.extend (spatialKernelRankSlot e) (c x) (fun d => fixed (d,x)) := by
  funext d
  by_cases hd : d ∈ Set.range (spatialKernelRankSlot (P := P) e)
  · obtain ⟨a, rfl⟩ := hd
    change Function.extend (spatialNoiseRankSlot e) (fun ax => c ax.2 ax.1)
      fixed (spatialNoiseRankSlot e (a,x)) = _
    rw [(spatialNoiseRankSlot_injective e).extend_apply,
      (spatialKernelRankSlot_injective e).extend_apply]
  · have hdx : (d,x) ∉ Set.range (spatialNoiseRankSlot (P := P) (X := X) e) := by
      rintro ⟨⟨a,y⟩, h⟩
      exact hd ⟨a, congrArg Prod.fst h⟩
    simp only [resampleSpatialRankNoise, Function.extend_apply' _ _ _ hdx,
      Function.extend_apply' _ _ _ hd]

theorem spatialRankNoise_selected_top {G P A X R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) × X → R) (c : X → A → R) (x : X) :
    homogeneousComponent 1
      (spatialRankPolynomial (fun d => resampleSpatialRankNoise e fixed c (d,x))) =
      homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
          monomial (spatialRankExponent d) (fixed (d,x))) +
      ∑ a, c x a • (MvPolynomial.X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [resampleSpatialRankNoise_coordinate]
  exact spatialRankPolynomial_kernel_selected_top e (fun d => fixed (d,x)) (c x)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {K J R : Type*} [Fintype K] [CommRing R]

theorem spatialRankPolynomial_top_congr (f g : Option K → R)
    (hfg : ∀ k, f (some k) = g (some k)) :
    homogeneousComponent 1 (spatialRankPolynomial f) =
      homogeneousComponent 1 (spatialRankPolynomial g) := by
  have hf := spatialRankPolynomial_top (0 : R) f
  have hg := spatialRankPolynomial_top (0 : R) g
  simp only [map_zero, zero_add] at hf hg
  rw [hf, hg]
  apply Finset.sum_congr rfl
  intro k _
  rw [hfg k]

theorem spatialRankPolynomial_conditioned_top_congr (e : J ↪ K)
    (f g : Option K → R) (hfg : ∀ k, f (some k) = g (some k))
    (v w : K → R) :
    homogeneousComponent 1 (conditionPolynomial e e.injective v (spatialRankPolynomial f)) =
      homogeneousComponent 1 (conditionPolynomial e e.injective w (spatialRankPolynomial g)) := by
  rw [homogeneousComponent_conditionPolynomial_top e e.injective _ v 1
      (spatialRankPolynomial_degree f),
    homogeneousComponent_conditionPolynomial_top e e.injective _ w 1
      (spatialRankPolynomial_degree g),
    spatialRankPolynomial_top_congr f g hfg]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open BooleanCubeKernel

theorem selectedResidueSmoothPMF_singleton_eq_residue
    {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z)
    (hc : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative q r) q) (residueProfileWidth q V)) :
    selectedResidueSmoothPMF q {r} V hV hZ =
      residueSmoothPMF (columnResidueRepresentative q r) q hq V hV hc := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_singleton,
    residueSmoothPMF_conditional_weight]

theorem selectedResidueSmoothWeight_singleton_index_mass_pos
    {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z) :
    0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative q r) q) (residueProfileWidth q V) := by
  rw [residueSmoothWeight_mass _ q hq V hV]
  simpa only [selectedResidueSmoothWeight_singleton] using hZ

theorem selectedResidueSmoothPMF_singleton_eq_independent_map
    {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z) :
    let hc := selectedResidueSmoothWeight_singleton_index_mass_pos q hq r V hV hZ
    selectedResidueSmoothPMF q {r} V hV hZ =
      (independentProductPMF
        (residueSmoothScalarPMFs (columnResidueRepresentative q r) q hq V hV hc)).map
        (residueLatticeArray (columnResidueRepresentative q r) q) := by
  intro hc
  rw [selectedResidueSmoothPMF_singleton_eq_residue q hq r V hV hZ hc,
    residueSmoothPMF, residueSmoothIndexPMF_eq_independent]

theorem selectedResidueSmoothPMF_independent_mixture
    {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V)) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) * φ z) =
      ∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' t, ((independentProductPMF
          (residueSmoothScalarPMFs (boundedColumnResidueRepresentative q r.val)
            q hq V hV (hc r)) t).toReal : ℂ) *
          φ (residueLatticeArray (boundedColumnResidueRepresentative q r.val) q t) := by
  rw [selectedResidueSmoothPMF_bounded_mixture q hq T V hV hZ hc φ]
  apply Finset.sum_congr rfl
  intro r _
  rw [residueSmoothPMF_expectation, residueSmoothIndexPMF_eq_independent]

theorem allocatedSpatialRank_residue_width
    {G P A X : Type*} (e : A ↪ G) (W τ ξ : ℝ) (N q : X → ℕ)
    (a : A) (x : X) :
    residueProfileWidth q (narrowTrimmedSpatialWidths (G := G) (J := P) W τ ξ N)
      (spatialNoiseRankSlot e (a,x)) = trimmedSpatialSlopeScale W τ N q x := by
  exact congrFun (narrowTrimmedSpatial_residue_scale (G := G) (J := P) W τ ξ N q x)
    (some (.inl (e a)))

theorem allocatedSpatialRank_scalar_law
    {G P A X : Type*} [Fintype G] [Fintype P] [Fintype X]
    (e : A ↪ G) (residue : Option (G ⊕ P) × X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (N : X → ℕ)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < N x)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q)
      (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N))) (a : A) (x : X)
    (hwidth : 0 < trimmedSpatialSlopeScale W τ N q x)
    (hmass : 0 < shiftedSmoothSampleSum
      (-(residue (spatialNoiseRankSlot e (a,x)) : ℝ) / q x)
      (trimmedSpatialSlopeScale W τ N q x)) :
    residueSmoothScalarPMFs residue q hq (narrowTrimmedSpatialWidths W τ ξ N)
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hZ (spatialNoiseRankSlot e (a,x)) =
      shiftedSmoothCoefficientPMF
        (-(residue (spatialNoiseRankSlot e (a,x)) : ℝ) / q x)
        (trimmedSpatialSlopeScale W τ N q x) hwidth hmass := by
  unfold residueSmoothScalarPMFs
  have hw := allocatedSpatialRank_residue_width (P := P) e W τ ξ N q a x
  simp only [residueProfileCenter, spatialNoiseRankSlot, spatialKernelRankSlot] at *
  congr 1

theorem allocatedSpatialRank_scalar_mass_pos
    {G P A X : Type*} [Fintype G] [Fintype P] [Fintype X]
    (e : A ↪ G) (residue : Option (G ⊕ P) × X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (N : X → ℕ)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < N x)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q)
      (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N))) (a : A) (x : X) :
    0 < shiftedSmoothSampleSum
      (-(residue (spatialNoiseRankSlot e (a,x)) : ℝ) / q x)
      (trimmedSpatialSlopeScale W τ N q x) := by
  have h := shiftedSmoothProductMass_coordinate_pos (residueProfileCenter residue q)
    (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N))
    (residueProfileWidth_pos q _ hq (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN))
    hZ (spatialNoiseRankSlot e (a,x))
  rw [allocatedSpatialRank_residue_width] at h
  exact h

theorem allocatedSpatialRank_index_mass_pos
    {G P X : Type*} [Fintype G] [Fintype P] [Fintype X]
    (residue : Option (G ⊕ P) × X → ℤ) (q N : X → ℕ)
    (hq : ∀ x, 0 < q x) (hN : ∀ x, 0 < N x)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) *
      (8 * (probabilityProfileLipschitz : ℝ)) ≤ (ξ * τ) * (N x : ℝ)) :
    0 < shiftedSmoothProductMass (residueProfileCenter residue q)
      (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N)) := by
  have hscale (z : Option (G ⊕ P) × X) :
      8 * (probabilityProfileLipschitz : ℝ) ≤
        residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z :=
    narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 (by positivity) N q hN hq hsize z
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun z => smoothSamplingScale_pos (hscale z))]
  exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))

theorem allocatedSpatialRank_scalar_law_of_cell_mass
    {G P A X : Type*} [Fintype G] [Fintype P] [Fintype X]
    (e : A ↪ G) (residue : Option (G ⊕ P) × X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (N : X → ℕ)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < N x)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q)
      (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N))) (a : A) (x : X) :
    residueSmoothScalarPMFs residue q hq (narrowTrimmedSpatialWidths W τ ξ N)
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hZ (spatialNoiseRankSlot e (a,x)) =
      shiftedSmoothCoefficientPMF
        (-(residue (spatialNoiseRankSlot e (a,x)) : ℝ) / q x)
        (trimmedSpatialSlopeScale W τ N q x)
        (trimmedSpatial_scales_pos hW hτ N q x (hN x) (hq x)).2
        (allocatedSpatialRank_scalar_mass_pos e residue q hq N hW hτ hξ hN hZ a x) :=
  allocatedSpatialRank_scalar_law e residue q hq N hW hτ hξ hN hZ a x _ _

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

abbrev SpatialMatrixBlockIndex (X : Type*) := Fin 2 × X × X

def spatialMatrixBlockSlot {G P X : Type*} (e : Fin 2 × X ↪ G) :
    SpatialMatrixBlockIndex X ↪ Option (G ⊕ P) × X where
  toFun t := (some (.inl (e (t.1,t.2.1))),t.2.2)
  inj' := by
    rintro ⟨b,j,x⟩ ⟨c,k,y⟩ h
    have hx : x = y := congrArg Prod.snd h
    have hbj : (b,j) = (c,k) := e.injective
      (Sum.inl.inj (Option.some.inj (congrArg Prod.fst h)))
    have hb : b = c := congrArg Prod.fst hbj
    have hj : j = k := congrArg Prod.snd hbj
    subst c
    subst k
    subst y
    rfl

noncomputable def spatialMatrixNormalizedEntries {G P X : Type*} (e : Fin 2 × X ↪ G)
    (V : Option (G ⊕ P) × X → ℝ) (z : Option (G ⊕ P) × X → ℤ) :
    SpatialMatrixBlockIndex X → ℝ :=
  fun t => (z (spatialMatrixBlockSlot e t) : ℝ) / V (spatialMatrixBlockSlot e t)

noncomputable def spatialMatrixIndexCenter {G P X : Type*} (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) : SpatialMatrixBlockIndex X → ℝ :=
  fun t => -(residue (spatialMatrixBlockSlot e t) : ℝ) / q t.2.2

noncomputable def spatialMatrixIndexWidth {G P X : Type*} (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (V : Option (G ⊕ P) × X → ℝ) : SpatialMatrixBlockIndex X → ℝ :=
  fun t => V (spatialMatrixBlockSlot e t) / q t.2.2

theorem spatialMatrixIndexWidth_pos {G P X : Type*} (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z) (t : SpatialMatrixBlockIndex X) :
    0 < spatialMatrixIndexWidth e q V t :=
  div_pos (hV _) (by exact_mod_cast hq t.2.2)

variable {G P X : Type*} [Fintype G] [Fintype P] [Fintype X]

theorem spatialMatrixIndexMass_pos (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    0 < shiftedSmoothProductMass (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) :=
  shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ

theorem spatialMatrixNormalizedEntries_residue (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (t : Option (G ⊕ P) × X → ℤ) :
    spatialMatrixNormalizedEntries e V (residueLatticeArray residue q t) =
      rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (fun i => t (spatialMatrixBlockSlot e i)) := by
  funext i
  exact (congrFun (residueProfile_point residue q hq V hV t) (spatialMatrixBlockSlot e i)).symm

theorem spatialMatrixIndexPMF_marginal (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    (residueSmoothIndexPMF residue q hq V hV hZ).map
      (fun t i => t (spatialMatrixBlockSlot e i)) =
      shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ) := by
  exact shiftedSmoothProductPMF_selected_marginal (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ

theorem spatialMatrixNormalizedEntries_residue_law (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    (residueSmoothPMF residue q hq V hV hZ).map (spatialMatrixNormalizedEntries e V) =
      (shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ)).map
        (rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)) := by
  rw [residueSmoothPMF, PMF.map_comp]
  have hf : spatialMatrixNormalizedEntries e V ∘ residueLatticeArray residue q =
      rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) ∘
        (fun t i => t (spatialMatrixBlockSlot e i)) := by
    funext t
    exact spatialMatrixNormalizedEntries_residue e residue q hq V hV t
  rw [hf, ← PMF.map_comp, spatialMatrixIndexPMF_marginal]

theorem spatialMatrixNormalizedEntries_singleton_law (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern (Option (G ⊕ P)) X q)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z) :
    let hc := selectedResidueSmoothWeight_singleton_index_mass_pos q hq r V hV hZ
    (selectedResidueSmoothPMF q {r} V hV hZ).map (spatialMatrixNormalizedEntries e V) =
      (shiftedSmoothProductPMF (spatialMatrixIndexCenter e (columnResidueRepresentative q r) q)
        (spatialMatrixIndexWidth e q V) (spatialMatrixIndexWidth_pos e q hq V hV)
        (spatialMatrixIndexMass_pos e _ q hq V hV hc)).map
          (rectangularLatticePoint (spatialMatrixIndexCenter e (columnResidueRepresentative q r) q)
            (spatialMatrixIndexWidth e q V)) := by
  intro hc
  rw [selectedResidueSmoothPMF_singleton_eq_residue q hq r V hV hZ hc]
  exact spatialMatrixNormalizedEntries_residue_law e _ q hq V hV hc

theorem spatialMatrixNormalizedEntries_residue_expectation (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V))
    (φ : (SpatialMatrixBlockIndex X → ℝ) → ℂ) :
    (∑' z, ((residueSmoothPMF residue q hq V hV hZ z).toReal : ℂ) *
      φ (spatialMatrixNormalizedEntries e V z)) =
      ∑' t, ((shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ) t).toReal : ℂ) *
          φ (rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) t) := by
  rw [residueSmoothPMF_expectation]
  simp only [spatialMatrixNormalizedEntries_residue e residue q hq V hV]
  exact shiftedSmoothProductPMF_selected_expectation (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ
    (fun t => φ (rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) t))

theorem spatialMatrixNormalizedEntries_mixture_expectation (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) X q))
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q) (residueProfileWidth q V))
    (φ : (SpatialMatrixBlockIndex X → ℝ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) *
      φ (spatialMatrixNormalizedEntries e V z)) =
      ∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' t, ((shiftedSmoothProductPMF
          (spatialMatrixIndexCenter e (boundedColumnResidueRepresentative q r.val) q)
          (spatialMatrixIndexWidth e q V) (spatialMatrixIndexWidth_pos e q hq V hV)
          (spatialMatrixIndexMass_pos e _ q hq V hV (hc r)) t).toReal : ℂ) *
            φ (rectangularLatticePoint
              (spatialMatrixIndexCenter e (boundedColumnResidueRepresentative q r.val) q)
              (spatialMatrixIndexWidth e q V) t) := by
  rw [selectedResidueSmoothPMF_bounded_mixture q hq T V hV hZ hc]
  apply Finset.sum_congr rfl
  intro r _
  rw [spatialMatrixNormalizedEntries_residue_expectation e _ q hq V hV (hc r)]

theorem spatialMatrixNormalizedEntries_mixture_event (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) X q))
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q) (residueProfileWidth q V))
    (bad : (SpatialMatrixBlockIndex X → ℝ) → Prop) :
    (∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
      (if bad (spatialMatrixNormalizedEntries e V z) then 1 else 0)) =
      ∑ r : T, selectedResidueCellWeight q T V r *
        ∑' t, (shiftedSmoothProductPMF
          (spatialMatrixIndexCenter e (boundedColumnResidueRepresentative q r.val) q)
          (spatialMatrixIndexWidth e q V) (spatialMatrixIndexWidth_pos e q hq V hV)
          (spatialMatrixIndexMass_pos e _ q hq V hV (hc r)) t).toReal *
            (if bad (rectangularLatticePoint
              (spatialMatrixIndexCenter e (boundedColumnResidueRepresentative q r.val) q)
              (spatialMatrixIndexWidth e q V) t) then 1 else 0) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_tsum, Complex.ofReal_sum, Complex.ofReal_mul,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using
    spatialMatrixNormalizedEntries_mixture_expectation e q hq T V hV hZ hc
      (fun z => if bad z then 1 else 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def spatialMatrixBlockEquiv (n : ℕ) :
    SpatialMatrixBlockIndex (Fin n) ≃ Fin (2 * n * n) :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_assoc 2 n n).symm))

def spatialMatrixBlockEntry (n : ℕ) (b : Fin 2) :
    Fin n × Fin n ↪ Fin (2 * n * n) where
  toFun rc := spatialMatrixBlockEquiv n (b, rc.2, rc.1)
  inj' := by
    intro x y h
    have hs := (spatialMatrixBlockEquiv n).injective h
    have hp := congrArg Prod.snd hs
    exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

@[simp] theorem spatialMatrixBlockEntry_apply (n : ℕ) (b : Fin 2) (r c : Fin n) :
    spatialMatrixBlockEntry n b (r,c) = spatialMatrixBlockEquiv n (b,c,r) := rfl

@[simp] theorem spatialMatrixBlockEntry_symm (n : ℕ) (b : Fin 2) (r c : Fin n) :
    (spatialMatrixBlockEquiv n).symm (spatialMatrixBlockEntry n b (r,c)) = (b,c,r) :=
  (spatialMatrixBlockEquiv n).symm_apply_apply _

theorem spatialMatrixBlockEntry_reindex_eval {R : Type*}
    (n : ℕ) (z : SpatialMatrixBlockIndex (Fin n) → R) (b : Fin 2) (r c : Fin n) :
    z ((spatialMatrixBlockEquiv n).symm (spatialMatrixBlockEntry n b (r,c))) = z (b,c,r) := by
  rw [spatialMatrixBlockEntry_symm]

theorem spatialMatrixBlockEntry_disjoint (n : ℕ) {b c : Fin 2} (hbc : b ≠ c) :
    Disjoint (Set.range (spatialMatrixBlockEntry n b))
      (Set.range (spatialMatrixBlockEntry n c)) := by
  rw [Set.disjoint_left]
  rintro k ⟨x, rfl⟩ ⟨y, he⟩
  have hh := (spatialMatrixBlockEquiv n).injective he
  exact hbc (congrArg Prod.fst hh).symm

theorem shiftedSmoothProductPMF_reindex {D J : Type*} [Fintype D] [Fintype J]
    (e : D ≃ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z d => z (e d)) =
      shiftedSmoothProductPMF (fun d => a (e d)) (fun d => S (e d))
        (fun d => hS (e d)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) :=
  shiftedSmoothProductPMF_selected_marginal e.toEmbedding a S hS hZ

theorem rectangularLatticePoint_reindex {D J : Type*} (e : D → J)
    (a S : J → ℝ) (z : J → ℤ) :
    rectangularLatticePoint (fun d => a (e d)) (fun d => S (e d)) (fun d => z (e d)) =
      fun d => rectangularLatticePoint a S z (e d) := rfl

theorem spatialMatrixBlock_normalized_law (n : ℕ)
    (a S : SpatialMatrixBlockIndex (Fin n) → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map
      (fun z k => rectangularLatticePoint a S z ((spatialMatrixBlockEquiv n).symm k)) =
      (shiftedSmoothProductPMF
        (fun k => a ((spatialMatrixBlockEquiv n).symm k))
        (fun k => S ((spatialMatrixBlockEquiv n).symm k))
        (fun k => hS ((spatialMatrixBlockEquiv n).symm k))
        (shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockEquiv n).symm a S hS hZ)).map
          (rectangularLatticePoint (fun k => a ((spatialMatrixBlockEquiv n).symm k))
            (fun k => S ((spatialMatrixBlockEquiv n).symm k))) := by
  exact shiftedSmoothProductPMF_selected_map (spatialMatrixBlockEquiv n).symm.toEmbedding
    a S hS hZ
    (rectangularLatticePoint (fun k => a ((spatialMatrixBlockEquiv n).symm k))
      (fun k => S ((spatialMatrixBlockEquiv n).symm k)))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

private theorem spatialMatrix_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

noncomputable def spatialMatrixBlockThreshold (n : ℕ) (η : ℝ) : ℝ :=
  shiftedSmoothSublevelThreshold (2 * n * n) n 2 η

theorem spatialMatrixBlockThreshold_pos {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    0 < spatialMatrixBlockThreshold n η :=
  shiftedSmoothSublevelThreshold_pos (by positivity) n 2 hη

def spatialMatrixBlockBad {G P : Type*} {n : ℕ} (e : Fin 2 × Fin n ↪ G)
    (V : Option (G ⊕ P) × Fin n → ℝ) (κ : ℝ)
    (z : Option (G ⊕ P) × Fin n → ℤ) : Prop :=
  ∃ b : Fin 2, |Matrix.det (fun i j : Fin n => spatialMatrixNormalizedEntries e V z (b,j,i))| ≤ κ

theorem spatialMatrixBlock_flat_bad_probability {n : ℕ} (hn : 0 < n)
    (a S : SpatialMatrixBlockIndex (Fin n) → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ b : Fin 2, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (b,j,i))| ≤
        spatialMatrixBlockThreshold n η)) true).toReal ≤ η / 2 := by
  unfold spatialMatrixBlockThreshold at hsmall ⊢
  simp only [spatialMatrix_decide_eq_classical]
  have h := smoothMatrixBlock_bad_probability hn (show 0 < 2*n*n by positivity)
    (spatialMatrixBlockEntry n)
    (fun k => a ((spatialMatrixBlockEquiv n).symm k))
    (fun k => S ((spatialMatrixBlockEquiv n).symm k))
    (fun k => hS ((spatialMatrixBlockEquiv n).symm k))
    (shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockEquiv n).symm a S hS hZ)
    (fun k => hlarge ((spatialMatrixBlockEquiv n).symm k)) hδ hδ1 hη
    (fun k => hmesh ((spatialMatrixBlockEquiv n).symm k))
    (by simpa only [Fintype.card_fin, spatialMatrixBlockThreshold] using hsmall)
  rw [← shiftedSmoothProductPMF_reindex (spatialMatrixBlockEquiv n).symm a S hS hZ,
    PMF.map_comp] at h
  simpa only [Function.comp_def, rectangularLatticePoint_reindex,
    spatialMatrixBlockEntry_reindex_eval, Fintype.card_fin, spatialMatrixBlockThreshold,
    spatialMatrix_decide_eq_classical] using h

variable {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}

theorem spatialMatrixBlock_residue_bad_probability (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
    (residue : Option (G ⊕ P) × Fin n → ℤ) (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V))
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ spatialMatrixIndexWidth e q V i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hmesh : ∀ i, 1 / spatialMatrixIndexWidth e q V i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((residueSmoothPMF residue q hq V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  let test : (SpatialMatrixBlockIndex (Fin n) → ℝ) → Bool := fun z => decide
    (∃ b : Fin 2, |Matrix.det (fun i j : Fin n => z (b,j,i))| ≤ spatialMatrixBlockThreshold n η)
  have heq := congrArg (fun law : PMF (SpatialMatrixBlockIndex (Fin n) → ℝ) =>
      (law.map test true).toReal)
    (spatialMatrixNormalizedEntries_residue_law e residue q hq V hV hZ)
  have hbound := spatialMatrixBlock_flat_bad_probability hn
    (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
    (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ)
    hlarge hδ hδ1 hη hmesh hsmall
  simp only [PMF.map_comp, Function.comp_def, test, spatialMatrixBlockBad,
    spatialMatrix_decide_eq_classical] at heq hbound ⊢
  exact heq.trans_le hbound

theorem spatialMatrixBlock_cellMass_pos
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (residue : Option (G ⊕ P) × Fin n → ℤ) :
    0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos q V hq hV)]
  exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))

theorem spatialMatrixBlock_bad_probability (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hmesh : ∀ i, 1 / spatialMatrixIndexWidth e q V i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  let hc (r : T) := spatialMatrixBlock_cellMass_pos q hq V hV hscale
    (boundedColumnResidueRepresentative q r.val)
  apply selectedResidueSmoothPMF_bind_le_of_cells q hq T V hV hZ hc
    (fun z => PMF.pure (decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z))) true (η/2)
  intro r
  exact spatialMatrixBlock_residue_bad_probability hn e _ q hq V hV (hc r)
    (fun i => hscale (spatialMatrixBlockSlot e i)) hδ hδ1 hη hmesh hsmall

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrixBlockThreshold_inverse_le_exp {n : ℕ} (hn : 0 < n)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (spatialMatrixBlockThreshold n η)⁻¹ ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget (2 * n * n) n 2 E) :=
  smoothMatrixBlock_threshold_inverse_le_exp (by positivity) hn 2 hη hE hηb

theorem spatialMatrixBlock_bad_probability_of_exp_width
    {G P : Type*} [Fintype G] [Fintype P] {n : ℕ} (hn : 0 < n)
    (e : Fin 2 × Fin n ↪ G)
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E)
    (hwide : ∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * n * n) n 2 E) ≤
      spatialMatrixIndexWidth e q V i) :
    ((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  have hκ := spatialMatrixBlockThreshold_pos hn hη
  have hδ := smoothMatrixBlockMesh_spec n (2 * n * n) hκ
  have hwide' (i) := smoothMatrixBlockMesh_width_spec n (2 * n * n) hκ
    ((smoothMatrixBlock_actual_width_le_exp (by positivity) hn 2 hη hE hηb).trans (hwide i))
  exact spatialMatrixBlock_bad_probability hn e q hq T V hV hZ hscale
    hδ.1.le hδ.2.1 hη (fun i => (hwide' i).2.2) hδ.2.2

end Erdos3

end

end OAI
