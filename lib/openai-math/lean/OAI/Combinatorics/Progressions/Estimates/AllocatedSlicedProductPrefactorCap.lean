/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedDiscreteIdeal
import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedSupportedSite
import OAI.Combinatorics.Progressions.Probability.AllocatedGlobalMaskedDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "Output" => (Σ _e : Row, Unit)

theorem exists_allocatedSlicedPhysical_supported_site_expansion
    [∀ j, DecidableEq (I j)]
    (hR : ∀ j, 0 < R j)
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε)
    (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let Q := slicedJointDensityLogBudget O m P + P
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    ∃ z : ℕ, (z : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (c : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (NNReal.mk (Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12)) (Real.exp_nonneg _) + C) (f k s)) ∧
        (∀ k s v, (∃ d, (4 : ℝ) < |v d|) → f k s v = 0) ∧
        ∀ v : Jet → ℝ,
          ‖((∏ o : Output, R o.1.2.val.1) : ℂ) *
              (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width v : ℂ) -
            ∑ k, c k * ∏ t, f k t (oneCubeNormalizedSites grid (fun a => R a.1) v t)‖ ≤ ε := by
  intro Q C
  obtain ⟨χ, hone, z, hz, c, f, hc, hf, hLf, hs, herr⟩ :=
    exists_allocatedSlicedIdeal_supported_site_expansion B U basis S O hO hB lower width
      ha hδ hP haP hδP hprincipal hw hl 2 (by norm_num) hε (by norm_num only [NNReal.coe_ofNat] ; linarith) hεP
  refine ⟨z, hz, c, f, hc, hf, ?_, ?_, ?_⟩
  · convert hLf using 1; norm_num [Q, C]
  · simpa only [NNReal.coe_ofNat, show (2 : ℝ) * 2 = 4 by norm_num] using hs
  · intro v
    have he := herr (oneCubeNormalizedSites grid (fun a => R a.1) v)
    have hd := allocatedSlicedPhysicalJetIdeal_normalized_coordinates B U basis S hR hB lower width v
    have hcut := allocatedSlicedPhysicalJetIdeal_cutoff B U basis S hR hB lower width hwidth
      ha hδ hprincipal hw hl χ hone v
    have hcC := congrArg Complex.ofReal hcut
    simp only [Complex.ofReal_mul, Complex.ofReal_prod] at hcC
    have hdC := congrArg Complex.ofReal hd
    simp only [Complex.ofReal_mul] at hdC
    rw [← hdC, mul_left_comm, hcC] at he
    simpa only [Complex.ofReal_prod] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "Output" => (Σ _e : Row, Unit)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin 1) (Fin.val j + 1))
local notation "BoundedJet" => (Σ a : {a // ¬grid a}, BoundedBooleanJet (Fin 1) (Fin.val (Sigma.fst (Subtype.val a)) + 1))

theorem exists_allocatedSlicedIdeal_bounded_site_expansion
    [∀ j, DecidableEq (I j)]
    (hR : ∀ j, 0 < R j)
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε)
    (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let Q := slicedJointDensityLogBudget O m P + P
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    ∃ z : ℕ, (z : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (c : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (NNReal.mk (Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12)) (Real.exp_nonneg _) + C) (f k s)) ∧
        (∀ k s v, (∃ d, (4 : ℝ) < |v d|) → f k s v = 0) ∧
        ∀ v : AllocatedLongJetRows B U basis S jets,
          ‖((∏ o : BoundedJet, R o.1.val.1 : ℝ) : ℂ) *
              (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width (allocatedOneCubeFullLongJets B U basis S v) : ℂ) -
            ∑ k, c k * ∏ t, f k t (allocatedIdealSiteCoordinates B U basis S v t)‖ ≤ ε := by
  intro Q C
  obtain ⟨z, hz, c, f, hc, hf, hLf, hs, herr⟩ :=
    exists_allocatedSlicedPhysical_supported_site_expansion B U basis S hR O hO hB lower width hwidth
      ha hδ hP haP hδP hprincipal hw hl hε hHP hεP
  have hcard : (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) : ℝ) ≤
      Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, pow_one, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hz _).trans_eq (Real.exp_nat_mul _ _).symm
  refine ⟨z, hz, hcard, c, f, hc, hf, hLf, hs, ?_⟩
  intro v
  have he := herr (allocatedOneCubeFullLongJets B U basis S v)
  have hprod : (∏ o : Output, R o.1.2.val.1) = ∏ o : BoundedJet, R o.1.val.1 := by
    exact (oneCube_endpoint_scale_product (fun a : {a // ¬grid a} => R a.val.1)).trans
      (oneCube_bounded_scale_product (fun a : {a // ¬grid a} => R a.val.1)
        (fun a => a.val.1.val + 1) (fun _ => Nat.le_add_left 1 _)).symm
  simp only [← Complex.ofReal_prod, hprod, allocatedOneCubeNormalizedSites_eq] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedWholeMaskedCoveredProfile_measurable
    (w : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d w q f) := by
  apply allocatedCoveredProfileDensity_measurable B U b hR hσ S x
    (principalAxisRestrict grid w) (principalAxisRestrict (fun a => ¬grid a) w) rows hb o bW d
    (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  exact allocatedLongProfileDensity_measurable B U b S x rows q _ f hf

theorem allocatedWholeMaskedCoveredProfile_mean_measurable
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (w : A → PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (fun y => (p.mean (fun a =>
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (w a) q f y) : ℂ)) :=
  (p.mean_measurable _ (fun a =>
    allocatedWholeMaskedCoveredProfile_measurable B U b hR hσ S x rows hb o bW d (w a) q f hf)).complex_ofReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators Classical

def oneCubeRowsEquiv (rows : Finset (Finset (Fin 1))) (hrows : ∀ t, t ∈ rows) :
    Finset (Fin 1) ≃ rows where
  toFun t := ⟨t, hrows t⟩
  invFun t := t.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem realRowsSiteValue_oneCube (rows : Finset (Finset (Fin 1))) (hrows : ∀ t, t ∈ rows)
    (v : rows → ℝ) (t : Finset (Fin 1)) :
    realRowsSiteValue rows v t = v ⟨∅, hrows ∅⟩ + if (0 : Fin 1) ∈ t then v ⟨{0}, hrows {0}⟩ else 0 := by
  unfold realRowsSiteValue
  rw [← Fintype.sum_equiv (oneCubeRowsEquiv rows hrows)
    (fun s => v ⟨s,hrows s⟩ * (if s ⊆ t then 1 else 0))
    (fun s => v s * (if s.val ⊆ t then 1 else 0)) (fun _ => rfl)]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [huniv]
  by_cases ht : (0 : Fin 1) ∈ t <;> simp [ht]

theorem oneCube_rows_scale_product {D : Type*} [Fintype D] (R : D → ℝ)
    (rows : D → Finset (Finset (Fin 1))) (hrows : ∀ d t, t ∈ rows d) :
    (∏ o : (Σ d, ↥(rows d)), R o.1) = ∏ d, (R d)^2 := by
  have hc (d) : Fintype.card ↥(rows d) = 2 := by
    rw [← Fintype.card_congr (oneCubeRowsEquiv (rows d) (hrows d))]
    simp
  simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, hc]

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "jets" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

noncomputable def allocatedOneCubeRowFullJets (z : AllocatedLongJetRows B U basis S jets) : Jet → ℝ :=
  fun q => allocatedLongJetRealCoordinates B U basis S z ⟨q.1, ⟨q.2, hrows q.1.val.1 q.2⟩⟩

theorem allocatedOneCubeNormalizedSites_rows (z : AllocatedLongJetRows B U basis S jets) :
    oneCubeNormalizedSites grid (fun a => R a.1) (allocatedOneCubeRowFullJets B U basis S rowSets hrows z) =
      allocatedRowIdealCoordinates B U basis S rowSets z := by
  funext t a
  unfold allocatedRowIdealCoordinates
  rw [realRowsSiteValue_oneCube _ (hrows a.1)]
  by_cases ha : ¬grid a
  · rw [oneCubeNormalizedSites, dite_eq_left ha]
    by_cases ht : (0 : Fin 1) ∈ t
    · simp only [dite_eq_left ha, ite_eq_left ht, allocatedOneCubeRowFullJets, add_div]
    · simp only [dite_eq_left ha, ite_eq_right ht, allocatedOneCubeRowFullJets, add_zero]
  · simp only [oneCubeNormalizedSites, dite_eq_right ha, ite_self, zero_add]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "Output" => (Σ _e : Row, Unit)

variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
local notation "jets" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "RowJet" => (Σ a : {a // ¬grid a}, {t : Finset (Fin 1) // t ∈ rowSets (Sigma.fst (Subtype.val a))})

theorem exists_allocatedSlicedIdeal_row_site_expansion
    [∀ j, DecidableEq (I j)]
    (hR : ∀ j, 0 < R j)
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε)
    (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let Q := slicedJointDensityLogBudget O m P + P
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    ∃ z : ℕ, (z : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (c : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (NNReal.mk (Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12)) (Real.exp_nonneg _) + C) (f k s)) ∧
        (∀ k s v, (∃ d, (4 : ℝ) < |v d|) → f k s v = 0) ∧
        ∀ v : AllocatedLongJetRows B U basis S jets,
          ‖((∏ o : RowJet, R o.1.val.1 : ℝ) : ℂ) *
              (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width (allocatedOneCubeRowFullJets B U basis S rowSets hrows v) : ℂ) -
            ∑ k, c k * ∏ t, f k t (allocatedRowIdealCoordinates B U basis S rowSets v t)‖ ≤ ε := by
  intro Q C
  obtain ⟨z, hz, c, f, hc, hf, hLf, hs, herr⟩ :=
    exists_allocatedSlicedPhysical_supported_site_expansion B U basis S hR O hO hB lower width hwidth
      ha hδ hP haP hδP hprincipal hw hl hε hHP hεP
  have hcard : (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) : ℝ) ≤
      Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, pow_one, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hz _).trans_eq (Real.exp_nat_mul _ _).symm
  refine ⟨z, hz, hcard, c, f, hc, hf, hLf, hs, ?_⟩
  intro v
  have he := herr (allocatedOneCubeRowFullJets B U basis S rowSets hrows v)
  have hprod : (∏ o : Output, R o.1.2.val.1) = ∏ o : RowJet, R o.1.val.1 := by
    exact (oneCube_endpoint_scale_product (fun a : {a // ¬grid a} => R a.val.1)).trans
      (oneCube_rows_scale_product (fun a : {a // ¬grid a} => R a.val.1)
        (fun a => rowSets a.val.1) (fun a => hrows a.val.1)).symm
  simp only [← Complex.ofReal_prod, hprod, allocatedOneCubeNormalizedSites_rows] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedSlicedRowIdeal
    (z : (Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) : ℝ :=
  allocatedSlicedPhysicalJetIdeal B U b S hR hB lower width
    (fun q => z ⟨q.1, ⟨q.2, hrows q.1.val.1 q.2⟩⟩)

include hperiod hM hm hR hC hchart hbudget in
theorem exists_allocated_global_masked_sliced_approximation
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε) (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    let Q := slicedJointDensityLogBudget O m P + P
    let A := Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, (4 : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin 1)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε := by
  intro cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, herr⟩ :=
    exists_allocatedSlicedIdeal_row_site_expansion B U b S rowSets hrows hR O hO hB lower width hwidth
      ha hδ hP haP hδP hprincipal hw hl hε hHP hεP
  refine ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, ?_, ?_, ?_, ?_, ?_⟩
  · exact allocatedProductMaskedIdealCoefficient_bound B U b S rowSets x y₀ q d period hperiod hM hm a ha'
  · intro label i s y
    exact allocatedMaskedSiteChartFactor_norm B U b S o hb bW d r hr period label (f i s) (hf i s) y
  · intro label i s
    exact allocatedMaskedSiteChartFactor_measurable B U b S o hb bW d r hr period label (f i s) (hLf i s) (hf i s)
  · exact allocatedProductChartIdealApproximation_measurable B U b S rowSets x y₀ q d period r hr hb o bW a f hLf hf
  · intro y
    apply allocatedProductChartDensityApproximation_error B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget a f
      (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) hε.le
    intro z
    exact herr z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "rows" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "e" => (fun j => Equiv.symm (oneCubeRowsEquiv (rowSets j) (hrows j)))
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedSlicedRowIdeal_measurable :
    Measurable (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) := by
  apply (allocatedSlicedPhysicalJetIdeal_measurable B U b S hR hB lower width).comp
  exact Measurable.of_eval (fun index => measurable_pi_apply _)

theorem allocatedWholeMaskedSlicedProfile_mean_measurable
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (w : A → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
    (q : ℕ) :
    Measurable (fun y => (p.mean (fun a => allocatedWholeMaskedCoveredProfile B U b hR hσ S x
      (fun j => (Subtype.val : rows j → Finset (Fin 1))) hb o bW d (w a) q
      (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y) : ℂ)) :=
  allocatedWholeMaskedCoveredProfile_mean_measurable B U b hR hσ S x
    (fun j => (Subtype.val : rows j → Finset (Fin 1))) hb o bW d p w q _
    (allocatedSlicedRowIdeal_measurable B U b hR S rowSets hrows hB lower width)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)] [∀ j, DecidableEq (I j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable (hR : ∀ j, 0 < R j) (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [(index : Fin m) → DecidableEq (I index)] in
theorem allocatedSlicedRowIdeal_normalized_cap
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (z : (Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) :
    ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
      (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width z : ℂ)‖ ≤
      Real.exp (slicedJointDensityLogBudget O m P) := by
  let Output := Σ _e : OneCubeActiveRow grid, Unit
  have hp : 0 < ∏ o : Output, R o.1.2.val.1 := Finset.prod_pos (fun o _ => hR _)
  have hprod : (∏ o : Output, R o.1.2.val.1) = ∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 :=
    (oneCube_endpoint_scale_product (fun a : {a // ¬grid a} => R a.val.1)).trans
      (oneCube_rows_scale_product (fun a : {a // ¬grid a} => R a.val.1)
        (fun a => rowSets a.val.1) (fun a => hrows a.val.1)).symm
  have hb := allocatedSlicedAveragedIdealDensity_uniform_bounds B U b S O hO hB lower width
    ha hδ hP haP hδP hprincipal hw hl
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, ← hprod]
  unfold allocatedSlicedRowIdeal allocatedSlicedPhysicalJetIdeal allocatedSlicedPhysicalEndpointIdeal
  rw [diagonalDensityTransport_eq, abs_of_pos hp, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  rw [abs_of_nonneg (hb.1 _).1]
  exact (hb.1 _).2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

include hperiod hM hm hR hC hchart hbudget in

theorem allocatedSlicedProductPrefactor_cap
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y‖ ≤
      ‖inverseNormalizer‖ * (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) *
        Real.exp (slicedJointDensityLogBudget O m P) := by
  let aa : Empty → ℂ := fun i => i.elim
  let ff : Empty → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ := fun i => i.elim
  have herr (v : AllocatedLongJetRows B U b S rowTypes) :
      ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
          (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width
            (allocatedLongJetRealCoordinates B U b S v) : ℂ) -
        ∑ k, aa k * ∏ s, ff k s (allocatedRowIdealCoordinates B U b S rowSets v s)‖ ≤
      Real.exp (slicedJointDensityLogBudget O m P) := by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact allocatedSlicedRowIdeal_normalized_cap B U b S rowSets hR hrows hB lower width
      O hO ha hδ hP haP hδP hprincipal hw hl _
  have he := allocatedProductChartDensityApproximation_error B U b S rowSets x y₀ q d period r hr hb o bW
    hperiod hM hm hR C hC hchart hbudget aa ff
    (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width)
    (Real.exp_nonneg _) herr y
  simpa only [allocatedProductChartIdealApproximation, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.sum_const_zero, sub_zero] using he

end Erdos3.VectorPolynomial

end

end OAI
