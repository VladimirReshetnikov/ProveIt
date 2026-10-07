import OAI.Combinatorics.Progressions.Estimates.AllocatedActivePlateauAverage

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets

noncomputable def allocatedActiveRowsOfMixed
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (a : activeAxes) : CoefficientJetAxisRow O a.val.val := (split z).1 a.val

omit [Fintype α] [DecidableEq α] in
theorem allocatedActiveRowsOfMixed_integer
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) (a : activeAxes) :
    allocatedGridIntegerValues B U b S rowSets a.val
        (allocatedActiveRowsOfMixed B U b S rowSets z a) = (z (ig a.val).1).2 (ig a.val).2 := by
  rcases a with ⟨⟨⟨j, i | i⟩, ha⟩, hactive⟩
  · exact False.elim ha
  · rfl

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

omit [∀ j, Fintype (E j)] in
theorem allocatedActiveSiteValues_mixed (z : MixedCoveredJetSource I O E n d)
    (s : Finset α) (a : activeAxes) :
    allocatedActiveSiteValues B U b S rowSets
        (allocatedActiveRowsOfMixed B U b S rowSets z.1) s a =
      ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 () := by
  rw [mixedCoveredRowsSiteValue_integer]
  unfold allocatedActiveSiteValues
  rw [allocatedActiveRowsOfMixed_integer]

omit [∀ j, Fintype (E j)] in
theorem allocatedActiveSiteApproximation_mixed
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d) :
    allocatedActiveSiteApproximation B U b S rowSets e
        (allocatedActiveRowsOfMixed B U b S rowSets z.1) =
      siteFamilyEval e
        (fun s a => ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 ())
        (fun s a => (((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 () : ℝ) /
          allocatedGridNaturalScale B U b S a.val) := by
  have hy : allocatedActiveSiteValues B U b S rowSets
      (allocatedActiveRowsOfMixed B U b S rowSets z.1) =
      fun s a => ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a.val).1).2 (ig a.val).2 () := by
    funext s a
    exact allocatedActiveSiteValues_mixed B U b S rowSets d z s a
  unfold allocatedActiveSiteApproximation
  rw [hy]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell

noncomputable def allocatedActiveSiteChartPrefactor (z : MixedCoveredJetSource I O E n d) : ℂ :=
  ((∏ a : {a : {a // grid a} // ¬active a}, (laws a.val ((split z.1).1 a.val)).toReal : ℝ) : ℂ) /
    (volumeN : ℂ) * (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)

theorem allocatedActiveSiteProfile_mixed
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))) :
    allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e (chart z) =
      allocatedActiveSiteChartPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z *
        allocatedActiveSiteApproximation B U b S rowSets e
          (allocatedActiveRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedActiveSiteProfile, allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz]
  unfold allocatedSelectedGridExtension selectedProductExtension allocatedActiveSiteChartPrefactor
    allocatedActiveRowsOfMixed
  ring

end Erdos3.VectorPolynomial

end

end OAI
