import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)

noncomputable def allocatedActiveSiteValues
    (z : (a : activeAxes) → CoefficientJetAxisRow (rowTypes) a.val.val)
    (s : Finset α) (a : activeAxes) : ℤ :=
  integerBooleanSitesFromRows (rowSets (ig a.val).1)
    (allocatedGridIntegerValues B U b S rowSets a.val (z a)) s

noncomputable def allocatedActiveSiteApproximation
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : (a : activeAxes) → CoefficientJetAxisRow (rowTypes) a.val.val) : ℂ :=
  siteFamilyEval e (allocatedActiveSiteValues B U b S rowSets z)
    (fun s a => (allocatedActiveSiteValues B U b S rowSets z s a : ℝ) / axisN a.val)

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedActiveSiteApproximation_zero
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (he : ∀ a i s r v, (siteH) a ≤ |v| → (e a).factor i s r v = 0)
    (z : (a : activeAxes) → CoefficientJetAxisRow (rowTypes) a.val.val)
    (hz : ∃ a, z a ∉ allocatedGridSiteWindow B rowSets U b S a.val) :
    allocatedActiveSiteApproximation B U b S rowSets e z = 0 := by
  obtain ⟨a, ha⟩ := hz
  rw [allocatedActiveSiteApproximation, siteFamilyEval_eq]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  have hH : 0 ≤ (siteH) a := by
    have h := allocatedNaturalSiteRadius_nonneg (G := G) B (ig a.val).1 (ig a.val).2 (rowSets (ig a.val).1)
    linarith
  exact reconstructedSiteEval_zero_off_window (rowSets (ig a.val).1) (e a)
    (allocatedGridNaturalScale_pos B U b hR S a.val) (hrows _) hH
    (allocatedSiteCoefficientRadius_sites (G := G) B rowSets (ig a.val)) (he a)
    (allocatedGridIntegerValues B U b S rowSets a.val (z a))
    (fun h => ha ((allocatedGridSiteWindow_integer B rowSets U b S a.val (z a)).mpr h))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell

include hq hsize in
theorem allocatedActiveGridMass_zero_off_site_window
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (z : (a : activeAxes) → CoefficientJetAxisRow (rowTypes) a.val.val)
    (hz : ∃ a, z a ∉ allocatedGridSiteWindow B rowSets U b S a.val) :
    (∏ a, (laws a.val (z a)).toReal) = 0 := by
  obtain ⟨a, ha⟩ := hz
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  rw [allocatedSupportedGridJetPMF_integer B U b hR hσ S rowSets x q r hcell]
  have hout : ¬∀ t, |(allocatedGridIntegerValues B U b S rowSets a.val (z a) t : ℝ)| ≤
      allocatedNaturalSupportRadius (G := G) B α (ig a.val).1 (ig a.val).2 * axisN a.val := by
    intro ht
    apply ha
    apply allocatedGridSiteWindow_mem B rowSets U b S a.val (z a)
    intro t
    exact (ht t).trans (mul_le_mul_of_nonneg_right
      (allocatedSiteCoefficientRadius_physical (G := G) B rowSets (ig a.val)) (Nat.cast_nonneg _))
  rw [allocatedNaturalPhysicalPoint_zero_off_window B U b hR hσ S (ig a.val).1 (ig a.val).2
    a.property q r hq hsize hcell (allocatedGridIntegerAxis_grid B U b S a.val)
    (rowSets (ig a.val).1) (hrows _) x _ hout, ENNReal.toReal_zero]

end Erdos3.VectorPolynomial

end

end OAI
