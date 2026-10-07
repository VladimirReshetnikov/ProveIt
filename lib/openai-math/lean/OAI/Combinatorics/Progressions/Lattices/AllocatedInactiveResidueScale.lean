import OAI.Combinatorics.Progressions.Probability.PrincipalSupportedUnitBlockLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

noncomputable def allocatedLocalResidueSources
    (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) : NormalizedScalarCubeSource α :=
  principalSupportedAxisSources B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    q hq r ⟨j, Sum.inr i⟩ hsize a v

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedLocalResidueSources_length (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    (allocatedLocalResidueSources B U b S j i q hq r hsize a v).length =
      integerAxisSideLength (j.val + 1) (basisAxisScale (b j) i) S.value
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) := by
  rw [layerIntegerPrincipalSlots_card]
  rfl

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedLocalResidueSources_primitive
    (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (allocatedLocalResidueSources B U b S j i q hq r hsize a v)
      A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  principalSupportedAxisSources_primitive B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    q hq r ⟨j, Sum.inr i⟩ hsize a v A

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedInactivePrincipalPMF
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1)) (a : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a) =
    PMF.pure (inactivePrincipalCoefficient (basisAxisScale (b j) i)
      (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card))) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ∈
      layerIntegerPrincipalSlots (G := G) B j i := (mem_principalCoefficientSlots _ _ _).mpr ⟨a, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    exact (layerIntegerPrincipalSlots_not_constant B j i) (he ▸ hmem)
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · exact integerAxisPrincipalPMF_inactive (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) i) S.positive (principalProfileSize_pos (hR j) _) (S.gap j i) hsmall
  · exact False.elim (hp hmem)

theorem allocatedInactiveResidueJetPMF_source
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1))
    (hlarge : 2 * inactiveDenominator
      (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) ≤ basisAxisScale (b j) i)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let s := allocatedLocalResidueSources B U b S j i q hq r hsize
    (weightedCubeIntegerSource s).toPMF.map (weightedCubeIntegerJetSum s rows shift) =
      allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift := by
  have hcoeff : (dependentProductPMF (fun a : B ⟨j, Sum.inr i⟩ =>
      allocatedLayerIntegerPMFs B U b hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a))) =
      PMF.pure (fun _ : B ⟨j, Sum.inr i⟩ => (1 : ℤ)) := by
    ext c
    rw [dependentProductPMF_apply]
    simp_rw [allocatedInactivePrincipalPMF B U b S j i hR hσ hsmall, inactivePrincipal_large hlarge]
    by_cases hc : c = fun _ => (1 : ℤ)
    · subst c
      simp
    · obtain ⟨a, ha⟩ : ∃ a, c a ≠ 1 := by
        by_contra hn
        apply hc
        funext a
        exact not_not.mp (fun h => hn ⟨a, h⟩)
      rw [PMF.pure_apply_of_ne _ _ hc]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (PMF.pure_apply_of_ne _ _ ha)
  unfold allocatedSupportedResidueJetPMF
  rw [hcoeff, PMF.pure_bind]
  simp only [one_mul]
  exact principalSupportedResidue_unit_block_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    q hq r ⟨j, Sum.inr i⟩ hsize hcell rows shift

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize

theorem allocatedInactiveResidueSources_scale
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height) :
    (∀ a, (∏ v, ((source a v).length : ℝ)) ≤ height) ∧
    (∀ a, (height : ℝ) ≤ ((denom : ℝ) * 2 ^ degree) * ∏ v, ((source a v).length : ℝ)) ∧
    (∀ a v, (height : ℝ) ≤ ((denom : ℝ) * 2 ^ degree) * ((source a v).length : ℝ) ^ degree) := by
  let T := inactiveSideLength degree height denom
  have hlen (a : B ⟨j, Sum.inr i⟩) (v : Fin degree) : (source a v).length = T := by
    rw [allocatedLocalResidueSources_length]
    simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false, T]
  have hprod (a : B ⟨j, Sum.inr i⟩) : (∏ v, ((source a v).length : ℝ)) = (T : ℝ) ^ degree := by
    simp only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hu : T ^ degree ≤ height :=
    (inactiveSideLength_power (Nat.zero_lt_succ _) hlarge).trans (Nat.div_le_self _ _)
  have hl : height ≤ denom * 2 ^ degree * T ^ degree :=
    (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hprod]
    exact_mod_cast hu
  · intro a
    rw [hprod]
    exact_mod_cast hl
  · intro a v
    rw [hlen]
    exact_mod_cast hl

end Erdos3.VectorPolynomial

end

end OAI
