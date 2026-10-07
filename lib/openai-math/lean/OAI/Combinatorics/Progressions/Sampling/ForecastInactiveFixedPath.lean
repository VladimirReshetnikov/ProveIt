import OAI.Combinatorics.Progressions.Lattices.AllocatedInactiveResidueScale
import OAI.Combinatorics.Progressions.Linear.ContainedSupportedProgressionKernels

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem forecastInactiveFixedPath_law (j : Fin m) (i : Fin (n j))
    (hsmall : basisAxisScale (basis j) i ≤ S.value ^ (j.val + 1))
    (c : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hc : ∀ d, c d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : G → IntegerScalarCubeBox α S.value) (rows : Finset (Finset α)) :
    (conditioned).toPMF.map (fun y =>
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α)) *ᵥ c) =
      allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows
        (fun t => booleanCoefficient (fun _ : Finset α => c (constantCoefficientSlot _ _)) t) := by
  have hdet := (allocatedLayerInteger_inactive_structure B U basis hR hσ S j i hsmall c hc).2
  let pc (b : B ⟨j, Sum.inr i⟩) :=
    c (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)
  have hprincipal (b : B ⟨j, Sum.inr i⟩) :
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        PMF.pure (pc b) := by
    rw [allocatedInactivePrincipalPMF B U basis S j i hR hσ hsmall]
    congr 1
    exact (hdet _ ((mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩)).symm
  have hcoeff : (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))) =
      PMF.pure pc := by
    ext a
    rw [dependentProductPMF_apply]
    simp_rw [hprincipal]
    by_cases ha : a = pc
    · subst a
      simp
    · obtain ⟨b, hb⟩ : ∃ b, a b ≠ pc b := by
        by_contra hn
        apply ha
        funext b
        exact not_not.mp (fun h => hn ⟨b, h⟩)
      rw [PMF.pure_apply_of_ne _ _ ha]
      exact Finset.prod_eq_zero (Finset.mem_univ b) (PMF.pure_apply_of_ne _ _ hb)
  have hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1) :=
    hsmall.trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree j).trans (Nat.le_succ _)))
  unfold allocatedSupportedResidueJetPMF
  rw [hcoeff, PMF.pure_bind]
  apply congrArg (fun f => (conditioned).toPMF.map f)
  funext y t
  simpa only [Pi.add_apply, Finset.sum_apply, pc] using
    allocatedPhysicalGridJet_blocks B U basis hR hσ S j i hmoderate c hc x y
      (fun t : rows => (t : Finset α)) t

theorem forecastInactiveFixedPath_joint_law
    {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox α S.value) (rows : A → Finset (Finset α)) :
    (conditioned).toPMF.map (fun y a =>
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
        (fun t : rows a => (t : Finset α)) *ᵥ c a) =
      dependentProductPMF (fun a =>
        allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell
          (selected a).1 (selected a).2 (rows a)
          (fun t => booleanCoefficient (fun _ : Finset α => c a (constantCoefficientSlot _ _)) t)) := by
  let e (a : A) : LayerSamplerAxis I n := ⟨(selected a).1, Sum.inr (selected a).2⟩
  have he : Function.Injective e := by
    have hi : Function.Injective (fun z : (Σ j : Fin m, Fin (n j)) =>
        (⟨z.1, Sum.inr z.2⟩ : LayerSamplerAxis I n)) := by
      rintro ⟨j, i⟩ ⟨k, l⟩ h
      have hj : j = k := congrArg Sigma.fst h
      subst k
      have hsum : (Sum.inr i : I j ⊕ Fin (n j)) = Sum.inr l :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hl : i = l := Sum.inr.inj hsum
      subst l
      rfl
    exact hi.comp hselected
  let out (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) : rows a → ℤ :=
    boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)) *ᵥ c a
  let k (a : A) (y : ∀ b : B (e a), ∀ v : Fin (layerSamplerDegree I n (e a)),
      IntegerScalarCubeBox α (allocatedPrincipalSides B U basis S ⟨e a, b, v⟩)) : PMF (rows a → ℤ) :=
    PMF.pure (fun t => booleanCoefficient (fun _ : Finset α => c a (constantCoefficientSlot _ _)) t +
      ∑ b, c a (principalCoefficientSlot (G := G) (layerSamplerDegree I n) (e a) b) *
        integerBooleanBlockJet (fun v i => (y b v i : ℤ)) t)
  have hpoint (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) :
      k a (fun b v => y ⟨e a, b, v⟩) = PMF.pure (out a y) := by
    apply congrArg PMF.pure
    funext t
    have hmoderate := (hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
    exact (allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
      hmoderate (c a) (hc a) x y (fun t : rows a => (t : Finset α)) t).symm
  have hpure (z : ∀ a, rows a → ℤ) :
      dependentProductPMF (fun a => PMF.pure (z a)) = PMF.pure z := by
    ext z'
    rw [dependentProductPMF_apply]
    by_cases hz : z' = z
    · subst z'
      simp
    · obtain ⟨a, ha⟩ : ∃ a, z' a ≠ z a := by
        by_contra hn
        apply hz
        funext a
        exact not_not.mp (fun h => hn ⟨a, h⟩)
      rw [PMF.pure_apply_of_ne _ _ hz]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (PMF.pure_apply_of_ne _ _ ha)
  have hj := principalSupportedResidue_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    q r hcell e he k
  simp_rw [hpoint, hpure] at hj
  change (conditioned).toPMF.map (fun y a => out a y) =
    dependentProductPMF (fun a => (conditioned).toPMF.map (out a)) at hj
  refine hj.trans ?_
  apply congrArg dependentProductPMF
  funext a
  exact forecastInactiveFixedPath_law B U basis hR hσ S q r hcell
    (selected a).1 (selected a).2 (hsmall a) (c a) (hc a) x (rows a)

end Erdos3.VectorPolynomial

end

end OAI
