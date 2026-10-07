import OAI.Combinatorics.Progressions.Lattices.CoefficientIntegerFloorRemainder
import OAI.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
import OAI.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
import OAI.Combinatorics.Progressions.Sampling.PreparedLayerScore

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_polynomial_bound (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x : LayerSamplerVariables G I n B → ℝ) (hx : ∀ v, |x v| ≤ layerSamplerBox B U b S v)
    (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i| ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  have hc (k : I j) : |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val (a.1 k))| ≤ R j :=
    (continuousPolynomialDensity_box Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j)
      (hs.1 k) x hx).trans (by linarith [hR j])
  have hz (k : Fin (n j)) :
      |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val
        (fun d => (a.2 k d : ℝ) / basisAxisScale (b j) k))| ≤ R j := by
    exact (allocatedIntegerPolynomial_box (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl (hσ1 j)
      (layerSamplerSides_integer_principal B U b R S.value j k) (a.2 k) (hs.2 k) x hx).trans
        (by linarith [hR j])
  have hnorm := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j)
    (hC j) (hR j).le (hchart j) _ _ hc hz
  have hi := PiLp.norm_apply_le
    (mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x) i
  simpa only [Real.norm_eq_abs] using hi.trans hnorm

theorem allocatedAffineDensity_small_integer_remainder
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (center : ∀ j, U j)
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ)
    (hframe : allocatedAffineDensity B U b hb o hR hσ S p hm center frame ≠ 0) :
    ∃ β : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℤ,
      (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      ∀ (x : LayerSamplerVariables G I n B → ℝ), (∀ v, |x v| ≤ layerSamplerBox B U b S v) →
        ∀ j i,
          |eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i - (center j).val i -
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤
              C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  obtain ⟨a, ha, _⟩ := allocatedCoefficientDensity_recover B U b hb o hR hσ S
    hσ1 C hC hchart hsmall hframe
  obtain ⟨β, hβ⟩ := canonicalCoefficientSample_polynomial_remainder U b hb o a
    (centeredAffineCoefficientArray U p hm center frame) ha.1.1
  refine ⟨β, fun j i => (hβ j i).2, ?_⟩
  intro x hx j i
  rw [← coefficientRowPolynomial_centered_affine_eval U p hm hp center frame j i x,
    (hβ j i).1, map_add, add_sub_cancel_right, mixedLiftPolynomial_eval]
  exact allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart j (a j)
    (ha.1.2 j).2 x hx i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators TensorProduct

variable {X G : Type} [Fintype G] {s D E m : ℕ}
variable {A : PolynomialPatch X s (D + E)}
variable (L : RankPreparationFamily X (Fin D) m)
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (L j).space)ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (L j).space))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B (fun j => (L j).space) b R σ)

theorem allocated_prepared_freezing
    (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (hdeg : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L j).poly)
    (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space))
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (center : ∀ j, (L j).space)
    (frame : Option (LayerSamplerVariables G I n B) → X → ℤ)
    (hframe : allocatedAffineDensity B (fun j => (L j).space) b hb o hR hσ S
      (fun j => (L j).poly) hmem center (fun k v => (frame k v : ℝ)) ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (LayerSamplerVariables G I n B → ℝ))
    (hinteger : ∀ x ∈ Ω, ∃ z : LayerSamplerVariables G I n B → ℤ, x = fun i => (z i : ℝ))
    (hbox : ∀ x ∈ Ω, ∀ v, |x v| ≤ layerSamplerBox B (fun j => (L j).space) b S v)
    (herr : ∀ x ∈ Ω, ∀ i,
      |VectorPolynomial.eval (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
        err i| ≤ δ)
    (x₀ : LayerSamplerVariables G I n B → ℝ) (hx₀ : x₀ ∈ Ω) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots
      (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x₀ k)).residual bref) ≠ 0)
    (hbudget : (D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)) < 1 / 12) :
    ∃ A' : PolynomialPatch (LayerSamplerVariables G I n B) s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      ∀ x ∈ Ω, dist (A.value
          (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)) (A'.value x) ≤
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
          (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ))) := by
  obtain ⟨β, hβ, hrem⟩ := allocatedAffineDensity_small_integer_remainder B (fun j => (L j).space)
    b o hR hσ S hσ1 C hC hchart hb hsmall (fun j => (L j).poly) hmem hdeg center
    (fun k v => (frame k v : ℝ)) hframe
  apply F.exists_freeze_prepared_affine L ip hip c err hprepare frame β hβ (fun j => (center j).val)
    (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * R j))
    (fun j => mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le))
    hδ Ω hinteger (fun x hx => hrem x (hbox x hx)) herr x₀ hx₀ bref href hbudget

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

def AllocatedCenteredFramedRecoveredSampleAt
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (s : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  allocatedReadNoise f = (fun t => jointIntegerFrame (a,v) t.1 t.2) ∧
  canonicalCoefficientSample U b hb o s =
    affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
      (fun k x => (jointIntegerFrame (a,v) k x : ℝ)) ∧
  (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (s j) ∧
    mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (s j)) ∧
  (∀ d, |coefficientSamplerAmbientPoint U b o s d| < 1/2) ∧
  (∀ (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
    allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (s j).2 i e)

theorem allocatedCentered_recovered_sample_ae
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
      (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
      (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) a (sample center a) (read center a)) :
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center)
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
      columnResiduePattern stride z.2.2.val ∈ cells ∧
      0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hm z.1 z.2.1.val z.2.2.val ∧
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val)
        (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  intro law
  have hweight : ∀ x, Measurable (fun center => (law center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD
  apply (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
  intro z hz
  have hs := selectedJointFiniteLaw_support bases hbases stride cells width hwidth hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm z.1)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm z.1) (hD z.1) z.2 hz
  have hf := (hread z.1 z.2.1.val).jointFrame B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z.2.2.val
  exact ⟨hs.1, hs.2, hf.1, hf.2.2.2 hs.2.ne'⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem AllocatedCenteredFramedRecoveredSampleAt.freezing_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      c a v sample read) :
    ∃ β : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℤ,
      (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      (∀ x : LayerSamplerVariables G I n B → ℝ, ∀ j i,
        eval (fun z => (jointIntegerFrame (a,v) none z : ℝ) +
          ∑ k, (jointIntegerFrame (a,v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i =
        mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
          (sample j).1 (sample j).2 x i +
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i))) ∧
      ∀ x : LayerSamplerVariables G I n B → ℝ,
        (∀ k, |x k| ≤ layerSamplerBox B U b S k) → ∀ j i,
        |eval (fun z => (jointIntegerFrame (a,v) none z : ℝ) +
          ∑ k, (jointIntegerFrame (a,v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i -
          MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤
            C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a,v) k z : ℝ)
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  let β := coefficientIntegerFloorPolynomial U b o sample
    (centeredAffineCoefficientArray U poly hm c frame)
  have hβ := canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample
    (centeredAffineCoefficientArray U poly hm c frame) hc
  have heval (x : LayerSamplerVariables G I n B → ℝ) (j : Fin m) (i : J j) :
      eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i - (c j).val i =
        mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
          (sample j).1 (sample j).2 x i +
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i)) := by
    rw [← coefficientRowPolynomial_centered_affine_eval U poly hm hp c frame j i x,
      (hβ j i).1, map_add, mixedLiftPolynomial_eval]
  refine ⟨β, fun j i => (hβ j i).2, heval, ?_⟩
  intro x hx j i
  change |eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i -
    (c j).val i - _| ≤ _
  rw [heval, add_sub_cancel_right]
  exact allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart j
    (sample j) (h.2.2.1 j).2 x hx i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

instance coefficientTorus_zeroLayer_subsingleton {K : Type*} {J : Fin 0 → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Subsingleton (CoefficientTorus (K := K) U) where
  allEq x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    change QuotientAddGroup.mk' (coefficientIntegerLattice U) c =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) d
    apply congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    funext t
    exact Fin.elim0 t.1

variable {G X : Type*} {I E J : Fin 0 → Type*} {n : Fin 0 → ℕ}
variable (B : LayerSamplerAxis I n → Type*)

def allocatedZeroLayerFramedRead (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ
  | .inl t => jointIntegerFrame (a, v) t.1 t.2
  | .inr (.inl ⟨j, _, _⟩) => Fin.elim0 j
  | .inr (.inr ⟨⟨j, _⟩, _⟩) => Fin.elim0 j

@[simp] theorem allocatedZeroLayerFramedRead_noise (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedZeroLayerFramedRead (E := E) B a v) =
      fun t => jointIntegerFrame (a, v) t.1 t.2 := rfl

def allocatedZeroLayerSample :
    CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n :=
  fun j => Fin.elim0 j

variable [Fintype G]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

def allocatedZeroLayerCenterLift : ∀ j, U j := fun j => Fin.elim0 j

omit [∀ j, Fintype (J j)] in
theorem allocatedZeroLayerCenterLift_spec
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => allocatedZeroLayerCenterLift U s.1))) := by
  exact Subsingleton.elim _ _

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedZeroLayer_recovered_sample
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      c a v sample (allocatedZeroLayerFramedRead (E := E) B a v) := by
  refine ⟨rfl, Subsingleton.elim _ _, ?_, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro d
    exact Fin.elim0 d.1.1
  · intro j
    exact Fin.elim0 j

theorem allocatedZeroLayer_recovered
    (a : X → ℤ) (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      (allocatedZeroLayerCenterLift U) a v (allocatedZeroLayerSample B)
      (allocatedZeroLayerFramedRead (E := E) B a v) :=
  allocatedZeroLayer_recovered_sample B U b hb o S hR hσ poly hm _ _ _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m)
variable {I Deck : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

omit [Fintype X] [∀ j, Fintype (Deck j)] in

theorem exists_freeze_allocated_recovered_sample
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (a : X → ℤ) (v : Option Vars × X → ℤ)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L j).poly) hm c a v sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (parentDomain : Set (X → ℤ))
    (herr : ∀ x ∈ parentDomain, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    (hbudget : (D : ℝ) * (2 * ((∑ j, (Fintype.card (L j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)) < 1 / 12)
    (hscoreBudget : A.kernel.lip * ((D : ℝ) * (2 *
      ((∑ j, (Fintype.card (L j).Coord : ℝ) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ))) ≤ gain / 16)
    {Ω : Type} [Fintype Ω] (t : Ω → Vars → ℤ)
    (hbox : ∀ u k, |(t u k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hinside : ∀ u, integerAffineMap (fun x k => jointIntegerFrame (a,v) (some k) x)
      (jointIntegerFrame (a,v) none) (t u) ∈ parentDomain)
    (score : Ω → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (a,v) (some k) x)
        (jointIntegerFrame (a,v) none) (t u) x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (t u k : ℝ)) := by
  let frame := jointIntegerFrame (a,v)
  let point : Ω → X → ℝ := fun u x =>
    (frame none x : ℝ) + ∑ k, (frame (some k) x : ℝ) * (t u k : ℝ)
  have hscore' : gain / 2 ≤ 𝔼 u, score u * A.value (point u) := by
    simpa only [point, frame, integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using hscore
  obtain ⟨β, hβ, _, hsmall⟩ := hread.freezing_lifts B U b hb o S hR hσ
    (fun j => (L j).poly) hm hσ1 C hC hchart hp c a v sample read
  let ε : Fin m → ℝ := fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * R j)
  have hε : ∀ j, 0 ≤ ε j := by
    intro j
    exact mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  let domain : Set (Vars → ℝ) := Set.range (fun u k => (t u k : ℝ))
  obtain ⟨u₀, bref, href⟩ := A.exists_contributing_site_of_pos_score point score
    ((half_pos hgain).trans_le hscore')
  let : Nonempty Ω := ⟨u₀⟩
  obtain ⟨A', hLip, hweight, hclose⟩ := F.exists_freeze_prepared_affine L ip hip c₀ err
    hprepare frame β hβ (fun j => (c j).val) ε hε hδ domain
    (by rintro x ⟨u, rfl⟩; exact ⟨t u, rfl⟩)
    (by rintro x ⟨u, rfl⟩; exact hsmall _ (hbox u))
    (by
      rintro x ⟨u, rfl⟩ i
      simpa only [frame, integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using
        herr _ (hinside u) i)
    (fun k => (t u₀ k : ℝ)) ⟨u₀, rfl⟩ bref href hbudget
  refine ⟨A', hLip, hweight, ?_⟩
  have hcompare : (𝔼 u, score u * A.value (point u)) ≤
      (𝔼 u, score u * A'.value (fun k => (t u k : ℝ))) + gain / 16 := by
    calc
      _ ≤ 𝔼 u, (score u * A'.value (fun k => (t u k : ℝ)) + gain / 16) := by
        apply Finset.expect_le_expect
        intro u _
        exact unit_weight_score_error (hscoreBound u)
          ((hclose _ ⟨u, rfl⟩).trans hscoreBudget)
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  linarith

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
