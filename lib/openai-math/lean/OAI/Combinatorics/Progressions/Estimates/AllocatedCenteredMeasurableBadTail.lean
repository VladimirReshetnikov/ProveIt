/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.CenteredFiniteEventSupport
import OAI.Combinatorics.Progressions.Lattices.AllocatedCenteredBadPrimeSurrogate

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
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
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (center : C → ∀ j, U j) (hcenter : Measurable center)
variable (base : Ω → X → ℤ)
variable (noise : Ω → Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (law : C → FiniteProbabilityWeights Ω)
variable (read : C → Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hcertificate : ∀ c x, 0 < (law c).weight x →
  AllocatedPhysicalRankReadCertificate B U bW b hb o
    (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
    (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
      (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
    inactive spatial kernel block rankC (noise x) (read c x))
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hcenter hcertificate in

theorem exists_allocatedCentered_badProduct_surrogate :
    ∃ test : Set (C × Ω), MeasurableSet test ∧ ∀ c x, 0 < (law c).weight x →
      (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x) ↔
      (c,x) ∈ test) := by
  let surrogate : Ω → ℕ → ℕ → C → Prop := fun x p a c =>
    if hp : p ∈ P then
      let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
      allocatedPhysicalPrimePowerEvent B U bW b hb o
        (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
        (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
          (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
        inactive rankC (noise x) p a
    else False
  have hsurrogate (x : Ω) (p : ℕ) (hp : p ∈ P) (a : ℕ) :
      MeasurableSet {c | surrogate x p a c} := by
    let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
    simp only [surrogate, dite_eq_left hp]
    exact allocatedPhysicalPrimePowerEvent_center_measurableSet B U bW b hb o poly hm
      inactive rankC center hcenter (base x) (noise x) p a
  let test : Set (C × Ω) := {z | cutoff <
    ∏ p ∈ P, p ^ largestTestedBadDepth A (surrogate z.2) p z.1}
  refine ⟨test, ?_, ?_⟩
  · apply centeredFinite_event_measurableSet
    intro x
    exact largestBadPrimeProduct_tail_measurableSet P A (surrogate x)
      (fun p hp a _ => hsurrogate x p hp a) cutoff
  · intro c x hx
    have heq : (∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a c => allocatedActualPrimeBad inactive spatial kernel block P rankC p a (read c x)) p c) =
        ∏ p ∈ P, p ^ largestTestedBadDepth A (surrogate x) p c := by
      apply largestBadPrimeProduct_congr_on_tested
      intro p hp a _ _
      let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
      simp only [surrogate, dite_eq_left hp]
      have hactual := allocatedActualPrimeBad_iff_modulusBad inactive spatial kernel block P rankC
        ⟨p,hp⟩ a (read c x)
      exact hactual.trans ((hcertificate c x hx).primePowerEvent_iff B U bW b hb o _ _
        inactive rankC spatial kernel block p a).symm
    change (cutoff < _) ↔ (cutoff < _)
    exact congrArg (fun v : ℕ => cutoff < v) heq |>.to_iff

include hcenter hcertificate in

theorem allocatedCentered_badProduct_probability_le
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    {ε : ℝ} (hbound : ∀ c, (law c).mean (fun x =>
      if cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x)
      then (1 : ℝ) else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real {z | cutoff < ∏ p ∈ P,
      p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
        p (read z.1 z.2)} ≤ ε := by
  obtain ⟨test, htest, heq⟩ := exists_allocatedCentered_badProduct_surrogate B U bW b hb o
    poly hm inactive spatial kernel block rankC center hcenter base noise law read hcertificate P A cutoff
  apply centeredFiniteProbabilityMeasure_real_event_le_of_support μ law hweight _ test htest heq
  intro c
  convert hbound c using 1
  apply congrArg (law c).mean
  funext x
  simp only [Set.mem_ofPred_eq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
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
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (center : C → ∀ j, U j) (hcenter : Measurable center)
variable (base : Ω → X → ℤ)
variable (noise : Ω → Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (law : C → FiniteProbabilityWeights Ω)
variable (read : C → Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hcertificate : ∀ c x, 0 < (law c).weight x →
  AllocatedPhysicalRankReadCertificate B U bW b hb o
    (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
    (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
      (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
    inactive spatial kernel block rankC (noise x) (read c x))
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hcenter hcertificate in

theorem exists_allocatedCentered_badProduct_measurable_tail
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    {ε : ℝ} (hbound :
      (centeredFiniteProbabilityMeasure μ law).real {z | cutoff < ∏ p ∈ P,
        p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
          p (read z.1 z.2)} ≤ ε) :
    ∃ bad : Set (C × Ω), MeasurableSet bad ∧
      (centeredFiniteProbabilityMeasure μ law).real bad ≤ ε ∧
      (∀ c x, 0 < (law c).weight x →
        (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x) ↔
        (c,x) ∈ bad)) ∧
      {z | cutoff < ∏ p ∈ P,
        p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
          p (read z.1 z.2)} =ᵐ[centeredFiniteProbabilityMeasure μ law] bad := by
  obtain ⟨bad, hbad, heq⟩ := exists_allocatedCentered_badProduct_surrogate B U bW b hb o
    poly hm inactive spatial kernel block rankC center hcenter base noise law read hcertificate P A cutoff
  have hae : {z | cutoff < ∏ p ∈ P,
      p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
        p (read z.1 z.2)} =ᵐ[centeredFiniteProbabilityMeasure μ law] bad :=
    (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
      (fun z hz => propext (heq z.1 z.2 hz))
  refine ⟨bad, hbad, ?_, heq, hae⟩
  simpa only [measureReal_def, measure_congr hae] using hbound

end Erdos3.VectorPolynomial

end

end OAI
