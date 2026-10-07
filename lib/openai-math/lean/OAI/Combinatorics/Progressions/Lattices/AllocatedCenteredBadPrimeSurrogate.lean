import OAI.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource

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
variable (inactive : LayerSamplerAxis I n → Prop) (rankC : ℝ)

private theorem singleton_prime_neZero (p : ℕ) [NeZero p] (r : ({p} : Finset ℕ)) : NeZero r.val := by
  have hr : r.val = p := Finset.mem_singleton.mp r.property
  rw [hr]
  infer_instance

private theorem singleton_prime_power_dvd (p a : ℕ) (r : ({p} : Finset ℕ)) : r.val ^ a ∣ p ^ a := by
  have hr : r.val = p := Finset.mem_singleton.mp r.property
  simp only [hr, dvd_refl]

def allocatedPhysicalPrimePowerEvent
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) (p a : ℕ) [NeZero p] : Prop :=
  letI : ∀ r : ({p} : Finset ℕ), NeZero r.val := singleton_prime_neZero p
  coefficientDeckChartEvent U bW b hb o (p ^ a)
    (allocatedChartResiduePrimePowerWitness inactive rankC {p} (fun _ => a) (p ^ a)
      (singleton_prime_power_dvd p a) (fun v => (z v : ZMod (p ^ a))))
    (affineCoefficientCoverSample U poly hm (p ^ a) (fun k x => (z (k,x) : ℝ)))

variable {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)

theorem AllocatedPhysicalRankReadCertificate.primePowerEvent_iff
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block rankC z f)
    (p a : ℕ) [NeZero p] :
    allocatedPhysicalPrimePowerEvent B U bW b hb o poly hm inactive rankC z p a ↔
      allocatedActualModulusBad inactive spatial kernel block rankC (p ^ a) f := by
  have hpa : 0 < p ^ a := pow_pos (NeZero.pos p) a
  have he := hf {p} (singleton_prime_neZero p) (fun _ => a) (p ^ a) hpa
    (singleton_prime_power_dvd p a)
  refine he.trans ?_
  constructor
  · intro h
    exact h ⟨p, Finset.mem_singleton_self p⟩
  · intro h r
    have hr : r.val = p := Finset.mem_singleton.mp r.property
    rcases r with ⟨r, hrmem⟩
    have hrp : r = p := Finset.mem_singleton.mp hrmem
    subst r
    exact h

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedPhysicalPrimePowerEvent_center_measurableSet
    {T : Type*} [MeasurableSpace T] (c : T → ∀ j, U j) (hc : Measurable c)
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (p a : ℕ) [NeZero p] :
    MeasurableSet {center | allocatedPhysicalPrimePowerEvent B U bW b hb o
      (fun j => translate (fun x => (base x : ℝ)) (subtractConstant (c center j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) _
        (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
      inactive rankC z p a} := by
  unfold allocatedPhysicalPrimePowerEvent
  exact coefficientDeckChartEvent_center_measurableSet U bW b hb o poly hm c hc base z (p ^ a) _

end Erdos3.VectorPolynomial

end

end OAI
