/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.SampledNativeModel
import OAI.Combinatorics.Progressions.Nilpotent.NiltestOrbitOne

namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def selectedOrbitFactors (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) (i : ι) : (D i).Niltest w := by
  classical
  exact if i ∈ active then T i else (base i).oneOnOrbit

noncomputable def selectedOrbitFrequencies (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (active : Finset ι) (i : ι) : L i →ₗ[ℚ] ℚ := by
  classical
  exact if i ∈ active then eta i else 0

theorem selectedOrbitFactors_orbit (base T : ∀ i, (D i).Niltest w) (active : Finset ι)
    (horbit : ∀ i ∈ active, (T i).orbit = (base i).orbit) (i : ι) :
    (selectedOrbitFactors base T active i).orbit = (base i).orbit := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using horbit i hi
  · simp only [selectedOrbitFactors, hi, ite_false, Niltest.oneOnOrbit_orbit]

theorem selectedOrbitFactors_eval [Fintype ι] (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) (x : σ → ℤ) :
    (∏ i, (selectedOrbitFactors base T active i).eval x) = ∏ i ∈ active, (T i).eval x := by
  classical
  have heval (i : ι) : (selectedOrbitFactors base T active i).eval x =
      if i ∈ active then (T i).eval x else 1 := by
    by_cases hi : i ∈ active <;>
      simp only [selectedOrbitFactors, hi, ite_true, ite_false, Niltest.oneOnOrbit_eval]
  simp only [heval, Finset.prod_ite_mem_eq]

theorem selectedOrbitFactors_normBound (base T : ∀ i, (D i).Niltest w) (active : Finset ι)
    (hcap : ∀ i ∈ active, (T i).normBound ≤ 1) (i : ι) :
    (selectedOrbitFactors base T active i).normBound ≤ 1 := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using hcap i hi
  · simp only [selectedOrbitFactors, hi, ite_false, Niltest.oneOnOrbit, le_refl]

theorem selectedOrbitFactors_complexity (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) {p : ℝ} (hp : 2 ≤ p) (hD : ∀ i, (D i).GeometryComplexityLE p)
    (hT : ∀ i ∈ active, (T i).ComplexityLE p) (i : ι) :
    (selectedOrbitFactors base T active i).ComplexityLE p := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using hT i hi
  · simpa only [selectedOrbitFactors, hi, ite_false] using
      (base i).oneOnOrbit_complexity hp (hD i)

omit [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)] in
theorem selectedOrbitFrequencies_logHeight (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (active : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hheight : ∀ i ∈ active, ∀ k, rationalLogHeight (eta i ((D i).basis k)) ≤ p)
    (i : ι) (k : Fin (d i)) :
    rationalLogHeight (selectedOrbitFrequencies eta active i ((D i).basis k)) ≤ p := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFrequencies, hi, ite_true] using hheight i hi k
  · simpa [selectedOrbitFrequencies, hi, rationalLogHeight] using hp

theorem selectedOrbitFactors_vertical (base T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) (active : Finset ι)
    (hvert : ∀ i ∈ active, ∀ z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (i : ι) (z : (D i).RealGroup) (hz : z ∈ (D i).filtration.realification.subgroup s)
    (x : (D i).Space) :
    (selectedOrbitFactors base T active i).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (selectedOrbitFrequencies eta active i) z.coord : ℝ) : CircleFourier.Circle) *
          (selectedOrbitFactors base T active i).observable x := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, selectedOrbitFrequencies, hi, ite_true] using hvert i hi z hz x
  · simpa only [selectedOrbitFactors, selectedOrbitFrequencies, hi, ite_false] using
      (base i).oneOnOrbit_vertical z x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleModelFamily {ι σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (g : ι → X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : ι → model.Niltest w
  norm : ∀ i, (test i).normBound ≤ 1
  complexity : ∀ i, (test i).ComplexityLE p
  eval : ∀ i x, g i x = (test i).eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

namespace NativeSampleModelFamily

variable {ι σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {g : ι → X → ℂ}

def toSampleModel (V : NativeSampleModelFamily w degree p sample g) (i : ι) :
    NativeSampleModel w degree p sample (g i) where
  L := V.L
  dim := V.dim
  model := V.model
  test := V.test i
  norm := V.norm i
  complexity := V.complexity i
  eval := V.eval i

noncomputable def mono (V : NativeSampleModelFamily w degree p sample g)
    {q : ℝ} (hpq : p ≤ q) : NativeSampleModelFamily w degree q sample g :=
  { V with complexity := fun i => (V.complexity i).mono hpq }

noncomputable def ofModels {ι : Type} [Fintype ι] {g : ι → X → ℂ}
    (V : ∀ i, NativeSampleModel w degree p sample (g i))
    (hp : 2 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) :
    NativeSampleModelFamily w degree (productNiltestBudget p) sample g := by
  classical
  let D := fun i => (V i).model
  let base := fun i => (V i).test
  let : FiniteDimensional ℚ (∀ i, (V i).L) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, (V i).L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, (V i).L)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, (V i).L)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let factors := fun j => RationalFilteredNilmanifold.selectedOrbitFactors base base {j}
  have hD : ∀ i, (D i).GeometryComplexityLE p := fun i => (V i).complexity.1
  have hcomp : ∀ j i, (factors j i).ComplexityLE p := fun j =>
    RationalFilteredNilmanifold.selectedOrbitFactors_complexity base base {j} hp hD
      (fun i _ => (V i).complexity)
  have hcap : ∀ j i, (factors j i).normBound ≤ 1 := fun j =>
    RationalFilteredNilmanifold.selectedOrbitFactors_normBound base base {j}
      (fun i _ => (V i).norm)
  have hp0 : 0 ≤ p := by linarith
  let tests := fun j => RationalFilteredNilmanifold.unitBoundedPiNiltest
    D (factors j) hp0 hι (hcomp j) (hcap j)
  refine {
    L := ∀ i, (V i).L
    dim := Fintype.card (Σ i, Fin (V i).dim)
    model := RationalFilteredNilmanifold.pi D
    test := tests
    norm := fun _ => le_rfl
    complexity := fun j => RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
      D (factors j) hp0 hι (hcomp j) (hcap j)
    eval := ?_ }
  intro j x
  change g j x = (RationalFilteredNilmanifold.unitBoundedPiNiltest
    D (factors j) hp0 hι (hcomp j) (hcap j)).eval (sample x)
  rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval]
  change g j x = ∏ i, (RationalFilteredNilmanifold.selectedOrbitFactors base base {j} i).eval
    (sample x)
  rw [RationalFilteredNilmanifold.selectedOrbitFactors_eval]
  simpa only [Finset.prod_singleton] using (V j).eval x

end NativeSampleModelFamily

end Erdos3

end

end OAI
