import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency
import OAI.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis
import OAI.Combinatorics.Progressions.Nilpotent.CommonProductNiltestFamily
import OAI.Combinatorics.Progressions.Nilpotent.SumNilmanifoldFactors

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def anchoredInputs {J : Type*} (j : J) : Finset (Bool ⊕ (J × Bool)) := by
  classical
  exact {Sum.inl true, Sum.inl false, Sum.inr (j, true), Sum.inr (j, false)}

theorem anchoredInputs_prod {J : Type*} (j : J) (f : (Bool ⊕ (J × Bool)) → ℂ) :
    (∏ i ∈ anchoredInputs j, f i) =
      f (.inl true) * f (.inl false) * f (.inr (j, true)) * f (.inr (j, false)) := by
  classical
  simp only [anchoredInputs, Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Sum.inl.injEq, Bool.true_eq_false, Sum.inl_ne_inr, Sum.inr.injEq,
    Prod.mk.injEq, and_false, false_or, not_false_eq_true, Finset.prod_singleton]
  ring

namespace RationalFilteredNilmanifold

variable {J σ : Type*} {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : (Bool ⊕ (J × Bool)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def anchoredReferenceData
    (P : (D (.inl true)).Niltest w) (P₀ : (D (.inl false)).Niltest w)
    (A : ∀ j, (D (.inr (j, true))).Niltest w) (B : ∀ j, (D (.inr (j, false))).Niltest w) :
    ∀ i, (D i).Niltest w
  | .inl true => P
  | .inl false => P₀
  | .inr (j, true) => A j
  | .inr (j, false) => B j

noncomputable def anchoredObservableData
    (U : J → (D (.inl true)).Niltest w) (V : J → (D (.inl false)).Niltest w)
    (A : ∀ j, (D (.inr (j, true))).Niltest w) (B : ∀ j, (D (.inr (j, false))).Niltest w)
    (j : J) : ∀ i, (D i).Niltest w
  | .inl true => U j
  | .inl false => (V j).conjugate
  | .inr (k, true) => A k
  | .inr (k, false) => B k

noncomputable def anchoredFrequencyData
    (eta : J → L (.inl true) →ₗ[ℚ] ℚ) (theta : J → L (.inl false) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (.inr (j, true)) →ₗ[ℚ] ℚ) (beta : ∀ j, L (.inr (j, false)) →ₗ[ℚ] ℚ)
    (j : J) : ∀ i, L i →ₗ[ℚ] ℚ
  | .inl true => eta j
  | .inl false => -theta j
  | .inr (k, true) => alpha k
  | .inr (k, false) => beta k

theorem anchoredObservableData_product
    (U : J → (D (.inl true)).Niltest w) (V : J → (D (.inl false)).Niltest w)
    (A : ∀ j, (D (.inr (j, true))).Niltest w) (B : ∀ j, (D (.inr (j, false))).Niltest w)
    (j : J) (x : σ → ℤ) :
    (∏ i ∈ anchoredInputs j, (anchoredObservableData U V A B j i).eval x) =
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x := by
  rw [anchoredInputs_prod]
  rfl

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def anchoredOptionInputs {J : Type*} (j : J) : Finset (Option (Option J ⊕ J)) := by
  classical
  exact {none, some (.inl none), some (.inl (some j)), some (.inr j)}

theorem anchoredOptionInputs_prod {J : Type*} (j : J) (f : Option (Option J ⊕ J) → ℂ) :
    (∏ i ∈ anchoredOptionInputs j, f i) =
      f none * f (some (.inl none)) * f (some (.inl (some j))) * f (some (.inr j)) := by
  classical
  simp [anchoredOptionInputs]; ring

namespace RationalFilteredNilmanifold

variable {J σ : Type*} {L : Option (Option J ⊕ J) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : Option (Option J ⊕ J) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def anchoredOptionReferenceData
    (P : (D none).Niltest w) (P₀ : (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w) :
    ∀ i, (D i).Niltest w
  | none => P
  | some (.inl none) => P₀
  | some (.inl (some j)) => A j
  | some (.inr j) => B j

noncomputable def anchoredOptionObservableData
    (U : J → (D none).Niltest w) (V : J → (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w)
    (j : J) : ∀ i, (D i).Niltest w
  | none => U j
  | some (.inl none) => (V j).conjugate
  | some (.inl (some k)) => A k
  | some (.inr k) => B k

noncomputable def anchoredOptionFrequencyData
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (some (.inl (some j))) →ₗ[ℚ] ℚ)
    (beta : ∀ j, L (some (.inr j)) →ₗ[ℚ] ℚ) (j : J) : ∀ i, L i →ₗ[ℚ] ℚ
  | none => eta j
  | some (.inl none) => -theta j
  | some (.inl (some k)) => alpha k
  | some (.inr k) => beta k

theorem anchoredOptionObservableData_product
    (U : J → (D none).Niltest w) (V : J → (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w)
    (j : J) (x : σ → ℤ) :
    (∏ i ∈ anchoredOptionInputs j, (anchoredOptionObservableData U V A B j i).eval x) =
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x := by
  rw [anchoredOptionInputs_prod]
  rfl

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {J σ : Type*} [Fintype J] {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : (Bool ⊕ (J × Bool)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem exists_anchored_product_family
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (P : (D (.inl true)).Niltest w) (P₀ : (D (.inl false)).Niltest w)
    (U : J → (D (.inl true)).Niltest w) (V : J → (D (.inl false)).Niltest w)
    (A : ∀ j, (D (.inr (j, true))).Niltest w) (B : ∀ j, (D (.inr (j, false))).Niltest w)
    (eta : J → L (.inl true) →ₗ[ℚ] ℚ) (theta : J → L (.inl false) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (.inr (j, true)) →ₗ[ℚ] ℚ) (beta : ∀ j, L (.inr (j, false)) →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 2 ≤ p) (hcard : (Fintype.card (Bool ⊕ (J × Bool)) : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p)
    (hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (heta : ∀ j k, rationalLogHeight (eta j ((D (.inl true)).basis k)) ≤ p)
    (htheta : ∀ j k, rationalLogHeight (theta j ((D (.inl false)).basis k)) ≤ p)
    (halpha : ∀ j k, rationalLogHeight (alpha j ((D (.inr (j, true))).basis k)) ≤ p)
    (hbeta : ∀ j k, rationalLogHeight (beta j ((D (.inr (j, false))).basis k)) ≤ p)
    (hvertU : ∀ j z, z ∈ (D (.inl true)).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (hvertV : ∀ j z, z ∈ (D (.inl false)).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (hvertA : ∀ j z, z ∈ (D (.inr (j, true))).filtration.realification.subgroup s → ∀ x,
      (A j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (alpha j) z.coord : ℝ) : CircleFourier.Circle) * (A j).observable x)
    (hvertB : ∀ j z, z ∈ (D (.inr (j, false))).filtration.realification.subgroup s → ∀ x,
      (B j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (beta j) z.coord : ℝ) : CircleFourier.Circle) * (B j).observable x) :
    ∃ (S0 : (pi D).Niltest w) (S : J → (pi D).Niltest w),
      S0.orbit = NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
        (fun i => (anchoredReferenceData P P₀ A B i).orbit) ∧
      S0.ComplexityLE (productNiltestBudget p) ∧
      ∀ j, (S j).orbit = S0.orbit ∧ (S j).normBound = 1 ∧
        (S j).ComplexityLE (productNiltestBudget p) ∧
        (∀ x, (S j).eval x = (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x) ∧
        (∀ k, rationalLogHeight (piFrequency
          (selectedOrbitFrequencies (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))
          ((pi D).basis k)) ≤ p) ∧
        (∀ z, z ∈ (pi D).filtration.realification.subgroup s → ∀ x,
          (S j).observable (z • x) = CircleFourier.character
            ((realifyFunctional (piFrequency (selectedOrbitFrequencies
              (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))) z.coord : ℝ) :
                CircleFourier.Circle) * (S j).observable x) := by
  let ref := anchoredReferenceData P P₀ A B
  let row := anchoredObservableData U V A B
  let freq := anchoredFrequencyData eta theta alpha beta
  have horbit : ∀ j i, i ∈ anchoredInputs j → (row j i).orbit = (ref i).orbit := by
    intro j i _
    rcases i with a | ⟨k, a⟩ <;> cases a
    · exact (hV j).2.1
    · exact (hU j).2.1
    · rfl
    · rfl
  have hcomp : ∀ j i, i ∈ anchoredInputs j → (row j i).ComplexityLE p := by
    intro j i _
    rcases i with a | ⟨k, a⟩ <;> cases a
    · exact (hV j).1
    · exact (hU j).1
    · exact (hB k).1
    · exact (hA k).1
  have hcap : ∀ j i, i ∈ anchoredInputs j → (row j i).normBound ≤ 1 := by
    intro j i _
    rcases i with a | ⟨k, a⟩ <;> cases a
    · exact (hV j).2.2
    · exact (hU j).2.2
    · exact (hB k).2
    · exact (hA k).2
  have hheight : ∀ j i, i ∈ anchoredInputs j → ∀ k, rationalLogHeight (freq j i ((D i).basis k)) ≤ p := by
    intro j i _ k
    rcases i with a | ⟨l, a⟩ <;> cases a
    · change rationalLogHeight ((-theta j) ((D (.inl false)).basis k)) ≤ p
      simpa [rationalLogHeight] using htheta j k
    · exact heta j k
    · exact hbeta l k
    · exact halpha l k
  have hvert : ∀ j i, i ∈ anchoredInputs j → ∀ z,
      z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (row j i).observable (z • x) = CircleFourier.character
        ((realifyFunctional (freq j i) z.coord : ℝ) : CircleFourier.Circle) * (row j i).observable x := by
    intro j i _
    rcases i with a | ⟨k, a⟩ <;> cases a
    · exact (V j).conjugate_vertical (theta j) (hvertV j)
    · exact hvertU j
    · exact hvertB k
    · exact hvertA k
  obtain ⟨S0, S, hS0, hS0c, hS⟩ := exists_common_product_niltest_family D ref row anchoredInputs freq
    hp hcard hD horbit hcomp hcap hheight hvert
  refine ⟨S0, S, hS0, hS0c, ?_⟩
  intro j
  obtain ⟨hSo, hSn, hSc, hSeval, hSheight, hSvert⟩ := hS j
  exact ⟨hSo, hSn, hSc, fun x => (hSeval x).trans (anchoredObservableData_product U V A B j x),
    hSheight, hSvert⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J)

abbrev anchoredLieSpace (L M : Fin B.count → Type u) :=
  optionLieSpace B.L (sumLieSpace (optionLieSpace B.L L) M)

abbrev anchoredDimension (d e : Fin B.count → ℕ) :=
  optionDimension B.dim (Sum.elim (optionDimension B.dim d) e)

variable {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def anchoredFactors : ∀ i : Option (Option (Fin B.count) ⊕ Fin B.count),
    RationalFilteredNilmanifold (B.anchoredLieSpace L M i) s (B.anchoredDimension d e i) :=
  optionFactors B.model (sumFactors (optionFactors B.model D) E)

theorem anchoredFactors_geometry {p : ℝ} (hqp : q ≤ p)
    (hD : ∀ j, (D j).GeometryComplexityLE p) (hE : ∀ j, (E j).GeometryComplexityLE p) :
    ∀ i, (B.anchoredFactors D E i).GeometryComplexityLE p := by
  intro i
  rcases i with _ | ((_ | j) | j)
  · exact B.geometry.mono B.model hqp
  · exact B.geometry.mono B.model hqp
  · exact hD j
  · exact hE j

def anchoredWeights (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ) :
    ∀ i, Fin (B.anchoredDimension d e i) → ℕ
  | none => w
  | some (.inl none) => w
  | some (.inl (some j)) => v j
  | some (.inr j) => v' j

theorem anchoredFactors_layers (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ)
    (hw : ∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i}))
    (hv : ∀ j k, (D j).filtration.layer k = Submodule.span ℚ ((D j).basis '' {i | k ≤ v j i}))
    (hv' : ∀ j k, (E j).filtration.layer k = Submodule.span ℚ ((E j).basis '' {i | k ≤ v' j i})) :
    ∀ i k, (B.anchoredFactors D E i).filtration.layer k =
      Submodule.span ℚ ((B.anchoredFactors D E i).basis '' {j | k ≤ B.anchoredWeights w v v' i j}) := by
  intro i k
  rcases i with _ | ((_ | j) | j)
  · exact hw k
  · exact hw k
  · exact hv j k
  · exact hv' j k

end Erdos3.PositiveShiftBasis

end

end OAI
