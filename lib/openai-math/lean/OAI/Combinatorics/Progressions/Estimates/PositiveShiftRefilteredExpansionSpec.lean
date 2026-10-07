/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
import OAI.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion

namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J) {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))
  (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
  (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
  (anchor : ZMod N) (H : Finset (ZMod N)) (p : ℝ)

structure CommonFactorization where
  weight : ∀ i, Fin (B.anchoredDimension d e i) → ℕ
  adapted : ∀ i k, (B.anchoredFactors D E i).filtration.layer k =
    Submodule.span ℚ ((B.anchoredFactors D E i).basis '' {j | k ≤ weight i j})
  subalgebra : LieSubalgebra ℚ (pi (B.anchoredFactors D E)).filtration.AssociatedGraded
  spanning : Fin (Fintype.card (Σ i, Fin (B.anchoredDimension d e i))) →
    (pi (B.anchoredFactors D E)).filtration.AssociatedGraded
  span_eq : Submodule.span ℚ (Set.range spanning) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (B.anchoredFactors D E)).filtration.associatedGradedBasis (pi (B.anchoredFactors D E)).basis
      (productBasisWeight weight) (pi_layer_span (B.anchoredFactors D E) weight adapted))
    (productBasisWeight weight) subalgebra.toSubmodule
  height : ∀ i k, rationalLogHeight
    (((pi (B.anchoredFactors D E)).filtration.associatedGradedBasis (pi (B.anchoredFactors D E)).basis
      (productBasisWeight weight) (pi_layer_span (B.anchoredFactors D E) weight adapted)).repr (spanning i) k) ≤ p
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  shifts : Finset (ZMod N)
  shifts_sub : shifts ⊆ H
  shifts_nonempty : shifts.Nonempty
  shifts_large : Real.exp (-p) * N ≤ (shifts.card : ℝ)
  factors : ∀ h ∈ shifts, HasFixedProductOrbitFactors (B.anchoredFactors D E) none
    (fun i => (anchoredOptionReferenceData (B.test h) (B.test anchor) A (R h) i).orbit)
    (B.frequency h) (fun _ : Unit => (N : ℝ)) p denominator subalgebra
  frequency : ({h // h ∈ shifts} × Fin B.count) → ∀ i, B.anchoredLieSpace L M i →ₗ[ℚ] ℚ
  frequency_zero : ∀ j x,
    x ∈ (pi (B.anchoredFactors D E)).filtration.realGradedRefiltrationLayer subalgebra s →
      realifyFunctional (piFrequency (frequency j)) x = 0
  invariant : ∀ h ∈ shifts, ∀ z : B.model.RealGroup,
    z ∈ B.model.filtration.realification.subgroup s →
    (∀ j, realifyFunctional (frequency j none) z.coord = 0) → ∀ x,
      (B.test h).observable (z • x) = (B.test h).observable x

variable {B D E A R anchor H p}

def CommonFactorization.mono (F : B.CommonFactorization D E A R anchor H p) {p' : ℝ} (hpp' : p ≤ p') :
    B.CommonFactorization D E A R anchor H p' where
  weight := F.weight
  adapted := F.adapted
  subalgebra := F.subalgebra
  spanning := F.spanning
  span_eq := F.span_eq
  graded := F.graded
  height := fun i k => (F.height i k).trans hpp'
  denominator := F.denominator
  denominator_pos := F.denominator_pos
  denominator_bound := F.denominator_bound.trans (Real.exp_le_exp.mpr hpp')
  shifts := F.shifts
  shifts_sub := F.shifts_sub
  shifts_nonempty := F.shifts_nonempty
  shifts_large := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpp'))
    (Nat.cast_nonneg N)).trans F.shifts_large
  factors := fun h hh => (F.factors h hh).mono (B.anchoredFactors D E) none hpp'
    (fun _ => by exact_mod_cast NeZero.pos N)
  frequency := F.frequency
  frequency_zero := F.frequency_zero
  invariant := F.invariant

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  {B : PositiveShiftBasis.{u} s N q a J} {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  {D : ∀ j, RationalFilteredNilmanifold (L j) s (d j)}
  {E : ∀ j, RationalFilteredNilmanifold (M j) s (e j)}
  {A : ∀ j, (D j).Niltest (fun _ : Unit => 1)}
  {R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1)}
  {anchor : ZMod N} {H : Finset (ZMod N)} {p : ℝ}

def CommonFactorization.FactorFamily
    (F : B.CommonFactorization D E A R anchor H p) : Prop :=
    let T := B.anchoredFactors D E
    let g (h : ZMod N) : ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
      fun i => (anchoredOptionReferenceData (D := T) (B.test h) (B.test anchor) A (R h) i).orbit
    ∃ (κ : ZMod N → (pi T).RealGroup)
      (slow middle rat : ZMod N → ((pi T).filtration.realification.adaptedPolynomialFiltration
        (fun _ : Unit => 1)).Group),
      (∀ h ∈ F.shifts, κ h ∈ (pi T).realLattice) ∧
      (∀ h ∈ F.shifts, slow h * middle h * rat h *
        (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (κ h) =
          ⟨⟨(piRealOrbit (fun i => (T i).filtration)
            (g h)).log,
            (piRealOrbit (fun i => (T i).filtration)
            (g h)).property⟩⟩) ∧
      (∀ h ∈ F.shifts, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
        (fun _ => (N : ℝ)) (Real.exp p) (slow h)) ∧
      (∀ h ∈ F.shifts, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1)
        F.denominator (rat h)) ∧
      (∀ h ∈ F.shifts, coefficients
        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))) 0 = 0) ∧
      (∀ h ∈ F.shifts, ∀ α, coefficients
        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))) α ∈
          (pi T).filtration.realGradedRefiltrationLayer F.subalgebra (Finsupp.weight (fun _ : Unit => 1) α))

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  {B : PositiveShiftBasis.{u} s N q a J} {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  {D : ∀ j, RationalFilteredNilmanifold (L j) s (d j)}
  {E : ∀ j, RationalFilteredNilmanifold (M j) s (e j)}
  {A : ∀ j, (D j).Niltest (fun _ : Unit => 1)}
  {R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1)}
  {anchor : ZMod N} {H : Finset (ZMod N)} {p : ℝ}

theorem CommonFactorization.exists_test_extension
    (F : B.CommonFactorization D E A R anchor H p) (hH : H ⊆ B.shifts) (hqp : q ≤ p) :
    ∃ S : ZMod N → B.model.Niltest (fun _ : Unit => 1),
      (∀ h ∈ F.shifts, S h = B.test h) ∧
      (∀ h, (S h).ComplexityLE p) ∧ (∀ h, (S h).UnitIntervalValued) ∧
      (∀ h z, z ∈ B.model.filtration.realification.subgroup s →
        (∀ j, realifyFunctional (F.frequency j none) z.coord = 0) → ∀ x,
          (S h).observable (z • x) = (S h).observable x) := by
  classical
  obtain ⟨h₀, hh₀⟩ := F.shifts_nonempty
  let select (h : ZMod N) := if h ∈ F.shifts then h else h₀
  have hselect (h) : select h ∈ F.shifts := by
    by_cases hh : h ∈ F.shifts <;> simp [select, hh, hh₀]
  refine ⟨fun h => B.test (select h), ?_, ?_, ?_, ?_⟩
  · intro h hh
    simp only [select, ite_eq_left hh]
  · intro h
    exact (B.test_complexity (select h) (hH (F.shifts_sub (hselect h)))).mono hqp
  · intro h
    exact B.test_positive (select h) (hH (F.shifts_sub (hselect h)))
  · intro h z hz hfreq x
    exact F.invariant (select h) (hselect h) z hz hfreq x

theorem CommonFactorization.exists_factor_family
    (F : B.CommonFactorization D E A R anchor H p) : F.FactorFamily := by
  classical
  dsimp only [CommonFactorization.FactorFamily]
  let T := B.anchoredFactors D E
  have hdata (h : ZMod N) (hh : h ∈ F.shifts) := F.factors h hh
  choose freq _ _ κ slow middle rat hκ hfactor hslow hrat hzero _ hcoeff _ using hdata
  let κ' (h : ZMod N) := if hh : h ∈ F.shifts then κ h hh else 1
  let slow' (h : ZMod N) := if hh : h ∈ F.shifts then slow h hh else 1
  let middle' (h : ZMod N) := if hh : h ∈ F.shifts then middle h hh else 1
  let rat' (h : ZMod N) := if hh : h ∈ F.shifts then rat h hh else 1
  refine ⟨κ', slow', middle', rat', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    simpa only [κ', dite_eq_left hh] using hκ h hh
  · intro h hh
    simpa only [κ', slow', middle', rat', dite_eq_left hh] using hfactor h hh
  · intro h hh
    simpa only [slow', dite_eq_left hh] using hslow h hh
  · intro h hh
    simpa only [rat', dite_eq_left hh] using hrat h hh
  · intro h hh
    simpa only [middle', dite_eq_left hh] using hzero h hh
  · intro h hh α
    simpa only [middle', dite_eq_left hh] using hcoeff h hh α

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

def productExpansionBudget (p : ℝ) : ℝ := (2 * p + 4) ^ 2 + p + 2

theorem productExpansionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ productExpansionBudget p ∧ p ≤ productExpansionBudget p ∧
      (2 * p + 4) ^ 2 ≤ productExpansionBudget p := by
  dsimp [productExpansionBudget]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  · linarith

def CommonRefilteredExpansionSpec (s r C : ℕ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q a J)
      {L M : Fin B.count → Type}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1) (e j))
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
      (anchor : ZMod N) (H : Finset (ZMod N)) {p : ℝ}
      (F : B.CommonFactorization D E A R anchor H p),
      2 ≤ p → q ≤ p →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      let T := B.anchoredFactors D E
      let t := productExpansionBudget p
      ∃ U : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra)
          (s + 1) (finrank ℚ ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra)),
        U.filtration = (pi T).filtration.gradedRefiltration F.subalgebra ∧
        U.lattice = (pi T).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi T).filtration.gradedRefiltration F.subalgebra).lowerCentralSeries_eq_bot)
            ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra).incl) ∧
        U.GeometryComplexityLE ((t + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra) ⧸
                U.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = U.filtration.quotientTop ∧
            Q.lattice = U.lattice.map
              (U.filtration.quotientStepHom (U.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((t + C) ^ C) ∧
            (nativeRefilteredTarget T none F.subalgebra U Q).GeometryComplexityLE ((t + C) ^ C) ∧
            ∃ cost : ℝ, 0 ≤ cost ∧ cost ≤ (t + C) ^ C ∧
              RefilteredProductExpansionSpec T none F.subalgebra U Q t F.denominator r cost

end Erdos3.PositiveShiftBasis

end

end OAI
