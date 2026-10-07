/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeFrozenComparison
import OAI.Combinatorics.Progressions.Geometry.AntisymmetricPairCoordinateTest
import OAI.Combinatorics.Progressions.Linear.AntisymmetricPairProjections

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control 2 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.antisymmetricPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
      (fun k => (V.antisymmetricPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

theorem NativeSampleCorrelation.antisymmetricPairPolynomialMap_coefficient
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
    (k : Fin 2) (g : ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group) (α : (Fin 2) →₀ ℕ) :
    coefficients ((V.antisymmetricPairPolynomialMap k g).coord :
      VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) α =
    realificationLieHom (V.antisymmetricPairProjection k)
      (coefficients (g.coord : VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) α) := by
  rw [V.antisymmetricPairPolynomialMap_log, coefficients_map]
  rfl

namespace NativePolynomialOrbitFactors

variable (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
  V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
  (fun _ : Fin 2 => (N : ℝ)) r)

theorem pair_projected_product (k : Fin 2) (out : Fin W.outputDim) :
    V.antisymmetricPairPolynomialMap k R.slow * V.antisymmetricPairPolynomialMap k R.middle *
      V.antisymmetricPairPolynomialMap k R.rational *
        W.model.filtration.realification.adaptedConstantGroupHom (fun _ : Fin 2 => 1)
          (productProjectionHom V.antisymmetricPairModels (some k) R.latticeConstant) =
      W.pairComponentPolynomial out k k.rev := by
  have h := congrArg (V.antisymmetricPairPolynomialMap k) R.product
  simpa only [map_mul, V.antisymmetricPairPolynomialMap_constant,
    V.antisymmetricPairPolynomialMap_eq k out] using h

theorem pair_eval_component (k : Fin 2) (out : Fin W.outputDim) (n : Fin 2 → ℤ) :
    W.eval out (correlationInput (n k) (n k.rev)) =
      (W.pairComponent out k k.rev).observable (QuotientGroup.mk
        (W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.slow) *
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.middle) *
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.rational))) := by
  have h := Niltest.eval_of_lattice_factorization W.model (fun _ : Fin 2 => 1)
    (W.pairComponent out k k.rev) (V.antisymmetricPairPolynomialMap k R.slow)
    (V.antisymmetricPairPolynomialMap k R.middle) (V.antisymmetricPairPolynomialMap k R.rational)
    (productProjectionHom V.antisymmetricPairModels (some k) R.latticeConstant)
    (V.antisymmetricPairProjection_lattice k R.latticeConstant R.latticeConstant_mem)
    (R.pair_projected_product k out) n
  simpa only [W.pairComponent_eval] using h

theorem pair_projected_middle_zero (k : Fin 2) :
    coefficients ((V.antisymmetricPairPolynomialMap k R.middle).coord :
      VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) 0 = 0 := by
  rw [V.antisymmetricPairPolynomialMap_coefficient, R.middle_zero, map_zero]

theorem pair_projected_rational_zero (k : Fin 2) :
    coefficients ((V.antisymmetricPairPolynomialMap k R.rational).coord :
      VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) 0 = 0 := by
  rw [V.antisymmetricPairPolynomialMap_coefficient, R.rational_zero, map_zero]

theorem pair_projected_top_agreement (α : (Fin 2) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ k, mixedCorrelationDegree 1 k) :
    realifyFunctional W.vertical.frequency
      (coefficients ((V.antisymmetricPairPolynomialMap 0 R.middle).coord :
        VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) α) =
    realifyFunctional W.vertical.frequency
      (coefficients ((V.antisymmetricPairPolynomialMap 1 R.middle).coord :
        VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) α) := by
  simpa only [V.antisymmetricPairPolynomialMap_coefficient] using R.pair_middle_top_agreement α hα

theorem pair_projected_bracket_agreement (α β : (Fin 2) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ k, mixedCorrelationDegree 1 k) :
    realifyFunctional W.vertical.frequency
      ⁅coefficients ((V.antisymmetricPairPolynomialMap 0 R.middle).coord :
          VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) α,
        coefficients ((V.antisymmetricPairPolynomialMap 0 R.middle).coord :
          VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) β⁆ =
    realifyFunctional W.vertical.frequency
      ⁅coefficients ((V.antisymmetricPairPolynomialMap 1 R.middle).coord :
          VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) α,
        coefficients ((V.antisymmetricPairPolynomialMap 1 R.middle).coord :
          VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) β⁆ := by
  simpa only [V.antisymmetricPairPolynomialMap_coefficient] using R.pair_middle_bracket_agreement α β hαβ

theorem pair_first_layer_bracket_agreement (x y : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
    (hx : x ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer R.subalgebra 1)
    (hy : y ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer R.subalgebra 1) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.antisymmetricPairProjection 0) x,
        realificationLieHom (V.antisymmetricPairProjection 0) y⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.antisymmetricPairProjection 1) x,
        realificationLieHom (V.antisymmetricPairProjection 1) y⁆ := by
  have hb := (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_lie_mem R.subalgebra hx hy
  have hdegree : (1 + 1 : ℕ) = ∑ k, mixedCorrelationDegree 1 k := by decide
  have h := R.pair_top_agreement ⁅x, y⁆ (by simpa only [hdegree] using hb)
  simpa only [LieHom.map_lie] using h

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

theorem NativeSampleCorrelation.antisymmetricPairPolynomialMap_value
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
    (k : Fin 2)
    (g : ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group) (x : Fin 2 → ℝ) :
    W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) x
        (V.antisymmetricPairPolynomialMap k g) =
      productProjectionHom V.antisymmetricPairModels (some k)
        ((pi V.antisymmetricPairModels).filtration.adaptedPolynomialRealValueHom
          (fun _ : Fin 2 => 1) x g) :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap_value W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k)
    (fun _ : Fin 2 => 1) g x

namespace NativePolynomialOrbitFactors

variable (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
  V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
  (fun _ : Fin 2 => (N : ℝ)) r)

theorem pairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.eval out (correlationInput (x k) (x k.rev)) =
      R.pairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  rw [R.pair_eval_component k out x]
  simp only [pairFrozenVector, frozenMiddleValue, slowValue, rationalValue,
    productProjection_mk, map_mul, V.antisymmetricPairPolynomialMap_value]
  rfl

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem hasPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasPairFrozenEquivalence u b := by
  intro m hm hmb left right hleft hright
  exact (h m hm hmb left right hleft hright).mono hab

def HasPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasPairFrozenEquivalence u b

theorem hasPairFrozenReduction_mono {a b : ℝ}
    (h : R.HasPairFrozenReduction a) (hab : a ≤ b) : R.HasPairFrozenReduction b := by
  obtain ⟨u, hu, hua, houter, hequiv⟩ := h
  exact ⟨u, hu, hua.trans hab, houter, R.hasPairFrozenEquivalence_mono hequiv hab⟩

theorem pairFrozenEquivalence_at {b : ℝ} (h : R.HasPairFrozenReduction b)
    (x : Fin 2 → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence 1 b
      (R.pairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.pairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨m, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv m hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_pair_frozen_reduction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasPairFrozenReduction ((p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_antisymmetric_pair_outer_control
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_equivalence
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  exact ⟨u, hu, huC, houter R hr,
    R.hasPairFrozenEquivalence_mono (hfrozen R hr hu) hBC⟩

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

def HasPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin 2 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (correlationInput (x k) (x k.rev)) -
          R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

theorem hasPairLocalApproximation_mono {a b : ℝ}
    (h : R.HasPairLocalApproximation a) (hab : a ≤ b) : R.HasPairLocalApproximation b := by
  obtain ⟨P, hP, hPb, hlocal⟩ := h
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  exact (hlocal y hy k out x δ hδ hx hres hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) hδ)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin 2 → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.antisymmetricPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.antisymmetricPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.antisymmetricPairModels).basis.baseChange ℝ)
    ‖W.eval out (correlationInput (x k) (x k.rev)) -
        R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.antisymmetricPairModels
  let T := V.pairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 2 => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) := by
    have h := T.observable_budget (V.pairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.pairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.pairCoordinateNiltest_observable, pairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.pairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_local_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasPairLocalApproximation ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin 2) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.pairCoordinateNiltest_complexity 0 i).1.mono D htest
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.antisymmetricPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.pairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairAnchoredVector (y : Fin 2 → ℤ) (k : Fin 2) :
    Fin W.outputDim → (Fin 2 → ℤ) → ℂ :=
  R.pairFrozenVector k (R.slowValue y) (R.rationalValue y)

theorem pairAnchoredVector_norm (y : Fin 2 → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin 2 → ℤ) : ‖R.pairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

theorem select_pair_local_partition {b c : ℝ}
    (hlocal : R.HasPairLocalApproximation b) (hred : R.HasPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 2 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 2 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 1 c
            (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ (k : Fin 2) (out : Fin W.outputDim),
            (𝔼 x : Fin 2 → ZMod N,
              ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
                ∑ j, (A j x : ℂ) * R.pairAnchoredVector
                  (fun i => ((y j i).val : ℤ)) k out (fun i => ((x i).val : ℤ))‖) ≤
              Real.exp b * ρ + 4 * B.card / N := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 2 → ZMod N) (i : Fin 2) => ((x i).val : ℤ)
  have hv (x : Fin 2 → ZMod N) (i : Fin 2) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 2 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.pairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro k out
  let F := fun x : Fin 2 → ZMod N => W.eval out (correlationInput (v x k) (v x k.rev))
  let G := fun j (x : Fin 2 → ZMod N) => R.pairAnchoredVector (v (y j)) k out (v x)
  let E := coordinateExceptional (ι := Fin 2) B
  have hpoint (j : I) (x : Fin 2 → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - G j x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hmodel (v (y j)) (hv (y j)) k out (v x) ρ hρ (hv x) hres
      (by simpa only [v, Int.cast_natCast] using hnear)
  have hcap (x : Fin 2 → ZMod N) : ‖F x - ∑ j, (A j x : ℂ) * G j x‖ ≤ 2 := by
    apply norm_sub_positive_sum_le (fun j => A j x) (fun j => G j x) (F x) 2
      (fun j => hA j x) (hsum x)
    intro j _
    exact (norm_sub_le _ _).trans (by
      have hF : ‖F x‖ ≤ 1 := W.norm_eval out _
      have hG : ‖G j x‖ ≤ 1 := R.pairAnchoredVector_norm _ _ _ _
      linarith)
  have hgood (x : Fin 2 → ZMod N) (hx : x ∉ E) :
      ‖F x - ∑ j, (A j x : ℂ) * G j x‖ ≤ Real.exp b * ρ :=
    norm_sub_positive_sum_le (fun j => A j x) (fun j => G j x) (F x) (Real.exp b * ρ)
      (fun j => hA j x) (hsum x) (fun j => hpoint j x hx)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ‖F x - ∑ j, (A j x : ℂ) * G j x‖) (mul_nonneg (Real.exp_nonneg b) hρ)
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by simpa only [abs_of_nonneg (norm_nonneg _)] using hgood x hx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin 2) B
  have herr' : (𝔼 x : Fin 2 → ZMod N, ‖F x - ∑ j, (A j x : ℂ) * G j x‖) ≤
      Real.exp b * ρ + 2 * ((E.card : ℝ) / Fintype.card (Fin 2 → ZMod N)) := by
    simpa only [abs_of_nonneg (norm_nonneg _), mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + 2 * (2 * (B.card : ℝ) / N) := by gcongr
    _ = _ := by ring

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_pair_local_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ P : ℕ, ∃ hP : 0 < P,
        letI : NeZero P := ⟨hP.ne'⟩
        (P : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧
          (Fintype.card (Fin 2 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
          ∃ A : (Fin n × ZMod P) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            ∃ y : (Fin 2 → Fin n × ZMod P) → (Fin 2 → ZMod N),
              (∀ j, NativeIntegerVectorEquivalence 1 ((t + C) ^ C)
                (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
                (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
              ∀ (k : Fin 2) (out : Fin W.outputDim),
                (𝔼 x : Fin 2 → ZMod N,
                  ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
                    ∑ j, ((∏ i, A (j i) (x i) : ℝ) : ℂ) * R.pairAnchoredVector
                      (fun i => ((y j i).val : ℤ)) k out (fun i => ((x i).val : ℤ))‖) ≤
                  Real.exp (t + 40) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 40 + 2 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_pair_local_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 40 + 2 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have htwo : 2 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 2 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 2 => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, herr⟩ := hselect E w hρ.le hw hwSum hcells
  refine ⟨P, hP, hPt.trans (Real.exp_le_exp.mpr htC), n, hn, ?_, A,
    fun j => (hA j).mono le_rfl hcost, hsum, y,
    fun j => (hequiv j).mono (hct.trans htC), ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = Real.exp (2 * (t + B) ^ B) := (Real.exp_nat_mul _ 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr htwo
  · intro k out
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have h40 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
    apply (herr k out).trans
    calc
      _ = Real.exp b * ρ + 4 * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp t * ρ + 4 * (6 * ρ + 3 / N) := by gcongr
      _ ≤ Real.exp t * ρ + 4 * Real.exp t * (6 * ρ + 3 / N) := by
        gcongr
        nlinarith [Real.one_le_exp ht]
      _ = Real.exp t * (25 * ρ + 12 * (1 / N)) := by ring
      _ ≤ Real.exp t * (40 * (ρ + 1 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg t)
      _ = 40 * Real.exp t * (ρ + 1 / N) := by ring
      _ ≤ Real.exp 40 * Real.exp t * (ρ + 1 / N) := by gcongr
      _ = Real.exp (t + 40) * (ρ + 1 / N) := by rw [← Real.exp_add, add_comm 40 t]

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairCoordinate_common_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ l, mixedCorrelationDegree 1 l))
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency
          (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle) *
        (V.pairCoordinateNiltest k out).observable x := by
  have htop := (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le
    R.subalgebra _ hz
  have heq := R.pair_top_agreement z.coord hz
  rw [V.pairCoordinateNiltest_observable, productProjection_smul]
  have hv := W.pairComponent_vertical out k k.rev
    (productProjectionHom V.antisymmetricPairModels (some k) z)
    (productProjectionHom_mem_layer V.antisymmetricPairModels (some k) _ z htop)
    (productProjection V.antisymmetricPairModels (some k) x)
  change W.vertical.observable out _ = _ at hv
  refine hv.trans ?_
  change CircleFourier.character
      ((realifyFunctional W.vertical.frequency
        (realificationLieHom (V.antisymmetricPairProjection k) z.coord) : ℝ) : CircleFourier.Circle) *
      W.vertical.observable out _ = _
  have hphase : realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection k) z.coord) =
    realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) := by
    fin_cases k
    · rfl
    · exact heq.symm
  rw [hphase]
  exact congrArg (fun w : ℂ => CircleFourier.character
    ((realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle) * w)
      (V.pairCoordinateNiltest_observable k out x).symm

theorem pairCoordinate_comparison_invariant (k l : Fin 2) (i j : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ l, mixedCorrelationDegree 1 l))
    (x y : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k i).observable (z • x) *
      star ((V.pairCoordinateNiltest l j).observable (z • y)) =
    (V.pairCoordinateNiltest k i).observable x * star ((V.pairCoordinateNiltest l j).observable y) := by
  let c := CircleFourier.character
    ((realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    dsimp only [c]
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  rw [R.pairCoordinate_common_vertical k i z hz x,
    R.pairCoordinate_common_vertical l j z hz y, star_mul]
  change (c * _) * (_ * star c) = _
  calc
    _ = (c * star c) * ((V.pairCoordinateNiltest k i).observable x *
      star ((V.pairCoordinateNiltest l j).observable y)) := by ring
    _ = _ := by rw [hc, one_mul]

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_anchor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → R.HasOuterValueControl u →
      ∀ y z : Fin 2 → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
        (∀ k, |(z k : ℝ)| ≤ (N : ℝ)) → ∀ k l : Fin 2,
        NativeIntegerVectorEquivalence 1 ((p + q + r + u + C) ^ C)
          (R.pairAnchoredVector y k) (R.pairAnchoredVector z l) := by
  obtain ⟨A, _, hcomparison⟩ := exists_native_frozen_comparison 1
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R hr hu houter y z hy hz k l
  let := moduleTopology ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.antisymmetricPairModels).basis
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u
  let b := v + raisedNiltestBudget v + 4
  let t := productNiltestBudget b + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + A) ^ A ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + q + r + u + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + A) ^ A ≤ (p + q + r + u + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hcap (k : Fin 2) (out : Fin W.outputDim) (x : (pi V.antisymmetricPairModels).Space) :
      ‖(V.pairCoordinateNiltest k out).observable x‖ ≤ 1 := by
    rw [V.pairCoordinateNiltest_observable]
    exact W.vertical.norm out _
  obtain ⟨E⟩ := hcomparison (pi V.antisymmetricPairModels) (R.mono hrt hN)
    ![V.pairCoordinateNiltest k out₀, V.pairCoordinateNiltest l out₁] ht
    (by intro a; fin_cases a
        · exact (V.pairCoordinateNiltest_complexity k out₀).mono htest
        · exact (V.pairCoordinateNiltest_complexity l out₁).mono htest)
    (by intro a x; fin_cases a
        · exact hcap k out₀ x
        · exact hcap l out₁ x)
    (fun a ha x y => R.pairCoordinate_comparison_invariant k l out₀ out₁ a ha x y)
    m hm (hmb.trans (Real.exp_le_exp.mpr hut))
    ![R.slowValue y, R.slowValue z] ![R.rationalValue y, R.rationalValue z]
    (by intro a e; fin_cases a
        · exact (hslow y hy e).trans (Real.exp_le_exp.mpr hut)
        · exact (hslow z hz e).trans (Real.exp_le_exp.mpr hut))
    (by intro a; fin_cases a
        · exact hrat y
        · exact hrat z)
  simpa only [V.pairCoordinateNiltest_observable, NativePolynomialOrbitFactors.pairAnchoredVector,
    NativePolynomialOrbitFactors.pairFrozenVector] using
    (show Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + r + u + C) ^ C)
      (fun x => (V.pairCoordinateNiltest k out₀).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x)) *
        star ((V.pairCoordinateNiltest l out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue z) (R.rationalValue z) x))))) from
      ⟨E.mono hcost⟩)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors.FrozenMiddleRealization

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r}
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.antisymmetricPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

noncomputable def pairMiddleTest (k : Fin 2) (out : Fin W.outputDim) :
    M.model.Niltest (fun _ : Fin 2 => 1) :=
  M.pullTest (V.pairCoordinateNiltest k out) (fun x => by
    rw [V.pairCoordinateNiltest_observable]
    exact W.vertical.norm out _)

theorem pairMiddleTest_eval (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) :
    (M.pairMiddleTest k out).eval x = R.pairFrozenVector k a c out x := by
  rw [pairMiddleTest, M.pullTest_eval, V.pairCoordinateNiltest_observable]
  rfl

theorem pairMiddleTest_unit (k : Fin 2) (x : M.model.Space) :
    ∑ out, ‖(M.pairMiddleTest k out).observable x‖ ^ 2 = 1 := by
  change ∑ out, ‖(V.pairCoordinateNiltest k out).observable (M.spaceMap x)‖ ^ 2 = 1
  simp only [V.pairCoordinateNiltest_observable]
  exact W.vertical.unit _

theorem pairMiddleTest_complexity (hb : 0 ≤ b) (k : Fin 2) (out : Fin W.outputDim) :
    (M.pairMiddleTest k out).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q) + b + 4) := by
  apply M.pullTest_complexity _ _ _ hb (V.pairCoordinateNiltest_complexity k out)
  have hB : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  unfold productNiltestBudget productObservableLipBudget
  positivity

theorem pairMiddleTest_common_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ l, mixedCorrelationDegree 1 l))
    (x : M.model.Space) :
    (M.pairMiddleTest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency
          (realificationLieHom (V.antisymmetricPairProjection 0)
            (realificationLieHom
              ((pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
              z.coord)) : ℝ) : CircleFourier.Circle) *
      (M.pairMiddleTest k out).observable x := by
  let D := pi V.antisymmetricPairModels
  let φ := realificationMap (hnil := M.model.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have htop : φ z ∈ D.filtration.realification.subgroup (∑ l, mixedCorrelationDegree 1 l) :=
    D.filtration.realGradedRefiltrationLayer_le R.subalgebra _ (M.inclusion_mem_top z hz)
  have heq := R.pair_top_agreement (φ z).coord (M.inclusion_mem_top z hz)
  change (V.pairCoordinateNiltest k out).observable (M.spaceMap (z • x)) = _
  rw [M.spaceMap_top_smul z hz, V.pairCoordinateNiltest_observable,
    productProjection_smul]
  have hv := W.pairComponent_vertical out k k.rev
    (productProjectionHom V.antisymmetricPairModels (some k) (φ z))
    (productProjectionHom_mem_layer V.antisymmetricPairModels (some k) _ (φ z) htop)
    (productProjection V.antisymmetricPairModels (some k) (M.spaceMap x))
  change W.vertical.observable out _ = _ at hv
  refine hv.trans ?_
  change CircleFourier.character
      ((realifyFunctional W.vertical.frequency
        (realificationLieHom (V.antisymmetricPairProjection k) (φ z).coord) : ℝ) :
        CircleFourier.Circle) * W.vertical.observable out _ = _
  have hphase : realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection k) (φ z).coord) =
    realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) (φ z).coord) := by
    fin_cases k
    · rfl
    · exact heq.symm
  rw [hphase]
  congr 1
  exact (V.pairCoordinateNiltest_observable k out (M.spaceMap x)).symm

end NativePolynomialOrbitFactors.FrozenMiddleRealization

theorem exists_antisymmetric_pair_middle_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ r → 0 ≤ u → R.HasOuterValueControl u → ∀ y : Fin 2 → ℤ,
      (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
      ∃ M : R.FrozenMiddleRealization (R.slowValue y) (R.rationalValue y)
          ((p + q + r + u + C) ^ C),
        (∀ k out, (M.pairMiddleTest k out).ComplexityLE ((p + q + r + u + C) ^ C)) ∧
        (∀ k out x, (M.pairMiddleTest k out).eval x = R.pairAnchoredVector y k out x) := by
  obtain ⟨a, _, hmodel⟩ := exists_native_frozen_middle_realization 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R _ _ _ _ _ _ _ _ hr hu houter y hy
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u
  let b := v + raisedNiltestBudget v + 4
  let t := productNiltestBudget b + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a + 4 ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have hcost : (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by linarith
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter
  obtain ⟨M⟩ := @hmodel V.AntisymmetricPairAlgebra (Fin 2) _ _ _ _ _ _ _
    (pi V.antisymmetricPairModels) _ _ _ t (R.mono hrt hN)
    (inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ]
      (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ]
      (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (T2Space (ℝ ⊗[ℚ]
      (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra))) ht
    (V.antisymmetricPairNiltest_complexity.mono htest).1
    m hm (hmb.trans (Real.exp_le_exp.mpr hut)) (R.slowValue y) (R.rationalValue y)
    (fun k => (hslow y hy k).trans (Real.exp_le_exp.mpr hut)) (hrat y)
  rcases M with ⟨D', hD'F, hD', hinc, orbit, hzero, heval, f, hf, K, hK, hLip⟩
  let M' : R.FrozenMiddleRealization (R.slowValue y) (R.rationalValue y) ((t + a) ^ a) :=
    ⟨D', hD'F, hD', hinc, orbit, hzero, heval, f, hf, K, hK, hLip⟩
  refine ⟨M'.mono hcost, ?_, ?_⟩
  · intro k out
    exact (M'.pairMiddleTest_complexity (by positivity) k out).mono
      ((by linarith : productNiltestBudget (antisymmetricPairBudget p q) + (t + a) ^ a + 4 ≤
        t + (t + a) ^ a + 4).trans hsum)
  · intro k out x
    exact (M'.mono hcost).pairMiddleTest_eval k out x

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def pairMiddleVerticalBudget (p q b : ℝ) : ℝ :=
  productNiltestBudget (antisymmetricPairBudget p q) + b + 4 + (p + b + 2) ^ 4

namespace NativePolynomialOrbitFactors

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairMiddleFrequency :
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra →ₗ[ℚ] ℚ :=
  (W.vertical.frequency.comp (V.antisymmetricPairProjection 0).toLinearMap).comp
    ((pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl.toLinearMap

theorem pairMiddleFrequency_real
    (x : ℝ ⊗[ℚ] (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra) :
    realifyFunctional R.pairMiddleFrequency x = realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0)
        (realificationLieHom
          ((pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl x)) := by
  rw [pairMiddleFrequency, realifyFunctional_comp, realifyFunctional_comp]
  rfl

variable {R}
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.antisymmetricPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

theorem FrozenMiddleRealization.pairMiddleFrequency_height (hb : 0 ≤ b)
    (l : Fin (Module.finrank ℚ
      ((pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra))) :
    rationalLogHeight (R.pairMiddleFrequency (M.model.basis l)) ≤ (p + b + 2) ^ 4 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  change rationalLogHeight (W.vertical.frequency
    (V.antisymmetricPairProjection 0 (M.model.basis l : V.AntisymmetricPairAlgebra))) ≤ _
  apply rational_functional_value_logHeight W.model.basis W.vertical.frequency
    (add_nonneg hp hb)
    (by simpa only [Fintype.card_fin] using W.complexity.1.1.trans (le_add_of_nonneg_right hb))
    (fun k => (W.vertical.height k).trans (le_add_of_nonneg_right hb))
  intro k
  rw [V.antisymmetricPairProjection_repr]
  exact (M.inclusion_height l _).trans (le_add_of_nonneg_left hp)

theorem FrozenMiddleRealization.pairMiddleFrequency_integral (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ l, mixedCorrelationDegree 1 l))
    (hlat : z ∈ M.model.realLattice) :
    ∃ n : ℤ, realifyFunctional R.pairMiddleFrequency z.coord = n := by
  let x : M.model.Space := QuotientGroup.mk 1
  obtain ⟨out, hout⟩ := exists_large_unit_coordinate
    (fun out => (M.pairMiddleTest 0 out).observable x) (M.pairMiddleTest_unit 0 x)
  have hnonzero : (M.pairMiddleTest 0 out).observable x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt ((by positivity : (0 : ℝ) < 1 / (Fintype.card (Fin W.outputDim) + 1 : ℝ)).trans_le hout)
  apply vertical_frequency_integral_on_lattice M.model.filtration M.model.realLattice
    R.pairMiddleFrequency (M.pairMiddleTest 0 out).observable ?_ ⟨x, hnonzero⟩ z hz hlat
  intro a ha y
  rw [R.pairMiddleFrequency_real]
  exact M.pairMiddleTest_common_vertical 0 out a ha y

noncomputable def FrozenMiddleRealization.pairMiddleVertical (hb : 0 ≤ b) (k : Fin 2) :
    M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ l, mixedCorrelationDegree 1 l))
      (Fin W.outputDim) (pairMiddleVerticalBudget p q b) where
  observable out := (M.pairMiddleTest k out).observable
  unit := M.pairMiddleTest_unit k
  norm out x := (M.pairMiddleTest k out).norm_le x
  lipBound := productExpBound (productNiltestBudget (antisymmetricPairBudget p q) + b + 4)
  lip_bound := by
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_right (by positivity)
  lipschitz := by
    let := M.model.metricSpace
    intro out
    apply (M.pairMiddleTest k out).lipschitz.weaken
    change ((M.pairMiddleTest k out).lipBound : ℝ) ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q) + b + 4)
    have h := (M.pairMiddleTest k out).observable_budget
      (M.pairMiddleTest_complexity hb k out)
    linarith [(M.pairMiddleTest k out).normBound.coe_nonneg]
  frequency := R.pairMiddleFrequency
  height l := by
    have hB : 0 ≤ antisymmetricPairBudget p q :=
      (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
    have hT : 0 ≤ productNiltestBudget (antisymmetricPairBudget p q) + b + 4 := by
      unfold productNiltestBudget productObservableLipBudget
      positivity
    exact (M.pairMiddleFrequency_height hb l).trans (le_add_of_nonneg_left hT)
  vertical out z hz x := by
    rw [R.pairMiddleFrequency_real]
    exact M.pairMiddleTest_common_vertical k out z hz x
  integral := M.pairMiddleFrequency_integral

theorem FrozenMiddleRealization.pairMiddleVertical_eval (hb : 0 ≤ b)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) :
    (M.pairMiddleVertical hb k).observable out (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
      R.pairFrozenVector k a c out x := M.pairMiddleTest_eval k out x

end NativePolynomialOrbitFactors
end Erdos3

end

end OAI
