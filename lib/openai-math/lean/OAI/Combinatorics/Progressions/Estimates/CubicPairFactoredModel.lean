/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.CubicKernelCorrelatedModel
import OAI.Combinatorics.Progressions.Polynomial.CubicPairPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_cubic_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (_F : NativeCubicPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ _ : CubicReplicatedIndex, 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j shift V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have h3t : 3 ≤ t := by dsimp [t]; linarith
  have hBt : cubicPairBudget p q ≤ b := by
    dsimp [cubicPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ cubicPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  have hprodmono : productNiltestBudget (cubicPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (cubicPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.cubicPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.cubicPairPolynomial) t := by
    have h := F.factorization
    rw [V.cubicPairNiltest_symbol] at h
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration F.basis F.weight F.adapted h hrt (fun _ => by exact_mod_cast NeZero.pos N)
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.cubicPairNiltest_complexity.1.mono D htest) (by simpa using h3t)
    (fun a b => (F.height a b).trans hrt) V.cubicPairPolynomial
    (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ))
    (fun _ => (Real.exp_le_exp.mpr hcost).trans hN) hfactor
  exact ⟨R.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

theorem cubic_pair_top_agreement (x : ℝ ⊗[ℚ] V.CubicPairAlgebra)
    (hx : x ∈ (pi V.cubicPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : CubicReplicatedIndex, 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.cubicPairFrequency_real] at h
  linarith

theorem cubic_pair_middle_top_agreement (α : (Fin 3) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ _ : CubicReplicatedIndex, 1) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 0)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 3) ℚ
        (ℝ ⊗[ℚ] V.CubicPairAlgebra)) α)) =
    realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 1)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 3) ℚ
        (ℝ ⊗[ℚ] V.CubicPairAlgebra)) α)) := by
  apply R.cubic_pair_top_agreement
  simpa only [hα] using R.middle_coefficients α

theorem cubic_pair_middle_bracket_agreement (α β : (Fin 3) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ _ : CubicReplicatedIndex, 1) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.cubicPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 3) ℚ
            (ℝ ⊗[ℚ] V.CubicPairAlgebra)) α),
        realificationLieHom (V.cubicPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 3) ℚ
            (ℝ ⊗[ℚ] V.CubicPairAlgebra)) β)⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.cubicPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 3) ℚ
            (ℝ ⊗[ℚ] V.CubicPairAlgebra)) α),
        realificationLieHom (V.cubicPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 3) ℚ
            (ℝ ⊗[ℚ] V.CubicPairAlgebra)) β)⁆ := by
  have h := R.middle_bracket_frequency α β hαβ
  rw [V.cubicPairFrequency_real] at h
  simp only [LieHom.map_lie] at h
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

theorem cubic_pair_eval_factors (n : Fin 3 → ℤ) :
    W.cubicAntisymmetricPair i j (n 1) (n 2) (n 0 + shift) * star (V.test.eval n) =
      V.cubicPairNiltest.observable (QuotientGroup.mk
        ((pi V.cubicPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 3 => 1) (fun k => (n k : ℝ)) R.slow *
          (pi V.cubicPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 3 => 1) (fun k => (n k : ℝ)) R.middle *
          (pi V.cubicPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 3 => 1) (fun k => (n k : ℝ)) R.rational)) := by
  rw [← V.cubicPairNiltest_eval n]
  exact R.eval_niltest V.cubicPairNiltest V.cubicPairPolynomial_eq_test n

theorem cubic_pair_top_layer_invariant (z : (pi V.cubicPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.cubicPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : CubicReplicatedIndex, 1)) (x : (pi V.cubicPairModels).Space) :
    V.cubicPairNiltest.observable (z • x) = V.cubicPairNiltest.observable x := by
  have htop : z ∈ (pi V.cubicPairModels).filtration.realification.subgroup
      (∑ _ : CubicReplicatedIndex, 1) :=
    (pi V.cubicPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.cubicPairNiltest_vertical z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Erdos3.NativePolynomialOrbitFactors

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

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

include V in
theorem cubicOriginalComponent_cost : p + 4 ≤ cubicPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hr : 0 ≤ raisedNiltestBudget (p + q) :=
    (add_nonneg hp hq).trans (le_raisedNiltestBudget _)
  unfold cubicPairBudget
  linarith

noncomputable def cubicComparisonFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![-W.vertical.frequency, W.vertical.frequency] k

theorem cubicComparisonFrequency_apply (x : V.CubicPairAlgebra) :
    piFrequency V.cubicComparisonFrequencies x =
      W.vertical.frequency (V.cubicPairProjection 1 x) -
        W.vertical.frequency (V.cubicPairProjection 0 x) := by
  have h (x₀ x₁ : W.L) :
      0 + ((-W.vertical.frequency) x₀ + W.vertical.frequency x₁) =
        W.vertical.frequency x₁ - W.vertical.frequency x₀ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem cubicComparisonFrequency_real (x : ℝ ⊗[ℚ] V.CubicPairAlgebra) :
    realifyFunctional (piFrequency V.cubicComparisonFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 1) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 0) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.cubicComparisonFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

noncomputable def cubicPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.cubicPairModels k).Niltest (fun _ : Fin 3 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some k => ![(W.cubicOriginalComponent a 1 2 0 shift).conjugate, W.cubicOriginalComponent b 2 1 0 shift] k

theorem cubicPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.cubicPairComparisonTests a b k).ComplexityLE (cubicPairBudget p q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le)
      (V.cubicPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.cubicOriginalComponent_complexity a 1 2 0 shift).mono V.cubicOriginalComponent_cost
    · exact (W.cubicOriginalComponent_complexity b 2 1 0 shift).mono V.cubicOriginalComponent_cost

theorem cubicPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.cubicPairModels k).RealGroup)
    (hz : z ∈ (V.cubicPairModels k).filtration.realification.subgroup
      (∑ _ : CubicReplicatedIndex, 1)) (x : (V.cubicPairModels k).Space) :
    (V.cubicPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.cubicComparisonFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.cubicPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.cubicOriginalComponent_vertical a 1 2 0 shift) z hz x
    · exact W.cubicOriginalComponent_vertical b 2 1 0 shift z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

noncomputable def cubicPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.cubicPairModels).Niltest (fun _ : Fin 3 => 1) :=
  piNiltest V.cubicPairModels (V.cubicPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ cubicPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le))
    (V.cubicPairComparisonTests_complexity a b)

theorem cubicPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.cubicPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (cubicPairBudget p q)) :=
  piNiltest_complexity V.cubicPairModels (V.cubicPairComparisonTests a b) _ _ _

theorem cubicPairComparisonNiltest_orbit (a b : Fin W.outputDim) :
    (V.cubicPairComparisonNiltest a b).orbit = V.cubicPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun k => (V.cubicPairModels k).filtration))
  funext k
  cases k with
  | none => rfl
  | some k => fin_cases k <;> rfl

theorem cubicPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.cubicPairModels).Space) :
    (V.cubicPairComparisonNiltest a b).observable x =
      star (W.vertical.observable a (productProjection V.cubicPairModels (some 0) x)) *
        W.vertical.observable b (productProjection V.cubicPairModels (some 1) x) := by
  change (∏ k, (V.cubicPairComparisonTests a b k).observable
    (productProjection V.cubicPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (star (W.vertical.observable a
    (productProjection V.cubicPairModels (some 0) x)) *
      W.vertical.observable b (productProjection V.cubicPairModels (some 1) x)) = _
  exact one_mul _

theorem cubicPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.cubicPairModels).RealGroup)
    (hz : z ∈ (pi V.cubicPairModels).filtration.realification.subgroup
      (∑ _ : CubicReplicatedIndex, 1)) (x : (pi V.cubicPairModels).Space) :
    (V.cubicPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.cubicComparisonFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.cubicPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.cubicPairModels (V.cubicPairComparisonTests a b)
    V.cubicComparisonFrequencies _ _ _ (V.cubicPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

theorem cubic_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.cubicPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.cubicPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : CubicReplicatedIndex, 1)) (x : (pi V.cubicPairModels).Space) :
    (V.cubicPairComparisonNiltest a b).observable (z • x) =
      (V.cubicPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.cubicPairModels).filtration.realification.subgroup
      (∑ _ : CubicReplicatedIndex, 1) :=
    (pi V.cubicPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.cubicPairComparisonNiltest_vertical a b z htop, V.cubicComparisonFrequency_real,
    ← R.cubic_pair_top_agreement z.coord hz, sub_self]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

noncomputable def cubicPairFrozenVector (k : Fin 2)
    (a b : (pi V.cubicPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin 3 → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.cubicPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

theorem cubicPairFrozenVector_unit (k : Fin 2)
    (a b : (pi V.cubicPairModels).RealGroup) (x : Fin 3 → ℤ) :
    ∑ out, ‖R.cubicPairFrozenVector k a b out x‖ ^ 2 = 1 :=
  W.vertical.unit _

def HasCubicPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.cubicPairModels).RealGroup,
      (∀ i, |((pi V.cubicPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.cubicPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
      NativeIntegerVectorEquivalence 2 b (R.cubicPairFrozenVector 0 a r) (R.cubicPairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

theorem exists_cubic_frozen_equivalence_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p q r u : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r → 0 ≤ u →
      ∃ t : ℝ, 0 ≤ t ∧ r ≤ t ∧ u ≤ t ∧ p ≤ t ∧
        productNiltestBudget (cubicPairBudget p q) ≤ t ∧
        t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u hp hq hr hu
  let v := p + q + r + u
  let b := 4 * (v + 1) + raisedNiltestBudget v + 6
  let t := productNiltestBudget b + v + 3
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
  have hBt : cubicPairBudget p q ≤ b := by
    dsimp [cubicPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ cubicPairBudget p q := by
    unfold cubicPairBudget raisedNiltestBudget
    positivity
  have hprodmono : productNiltestBudget (cubicPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (cubicPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  exact ⟨t, ht, hrt, hut, hpt, htest, hsum⟩

theorem exists_cubic_pair_frozen_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasCubicPairFrozenEquivalence u ((p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion 2
  obtain ⟨C, hC, hbudget⟩ := exists_cubic_frozen_equivalence_budget a
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j shift V R _ _ _ _ hr hu m hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  obtain ⟨t, ht, hrt, hut, hpt, htest, hsum⟩ := hbudget p q r u hp hq hr hu
  have htC : t ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin 3, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.cubicPairModels) (R.mono hrt hN)
    (V.cubicPairComparisonNiltest out₀ out₁) ht ((V.cubicPairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.cubic_pair_comparison_invariant out₀ out₁) m hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2
      ((p + q + r + u + C) ^ C) (fun x =>
        star ((V.cubicPairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x))))) :=
    ⟨F.conjugate.mono hcost⟩
  have heq : (fun x : Fin 3 → ℤ =>
      star ((V.cubicPairComparisonNiltest out₀ out₁).observable
        (QuotientGroup.mk (R.frozenMiddleValue left right x)))) =
      (fun x => R.cubicPairFrozenVector 0 left right out₀ x *
        star (R.cubicPairFrozenVector 1 left right out₁ x)) := by
    funext x
    rw [V.cubicPairComparisonNiltest_observable, star_mul, star_star]
    exact mul_comm _ _
  exact (congrArg (fun f : (Fin 3 → ℤ) → ℂ =>
    Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2
      ((p + q + r + u + C) ^ C) f)) heq).mp hF

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

theorem exists_cubic_pair_factored_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) q,
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 q
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 q
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-q) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin V.outputDim × Fin V.outputDim),
              ∃ S : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
                Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
                (fun z => V.cubicAntisymmetricPair i j (z 1).val (z 2).val
                  (((z 0).val : ℤ) + -(if branch then (N : ℤ) else 0))),
                Nonempty (NativePolynomialOrbitFactors (pi S.cubicPairModels)
                  S.cubicPairPolynomial (piFrequency S.cubicPairFrequencies)
                  (fun _ : Fin 3 => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨a, _, hmodel⟩ := exists_cubic_kernel_correlated_model
  obtain ⟨b, _, hstep⟩ := exists_cubic_pair_step_drop
  obtain ⟨c, _, horbit⟩ := exists_cubic_pair_orbit_factors
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let U := (Q + Q + Polynomial.C b) ^ b
  let T := (Q + Q + U + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + U + T)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  let u := (q + q + b) ^ b
  let t := (q + q + u + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsum : q + u + t ≤ (p + C) ^ C := by
    simpa [X, Q, U, T, q, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, out, χ, hcorr,
    branch, i, j, hS⟩ := hmodel hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  have hS' : Nonempty (NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
      Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => V.cubicAntisymmetricPair i j (z 1).val (z 2).val
        (((z 0).val : ℤ) + -(if branch then (N : ℤ) else 0)))) := by
    simpa only [cyclicBranchOffset, sub_eq_add_neg] using hS
  obtain ⟨S⟩ := hS'
  obtain ⟨F⟩ := hstep S ((Real.exp_le_exp.mpr huC).trans hN)
  obtain ⟨R⟩ := horbit F hu ((Real.exp_le_exp.mpr htC).trans hN)
  exact ⟨q, hq, hqC, H, hH, hHdense, M, V, hdim, hsymm, hdiag, E,
    out, χ, hcorr, branch, i, j, S,
    ⟨R.mono htC (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

end OAI
