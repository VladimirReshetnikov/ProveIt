import OAI.Combinatorics.Progressions.Estimates.MixedPairComparison
import OAI.Combinatorics.Progressions.Polynomial.QuarticPairPolynomial

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

structure NativeQuarticPairFactorization {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
    {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
      Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.QuarticPairAlgebra)) ℚ V.QuarticPairAlgebra
  weight : Fin (finrank ℚ V.QuarticPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.quarticPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.quarticPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.quarticPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.quarticPairFrequencies) (fun _ : Fin 4 => (N : ℝ))
    (V.quarticPairNiltest.symbol basis weight adapted) r

noncomputable def NativeQuarticPairFactorization.mono {p q r r' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
    {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
      Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
    (F : NativeQuarticPairFactorization V r) (hrr' : r ≤ r') : NativeQuarticPairFactorization V r' := by
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  exact { F with
    height := fun a b => (F.height a b).trans hrr'
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.quarticPairModels).filtration F.basis F.weight F.adapted F.factorization hrr'
      (fun _ => by exact_mod_cast NeZero.pos N) }

theorem exists_quartic_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeQuarticPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : QuarticReplicatedIndex, 1) (by decide)
  let X : Polynomial ℕ := Polynomial.X
  let Q := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (quarticPairBudget p q) + (p + q) + 4
  have hprod : 0 ≤ productNiltestBudget (quarticPairBudget p q) := by
    have hbase := V.quarticPairBudget_six_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hqr : q ≤ r := by dsimp only [r]; linarith only [hp, hprod]
  have h4r : 4 ≤ r := by dsimp only [r]; linarith only [hp, hq, hprod]
  have hTr : productNiltestBudget (quarticPairBudget p q) ≤ r := by dsimp only [r]; linarith only [hp, hq]
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, quarticPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.quarticPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra) := htT
  let D := pi V.quarticPairModels
  let T := V.quarticPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.quarticPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 4 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 4 => N) = integerBox (fun _ : Fin 4 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.quarticPairNiltest_bias
  have hf := hconstruct (piFrequency V.quarticPairFrequencies) V.quarticPairNiltest_vertical
    0 (fun _ : Fin 4 => N) (fun _ => NeZero.pos N) (by simpa using h4r)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun a b => (he a b).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }⟩

end Erdos3

end

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

theorem exists_quartic_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_F : NativeQuarticPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ _ : QuarticReplicatedIndex, 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 4
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have h4t : 4 ≤ t := by dsimp [t]; linarith
  have hBt : quarticPairBudget p q ≤ b := by
    dsimp [quarticPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ quarticPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  have hprodmono : productNiltestBudget (quarticPairBudget p q) ≤ productNiltestBudget b := by
    exact productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (quarticPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.quarticPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.quarticPairFrequencies) (fun _ : Fin 4 => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.quarticPairPolynomial) t := by
    have h := F.factorization
    rw [V.quarticPairNiltest_symbol] at h
    have H := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.quarticPairModels).filtration F.basis F.weight F.adapted h hrt
      (fun _ => by exact_mod_cast NeZero.pos N)
    dsimp only [D]
    exact H
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.quarticPairNiltest_complexity.1.mono D htest) (by simpa using h4t)
    (fun a b => (F.height a b).trans hrt) V.quarticPairPolynomial
    (piFrequency V.quarticPairFrequencies) (fun _ : Fin 4 => (N : ℝ))
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
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

theorem quartic_pair_top_agreement (x : ℝ ⊗[ℚ] V.QuarticPairAlgebra)
    (hx : x ∈ (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : QuarticReplicatedIndex, 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.quarticPairFrequency_real] at h
  linarith

theorem quartic_pair_middle_top_agreement (α : (Fin 4) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ _ : QuarticReplicatedIndex, 1) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticPairProjection 0)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
        (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α)) =
    realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticPairProjection 1)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
        (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α)) := by
  apply R.quartic_pair_top_agreement
  simpa only [hα] using R.middle_coefficients α

theorem quartic_pair_middle_bracket_agreement (α β : (Fin 4) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ _ : QuarticReplicatedIndex, 1) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.quarticPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α),
        realificationLieHom (V.quarticPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) β)⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.quarticPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) α),
        realificationLieHom (V.quarticPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 4) ℚ
            (ℝ ⊗[ℚ] V.QuarticPairAlgebra)) β)⁆ := by
  have h := R.middle_bracket_frequency α β hαβ
  rw [V.quarticPairFrequency_real] at h
  simp only [LieHom.map_lie] at h
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

theorem quartic_pair_eval_factors (n : Fin 4 → ℤ) :
    W.quarticAntisymmetric i j n * star (V.test.eval n) =
      V.quarticPairNiltest.observable (QuotientGroup.mk
        ((pi V.quarticPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun k => (n k : ℝ)) R.slow *
          (pi V.quarticPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun k => (n k : ℝ)) R.middle *
          (pi V.quarticPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun k => (n k : ℝ)) R.rational)) := by
  rw [← V.quarticPairNiltest_eval n]
  exact R.eval_niltest V.quarticPairNiltest V.quarticPairPolynomial_eq_test n

theorem quartic_pair_top_layer_invariant (z : (pi V.quarticPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : QuarticReplicatedIndex, 1)) (x : (pi V.quarticPairModels).Space) :
    V.quarticPairNiltest.observable (z • x) = V.quarticPairNiltest.observable x := by
  have htop : z ∈ (pi V.quarticPairModels).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1) :=
    (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.quarticPairNiltest_vertical z htop, R.kills_top z.coord hz]
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
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem quarticPairComparison_component_cost : p + 4 ≤ quarticPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hr : 0 ≤ raisedNiltestBudget (p + q) :=
    (add_nonneg hp hq).trans (le_raisedNiltestBudget _)
  unfold quarticPairBudget
  linarith

noncomputable def quarticPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.quarticPairModels k).Niltest (fun _ : Fin 4 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some k => ![W.quarticPairComponent a id, (W.quarticPairComponent b ![1, 0, 2, 3]).conjugate] k

theorem quarticPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.quarticPairComparisonTests a b k).ComplexityLE (quarticPairBudget p q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le)
      (V.quarticPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.quarticPairComponent_complexity a id).mono V.quarticPairComparison_component_cost
    · exact (W.quarticPairComponent_complexity b ![1, 0, 2, 3]).mono V.quarticPairComparison_component_cost

theorem quarticPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.quarticPairModels k).RealGroup)
    (hz : z ∈ (V.quarticPairModels k).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1)) (x : (V.quarticPairModels k).Space) :
    (V.quarticPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.quarticPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.quarticPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact W.quarticPairComponent_vertical a id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.quarticPairComponent_vertical b ![1, 0, 2, 3]) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

noncomputable def quarticPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.quarticPairModels).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest V.quarticPairModels (V.quarticPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ quarticPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le))
    (V.quarticPairComparisonTests_complexity a b)

theorem quarticPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.quarticPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (quarticPairBudget p q)) :=
  piNiltest_complexity V.quarticPairModels (V.quarticPairComparisonTests a b) _ _ _

theorem quarticPairComparisonNiltest_orbit (a b : Fin W.outputDim) :
    (V.quarticPairComparisonNiltest a b).orbit = V.quarticPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun k => (V.quarticPairModels k).filtration))
  funext k
  cases k with
  | none => rfl
  | some k => fin_cases k <;> rfl

theorem quarticPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.quarticPairModels).Space) :
    (V.quarticPairComparisonNiltest a b).observable x =
      W.vertical.observable a (productProjection V.quarticPairModels (some 0) x) *
        star (W.vertical.observable b (productProjection V.quarticPairModels (some 1) x)) := by
  change (∏ k, (V.quarticPairComparisonTests a b k).observable
    (productProjection V.quarticPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (W.vertical.observable a
    (productProjection V.quarticPairModels (some 0) x) *
      star (W.vertical.observable b (productProjection V.quarticPairModels (some 1) x))) = _
  exact one_mul _

theorem quarticPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.quarticPairModels).RealGroup)
    (hz : z ∈ (pi V.quarticPairModels).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1)) (x : (pi V.quarticPairModels).Space) :
    (V.quarticPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.quarticPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.quarticPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.quarticPairModels (V.quarticPairComparisonTests a b)
    V.quarticPairFrequencies _ _ _ (V.quarticPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

theorem quartic_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.quarticPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : QuarticReplicatedIndex, 1)) (x : (pi V.quarticPairModels).Space) :
    (V.quarticPairComparisonNiltest a b).observable (z • x) =
      (V.quarticPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.quarticPairModels).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1) :=
    (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.quarticPairComparisonNiltest_vertical a b z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
