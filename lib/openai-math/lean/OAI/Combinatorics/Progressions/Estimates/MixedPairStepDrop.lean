import OAI.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
import OAI.Combinatorics.Progressions.Nilpotent.NativeMixedPairNiltest

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

structure NativeMixedPairFactorization {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
    {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
      Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.MixedPairAlgebra)) ℚ V.MixedPairAlgebra
  weight : Fin (finrank ℚ V.MixedPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.mixedPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.mixedPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.mixedPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
    (V.mixedPairNiltest.symbol basis weight adapted) r

noncomputable def NativeMixedPairFactorization.mono {n : ℕ} {p q r r' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
    {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
      Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
    (F : NativeMixedPairFactorization V r) (hrr' : r ≤ r') : NativeMixedPairFactorization V r' := by
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  exact { F with
    height := fun a b => (F.height a b).trans hrr'
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.mixedPairModels).filtration F.basis F.weight F.adapted F.factorization hrr'
      (fun _ => by exact_mod_cast NeZero.pos N) }

theorem exists_mixed_pair_step_drop (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeMixedPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : MixedReplicatedIndex (n + 1), 1) (by rw [mixedReplicated_totalDegree]; omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (mixedPairBudget p q) + (p + q) + ((n + 2 : ℕ) : ℝ)
  have hprod : 0 ≤ productNiltestBudget (mixedPairBudget p q) := by
    have hbase := V.mixedPairBudget_six_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqr : q ≤ r := by dsimp only [r]; linarith only [hp, hprod, hdim]
  have hdimr : ((n + 2 : ℕ) : ℝ) ≤ r := by dsimp only [r]; linarith only [hp, hq, hprod]
  have hTr : productNiltestBudget (mixedPairBudget p q) ≤ r := by dsimp only [r]; linarith only [hp, hq, hdim]
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, mixedPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.mixedPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htT
  let D := pi V.mixedPairModels
  let T := V.mixedPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.mixedPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 x ∈ translatedIntegerBox 0 (fun _ : Fin (n + 2) => N), T.eval x‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin (n + 2) => N) = integerBox (fun _ : Fin (n + 2) => N) := by
      ext x
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.mixedPairNiltest_bias
  have hf := hconstruct (piFrequency V.mixedPairFrequencies) V.mixedPairNiltest_vertical
    0 (fun _ : Fin (n + 2) => N) (fun _ => NeZero.pos N) (by simpa only [Fintype.card_fin] using hdimr)
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

end OAI
