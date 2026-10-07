import OAI.Combinatorics.Progressions.Nilpotent.CubicPairNiltest
import OAI.Combinatorics.Progressions.Polynomial.AntisymmetricPairPolynomial

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_intrinsic_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
      ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (e '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
        ∀ η : L →ₗ[ℚ] ℚ,
          (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
            T.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
          D.filtration.ControlledSymbolFactorization e ω hF η (fun i => (lengths i : ℝ))
            (T.symbol e ω hF) ((p + C) ^ C) := by
  cases s with
  | zero => omega
  | succ s =>
    have hs' : 1 ≤ s := by omega
    obtain ⟨c, _, hI⟩ := exists_translated_step_drop s hs'
    obtain ⟨C, hC, hstep⟩ := exists_biased_chosen_basis_step_drop s c hI
    refine ⟨C, hC, ?_⟩
    intro σ L _ _ _ _ d _ _ _ _ D p hp T hT
    obtain ⟨a, v, _grid, _hv, _central, hA, _rest⟩ := D.exists_controlled_adapted_basis hp hT.1
    obtain ⟨τS, hSA, hSM, hST⟩ := exists_real_module_topology
      (D.filtration.squareFinBasis a v (hA 2))
    let : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := τS
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSA
    let : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSM
    let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hST
    obtain ⟨τQ, hQA, hQM, hQT⟩ := exists_real_module_topology
      (D.filtration.reducedSquareBasis a v hA)
    let : TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := τQ
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQA
    let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQM
    let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQT
    obtain ⟨e, ω, hF, _N, _hN, _hin, _hout, he, _geometry, hconstruct⟩ :=
      hstep hs' D p hp T hT
    obtain ⟨g, hg⟩ := D.filtration.nativePolynomialOrbit_surjective
      (fun _ : σ => 1) e ω hF T.orbit
    refine ⟨e, ω, hF, he, ?_⟩
    intro η hvert origin lengths hlengths hσ hlarge hbias
    have hresult := hconstruct g hg η hvert origin lengths hlengths hσ hlarge hbias
    rw [← T.symbol_of_native e ω hF g hg] at hresult
    exact hresult

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

structure NativeAntisymmetricPairFactorization {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.AntisymmetricPairAlgebra)) ℚ V.AntisymmetricPairAlgebra
  weight : Fin (finrank ℚ V.AntisymmetricPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.antisymmetricPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.antisymmetricPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.antisymmetricPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
    (V.antisymmetricPairNiltest.symbol basis weight adapted) r

noncomputable def NativeAntisymmetricPairFactorization.mono {p q r r' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
    (F : NativeAntisymmetricPairFactorization V r) (hrr' : r ≤ r') :
    NativeAntisymmetricPairFactorization V r' := by
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  exact { F with
    height := fun a b => (F.height a b).trans hrr'
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.antisymmetricPairModels).filtration F.basis F.weight F.adapted F.factorization hrr'
      (fun _ => by exact_mod_cast NeZero.pos N) }

theorem exists_antisymmetric_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeAntisymmetricPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ k, mixedCorrelationDegree 1 k)
    (by decide)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + (X + 2) ^ 2 + 3) + 4
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (antisymmetricPairBudget p q) + (p + q) + 2
  have hprod : 0 ≤ productNiltestBudget (antisymmetricPairBudget p q) := by
    have hbase := V.antisymmetricPairBudget_four_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have h2r : 2 ≤ r := by dsimp [r]; linarith
  have hTr : productNiltestBudget (antisymmetricPairBudget p q) ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, antisymmetricPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.antisymmetricPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htT
  let D := pi V.antisymmetricPairModels
  let T := V.antisymmetricPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.antisymmetricPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 2 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 2 => N) = integerBox (fun _ : Fin 2 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.antisymmetricPairNiltest_bias
  have hf := hconstruct (piFrequency V.antisymmetricPairFrequencies)
    V.antisymmetricPairNiltest_vertical 0 (fun _ : Fin 2 => N)
    (fun _ => NeZero.pos N) (by simpa using h2r)
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

structure NativeCubicPairFactorization {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
    {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
    (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
      Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.CubicPairAlgebra)) ℚ V.CubicPairAlgebra
  weight : Fin (finrank ℚ V.CubicPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.cubicPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.cubicPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.cubicPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.cubicPairFrequencies) (fun _ : Fin 3 => (N : ℝ))
    (V.cubicPairNiltest.symbol basis weight adapted) r

noncomputable def NativeCubicPairFactorization.mono {p q r r' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
    {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
    {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
      Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
    (F : NativeCubicPairFactorization V r) (hrr' : r ≤ r') : NativeCubicPairFactorization V r' := by
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  exact { F with
    height := fun a b => (F.height a b).trans hrr'
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.cubicPairModels).filtration F.basis F.weight F.adapted F.factorization hrr'
      (fun _ => by exact_mod_cast NeZero.pos N) }

theorem exists_cubic_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCubicPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : CubicReplicatedIndex, 1) (by decide)
  let X : Polynomial ℕ := Polynomial.X
  let Q := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j shift V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (cubicPairBudget p q) + (p + q) + 3
  have hprod : 0 ≤ productNiltestBudget (cubicPairBudget p q) := by
    have hbase := V.cubicPairBudget_six_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hqr : q ≤ r := by dsimp only [r]; linarith only [hp, hprod]
  have h3r : 3 ≤ r := by dsimp only [r]; linarith only [hp, hq, hprod]
  have hTr : productNiltestBudget (cubicPairBudget p q) ≤ r := by dsimp only [r]; linarith only [hp, hq]
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, cubicPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.cubicPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra) := htT
  let D := pi V.cubicPairModels
  let T := V.cubicPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.cubicPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 3 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 3 => N) = integerBox (fun _ : Fin 3 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.cubicPairNiltest_bias
  have hf := hconstruct (piFrequency V.cubicPairFrequencies) V.cubicPairNiltest_vertical
    0 (fun _ : Fin 3 => N) (fun _ => NeZero.pos N) (by simpa using h3r)
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

theorem exists_finite_product_vertical_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (T : ∀ i, (D i).Niltest (fun _ : σ => 1)) {p : ℝ} (hp : 0 ≤ p)
      (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (∀ i, L i))) ℚ (∀ i, L i))
        (ω : Fin (finrank ℚ (∀ i, L i)) → ℕ)
        (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi D).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ eta : ∀ i, L i →ₗ[ℚ] ℚ,
          (∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
            (T i).observable (z • x) = CircleFourier.character
              ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
                (T i).observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, ∏ i, (T i).eval x‖ →
          (pi D).filtration.ControlledSymbolFactorization b ω hF (piFrequency eta)
            (fun i => (lengths i : ℝ)) ((piNiltest D T hp hι hT).symbol b ω hF)
            ((p + C) ^ C) := by
  obtain ⟨a, _ha, hstep⟩ := exists_intrinsic_step_drop s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + 1 + (Q + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D T p hp hι hT
  let q := productNiltestBudget p + p + 2
  have hprod : 0 ≤ productNiltestBudget p := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hTq : productNiltestBudget p ≤ q := by dsimp [q]; linarith
  have hcost : q + 1 + (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hheight : q + 1 ≤ (p + C) ^ C := by
    have : 0 ≤ (q + a) ^ a := by positivity
    linarith
  have hfactor : (q + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (pi D) hq (piNiltest D T hp hι hT)
      ((piNiltest_complexity D T hp hι hT).mono hTq)
  refine ⟨b, ω, hF, fun i j => (hb i j).trans hheight, ?_⟩
  intro eta hvert origin lengths hlength hσ hlarge hbias
  have hpair : Real.exp (-q) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths, (piNiltest D T hp hι hT).eval x‖ := by
    simp_rw [piNiltest_eval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
  have hf := hconstruct (piFrequency eta) (piNiltest_vertical D T eta hp hι hT hvert)
    origin lengths hlength (hσ.trans hpq)
    (fun i => (Real.exp_le_exp.mpr hfactor).trans (hlarge i)) hpair
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi D).filtration b ω hF hf hfactor (fun i => by exact_mod_cast hlength i)

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

theorem exists_antisymmetric_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (_F : NativeAntisymmetricPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ k, mixedCorrelationDegree 1 k)
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
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
  have h2t : 2 ≤ t := by dsimp [t]; linarith
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
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.antisymmetricPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.antisymmetricPairPolynomial) t := by
    have h := F.factorization
    rw [V.antisymmetricPairNiltest_symbol] at h
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration F.basis F.weight F.adapted h hrt (fun _ => by exact_mod_cast NeZero.pos N)
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.antisymmetricPairNiltest_complexity.1.mono D htest) (by simpa using h2t)
    (fun a b => (F.height a b).trans hrt) V.antisymmetricPairPolynomial
    (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
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
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem pair_top_agreement (x : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
    (hx : x ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.antisymmetricPairFrequency_real] at h
  linarith

theorem pair_middle_top_agreement (α : (Fin 2) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ k, mixedCorrelationDegree 1 k) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 2) ℚ
        (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) α)) =
    realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1)
      (coefficients (R.middle.coord : VectorPolynomial (Fin 2) ℚ
        (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) α)) := by
  apply R.pair_top_agreement
  simpa only [hα] using R.middle_coefficients α

theorem pair_middle_bracket_agreement (α β : (Fin 2) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ k, mixedCorrelationDegree 1 k) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.antisymmetricPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 2) ℚ
            (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) α),
        realificationLieHom (V.antisymmetricPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 2) ℚ
            (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) β)⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.antisymmetricPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 2) ℚ
            (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) α),
        realificationLieHom (V.antisymmetricPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin 2) ℚ
            (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) β)⁆ := by
  have h := R.middle_bracket_frequency α β hαβ
  rw [V.antisymmetricPairFrequency_real] at h
  simp only [LieHom.map_lie] at h
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pair_eval_factors (n : Fin 2 → ℤ) :
    W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) =
      V.antisymmetricPairNiltest.observable (QuotientGroup.mk
        ((pi V.antisymmetricPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 2 => 1) (fun k => (n k : ℝ)) R.slow *
          (pi V.antisymmetricPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 2 => 1) (fun k => (n k : ℝ)) R.middle *
          (pi V.antisymmetricPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 2 => 1) (fun k => (n k : ℝ)) R.rational)) := by
  rw [← V.antisymmetricPairNiltest_eval n]
  exact R.eval_niltest V.antisymmetricPairNiltest V.antisymmetricPairPolynomial_eq_test n

theorem pair_top_layer_invariant (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) (x : (pi V.antisymmetricPairModels).Space) :
    V.antisymmetricPairNiltest.observable (z • x) = V.antisymmetricPairNiltest.observable x := by
  have htop : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ k, mixedCorrelationDegree 1 k) :=
    (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.antisymmetricPairNiltest_vertical z htop, R.kills_top z.coord hz]
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
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def pairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.antisymmetricPairModels k).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some k => ![(W.pairComponent a 0 1).conjugate, W.pairComponent b 1 0] k

theorem pairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.pairComparisonTests a b k).ComplexityLE (antisymmetricPairBudget p q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
      (V.antisymmetricPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact V.antisymmetricPairTests_complexity (some 0)
    · exact V.antisymmetricPairTests_complexity (some 1)

theorem pairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.antisymmetricPairModels k).RealGroup)
    (hz : z ∈ (V.antisymmetricPairModels k).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (V.antisymmetricPairModels k).Space) :
    (V.pairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.antisymmetricPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.pairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.pairComponent_vertical a 0 1) z hz x
    · exact W.pairComponent_vertical b 1 0 z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def pairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels (V.pairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    (V.pairComparisonTests_complexity a b)

theorem pairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.pairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels (V.pairComparisonTests a b) _ _ _

theorem pairComparisonNiltest_orbit (a b : Fin W.outputDim) :
    (V.pairComparisonNiltest a b).orbit = V.antisymmetricPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun k => (V.antisymmetricPairModels k).filtration))
  funext k
  cases k with
  | none => rfl
  | some k => fin_cases k <;> rfl

theorem pairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable x =
      star (W.vertical.observable a (productProjection V.antisymmetricPairModels (some 0) x)) *
        W.vertical.observable b (productProjection V.antisymmetricPairModels (some 1) x) := by
  change (∏ k, (V.pairComparisonTests a b k).observable
    (productProjection V.antisymmetricPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (star (W.vertical.observable a
    (productProjection V.antisymmetricPairModels (some 0) x)) *
      W.vertical.observable b (productProjection V.antisymmetricPairModels (some 1) x)) = _
  exact one_mul _

theorem pairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.antisymmetricPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.pairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.antisymmetricPairModels (V.pairComparisonTests a b)
    V.antisymmetricPairFrequencies _ _ _ (V.pairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

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

theorem pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable (z • x) =
      (V.pairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ k, mixedCorrelationDegree 1 k) :=
    (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.pairComparisonNiltest_vertical a b z htop, R.kills_top z.coord hz]
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
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairFrozenVector (k : Fin 2)
    (a b : (pi V.antisymmetricPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.antisymmetricPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

theorem pairFrozenVector_unit (k : Fin 2)
    (a b : (pi V.antisymmetricPairModels).RealGroup) (x : Fin 2 → ℤ) :
    ∑ out, ‖R.pairFrozenVector k a b out x‖ ^ 2 = 1 :=
  W.vertical.unit _

def HasPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.antisymmetricPairModels).RealGroup,
      (∀ i, |((pi V.antisymmetricPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.antisymmetricPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
      NativeIntegerVectorEquivalence 1 b (R.pairFrozenVector 0 a r) (R.pairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

theorem exists_antisymmetric_pair_frozen_equivalence :
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
      [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasPairFrozenEquivalence u ((p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion 1
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R _ _ _ _ hr hu m hm hmb left right hleft hright
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
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpt.trans htC))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.antisymmetricPairModels) (R.mono hrt hN)
    (V.pairComparisonNiltest out₀ out₁) ht ((V.pairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.pair_comparison_invariant out₀ out₁) m hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((p + q + r + u + C) ^ C) (fun x =>
        star ((V.pairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x))))) :=
    ⟨F.conjugate.mono hcost⟩
  simpa only [V.pairComparisonNiltest_observable, star_mul, star_star,
    NativePolynomialOrbitFactors.pairFrozenVector, mul_comm] using hF

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  Nonempty (NativeAntisymmetricPairFactorization V ((p + C) ^ C)) := by
  obtain ⟨A, _, hcorr⟩ := exists_quadratic_pair_correlator
  obtain ⟨B, _, hdrop⟩ := exists_antisymmetric_pair_step_drop
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (2 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (2 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, hq, hqt, H, hH, hdense, M, i, hderiv, i', j', ⟨V⟩⟩ := hcorr hp f hf hG
  have hpair : (q + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + t + B ≤ 2 * t + B
    linarith
  obtain ⟨F⟩ := hdrop V ((Real.exp_le_exp.mpr hpair).trans hN)
  exact ⟨q, t, hq, hqt.trans htC, ht, htC, H, hH, hdense, M, i, hderiv, i', j', V,
    ⟨F.mono hpair⟩⟩

end Erdos3

end

end OAI
