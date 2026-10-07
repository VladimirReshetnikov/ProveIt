/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
import OAI.Combinatorics.Progressions.Polynomial.CanonicalPositivePolynomialSplitting

namespace OAI


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def DownsetSplittingStatement (s t a C : ℕ) : Prop :=
    ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ i, Fintype.card (M.PositivePolynomialDownsetIndex (J i)) ≤ 2 ^ t * d) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) r B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_multidegree_downset_splitting (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ DownsetSplittingStatement s t a C := by
  obtain ⟨b, _, hnormalize⟩ := exists_controlled_multidegree_basepoint_normalization s
  obtain ⟨c, _, hsplit⟩ := exists_canonical_positivePolynomial_splitting t a
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ d D bound M J _ hJ _ _ _ _
    p ht hM hα hcover g epsilon hepsilon hscale hI
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let r := p + (p + b) ^ b + 2
  have hnormal_nonneg : 0 ≤ (p + b) ^ b := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith only [hnormal_nonneg]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + (r + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + c) ^ c := by positivity
  have hr_cost : r ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  have hpower_cost : (r + c) ^ c ≤ (p + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨ε, A, hA, hLip, g', hg', heval⟩ := hnormalize M hp hM.1 g
  have hshift : p + 2 ≤ r + 2 := by linarith only [hpr]
  have hscale_r : 1 / epsilon ≤ Real.exp ((r + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift a))
  obtain ⟨B, hB, hstable, hresult⟩ :=
    hsplit (I := I) (α := α) (σ := σ) (L := L) M J hJ r ht (hM.mono M hpr) (hα.trans hshift) hcover g' hg'
      epsilon hepsilon hscale_r (hI.trans (Real.exp_le_exp.mpr hpr))
  obtain ⟨hE, h, hh, hresult⟩ := hresult
  obtain ⟨n, hn, hnb, hcount, T, hresult⟩ := hresult
  obtain ⟨hTnorm, hTunit, hT, hTorbit, happrox⟩ := hresult
  have hdim (i) : Fintype.card (M.PositivePolynomialDownsetIndex (J i)) ≤ 2 ^ t * d := by
    apply (M.positivePolynomialDownsetIndex_card_le (J i)).trans
    simpa only [ht] using M.positivePolynomialBasisIndex_card_le r
  refine ⟨r, hpr, hr_cost, B, hB, hstable, fun i => (hE i).mono _ hpower_cost,
    hdim, h, hh, n, hn, fun i => (hnb i).trans (Real.exp_le_exp.mpr hpower_cost),
    hcount.trans (Real.exp_le_exp.mpr hpower_cost), T, hTnorm, hTunit,
    fun i j => (hT i j).mono hpower_cost, hTorbit, ?_⟩
  let := D.metricSpace
  have htranslated_bound : Real.exp p * (A : ℝ) ≤ Real.exp r := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + b) ^ b) :=
        mul_le_mul_of_nonneg_left hA (Real.exp_nonneg _)
      _ = Real.exp (p + (p + b) ^ b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [r]; exact le_add_of_nonneg_right (by norm_num))
  exact vector_approximation_precompose (I := I) (J := ∀ i, Fin (n i))
    (S := σ → ℤ) (X := D.Space) (A := A) (p := p) (q := r)
    (B := Real.exp ((r + c) ^ c)) (B' := Real.exp ((p + C) ^ C))
    (epsilon := epsilon) (fun y : D.Space => ε • y)
    (fun x => QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g'))
    (fun x => QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))
    (fun j x => ∏ i, (T i (j i)).eval x) hLip heval htranslated_bound
    (Real.exp_le_exp.mpr hpower_cost) happrox

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def TwoDownsetSplittingStatement (s t a C : ℕ) : Prop :=
    ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : Bool → Set (σ →₀ ℕ))
      [∀ b, DecidablePred (· ∈ J b)] (hJ : ∀ b, IsLowerSet (J b))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (∀ c, c ≠ 0 → c ∉ J false ∪ J true → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ b, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
        (∀ b, (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ b, Fintype.card (M.PositivePolynomialDownsetIndex (J b)) ≤ 2 ^ t * d) ∧
        (∀ b c, c ∉ J b →
          (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).filtration.layer (fun i => c i) = ⊥) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
            ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ (A : Fin N → (E false).Niltest (fun _ : σ => 1))
                (B' : Fin N → (E true).Niltest (fun _ : σ => 1)),
                (∀ j, (A j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
                (∀ j, (A j).ComplexityLE ((p + C) ^ C)) ∧
                (∀ j, (B' j).ComplexityLE ((p + C) ^ C)) ∧
                (∀ j, (A j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h)) ∧
                (∀ j, (B' j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h)) ∧
                ∀ x, ‖u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) -
                  ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def TwoDownsetCorrelationStatement (s t C : ℕ) : Prop :=
    ∀ {σ Ω L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : Bool → Set (σ →₀ ℕ))
      [∀ b, DecidablePred (· ∈ J b)] (hJ : ∀ b, IsLowerSet (J b))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (∀ c, c ≠ 0 → c ∉ J false ∪ J true → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (g : M.filtration.realification.PolynomialOrbit) (u : D.Space → ℂ) (ell : ℝ≥0),
      (ell : ℝ) ≤ Real.exp p → (letI := D.metricSpace; LipschitzWith ell u) →
      (∀ x, ‖u x‖ ≤ 1) →
      ∀ (Q : Finset Ω) (x : Ω → σ → ℤ) (f : Ω → ℂ), Q.Nonempty →
      (∀ z ∈ Q, ‖f z‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation Q f
        (fun z => u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (x z) g)))‖ →
      letI : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ b, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
        (∀ b, (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ b, Fintype.card (M.PositivePolynomialDownsetIndex (J b)) ≤ 2 ^ t * d) ∧
        (∀ b c, c ∉ J b →
          (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).filtration.layer (fun i => c i) = ⊥) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ (A : (E false).Niltest (fun _ : σ => 1)) (B' : (E true).Niltest (fun _ : σ => 1)),
            A.normBound ≤ 1 ∧ B'.normBound ≤ 1 ∧
            A.ComplexityLE ((p + C) ^ C) ∧ B'.ComplexityLE ((p + C) ^ C) ∧
            A.orbit = (M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
              (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h) ∧
            B'.orbit = (M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
              (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h) ∧
            Real.exp (-((p + C) ^ C)) ≤ ‖finiteCorrelation Q f (fun z => A.eval (x z) * B'.eval (x z))‖

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def TwoDownsetPrecisionStatement (s t C : ℕ) : Prop :=
    ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : Bool → Set (σ →₀ ℕ))
      [∀ b, DecidablePred (· ∈ J b)] (hJ : ∀ b, IsLowerSet (J b))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (∀ c, c ≠ 0 → c ∉ J false ∪ J true → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon →
      let q := p + |Real.log epsilon|
      letI : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ b, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (q + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
        (∀ b, (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).ComplexityLE ((q + C) ^ C)) ∧
        (∀ b, Fintype.card (M.PositivePolynomialDownsetIndex (J b)) ≤ 2 ^ t * d) ∧
        (∀ b c, c ∉ J b →
          (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).filtration.layer (fun i => c i) = ⊥) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
            ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
              ∃ (A : Fin N → (E false).Niltest (fun _ : σ => 1))
                (B' : Fin N → (E true).Niltest (fun _ : σ => 1)),
                (∀ j, (A j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
                (∀ j, (A j).ComplexityLE ((q + C) ^ C)) ∧
                (∀ j, (B' j).ComplexityLE ((q + C) ^ C)) ∧
                (∀ j, (A j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h)) ∧
                (∀ j, (B' j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h)) ∧
                ∀ x, ‖u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) -
                  ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct

theorem exists_two_downset_splitting (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoDownsetSplittingStatement s t a C := by
  obtain ⟨b, _, hsplit⟩ := exists_multidegree_downset_splitting s t a
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d D bound M J _ hJ _ _ _ _ p ht hM hcover g epsilon hepsilon hscale
  classical
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hcost : (p + b) ^ b + 1 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hcost' : (p + b) ^ b ≤ (p + C) ^ C := by linarith only [hcost]
  have hfamily : (Fintype.card Bool : ℝ) ≤ p + 2 := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith only [hp]
  have hsupport : ∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥ := by
    intro c hc hout
    apply hcover c hc
    rintro (hl | hr)
    · exact hout false hl
    · exact hout true hr
  obtain ⟨r, hpr, hr, B, hB, hstable, hresult⟩ :=
    hsplit (I := Unit) (α := Bool) (σ := σ) (L := L) M J hJ p ht hM hfamily hsupport
      g epsilon hepsilon hscale (by simpa using Real.one_le_exp hp)
  obtain ⟨hE, hdim, h, hh, hresult⟩ := hresult
  obtain ⟨n, hn, hnb, hcount, T, hresult⟩ := hresult
  obtain ⟨hTnorm, hTunit, hT, hTorbit, happrox⟩ := hresult
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) r B hB hstable
  have hterminal : ∀ i c, c ∉ J i →
      (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).filtration.layer
        (fun j => c j) = ⊥ := by
    intro i c hc
    exact M.filtration.positivePolynomialDownsetQuotient_terminal (J i) (hJ i) c hc
  refine ⟨r, hpr, hr.trans hcost', B, hB, hstable,
    fun i => (hE i).mono _ hcost', hdim, hterminal, h, hh, ?_⟩
  intro u ell hell hu hub
  let coefficients := happrox (fun _ : Unit => u) ell hell (fun _ => hu) (fun _ => hub)
  let coeff := coefficients.choose
  have hcoeff := coefficients.choose_spec.1
  have herr := coefficients.choose_spec.2.2
  have hscalar := scalar_error_le_of_vector_error (I := Unit) (J := ∀ i, Fin (n i))
    (S := σ → ℤ) (epsilon := epsilon)
    (fun _ : Unit => fun x => u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
    (fun j x => ∏ i, (T i (j i)).eval x) coeff herr ()
  let : Nonempty (∀ i, Fin (n i)) := ⟨fun i => ⟨0, hn i⟩⟩
  let pairSum := exists_bounded_niltest_pair_sum (J := ∀ i, Fin (n i)) (σ := σ)
      (p := (p + b) ^ b) (E false) (E true) (fun _ : σ => 1)
      ((M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
        (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h))
      ((M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
        (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h))
      (fun j => T false (j false)) (fun j => T true (j true)) (fun j => coeff j ())
      (fun j => (hTnorm false (j false)).le) (fun j => (hTnorm true (j true)).le)
      (fun j => hT false (j false)) (fun j => hT true (j true))
      (fun j => hTorbit false (j false)) (fun j => hTorbit true (j true)) (fun j => hcoeff j ())
  let N := pairSum.choose
  have hNpos := pairSum.choose_spec.1
  have hN : N = 2 * Fintype.card (∀ i, Fin (n i)) := pairSum.choose_spec.2.1
  let leftTests := pairSum.choose_spec.2.2
  let A := leftTests.choose
  let rightTests := leftTests.choose_spec
  let B' := rightTests.choose
  have hdata := rightTests.choose_spec
  have hAnorm := hdata.1
  have hBnorm := hdata.2.1
  have hA := hdata.2.2.1
  have hB' := hdata.2.2.2.1
  have hAg := hdata.2.2.2.2.1
  have hBg := hdata.2.2.2.2.2.1
  have heval := hdata.2.2.2.2.2.2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hNbound : (N : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [hN, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ 2 * Real.exp ((p + b) ^ b) := mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = Real.exp ((p + b) ^ b) * 2 := mul_comm _ _
      _ ≤ Real.exp ((p + b) ^ b) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = Real.exp ((p + b) ^ b + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  refine ⟨N, hNpos, hNbound, A, B', hAnorm, hBnorm,
    fun j => (hA j).mono hcost', fun j => (hB' j).mono hcost', hAg, hBg, ?_⟩
  intro x
  rw [heval x]
  convert hscalar x using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.prod_bool, mul_comm ((T true (j true)).eval x) ((T false (j false)).eval x)]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_two_downset_correlation (s t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoDownsetCorrelationStatement s t C := by
  obtain ⟨b, _, hsplit⟩ := exists_two_downset_splitting s t 1
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ Ω L _ _ _ _ d D bound M J _ hJ _ _ _ _ p ht hM hcover g u ell hell hu hub
    Q x f hQ hf hcorr
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hcost : p + (p + b) ^ b + 1 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hcost' : (p + b) ^ b ≤ (p + C) ^ C := by linarith only [hcost, hp]
  have hscale : 1 / Real.exp (-p - 1) ≤ Real.exp ((p + 2) ^ 1) := by
    rw [one_div, ← Real.exp_neg, pow_one]
    exact Real.exp_le_exp.mpr (by linarith only)
  obtain ⟨r, hpr, hr, B, hB, hstable, hresult⟩ :=
    hsplit (σ := σ) (L := L) M J hJ p ht hM hcover g (Real.exp (-p - 1))
      (Real.exp_pos _) hscale
  obtain ⟨hE, hdim, hterminal, h, hh, happrox⟩ := hresult
  classical
  let approximation := happrox u ell hell hu hub
  let N := approximation.choose
  have hNbound := approximation.choose_spec.2.1
  let leftTests := approximation.choose_spec.2.2
  let A := leftTests.choose
  let rightTests := leftTests.choose_spec
  let B' := rightTests.choose
  have props := rightTests.choose_spec
  have hAnorm := props.1
  have hBnorm := props.2.1
  have hA := props.2.2.1
  have hB' := props.2.2.2.1
  have hAg := props.2.2.2.2.1
  have hBg := props.2.2.2.2.2.1
  have herr := props.2.2.2.2.2.2
  have herror : ∀ z ∈ Q, ‖(∑ j, (A j).eval (x z) * (B' j).eval (x z)) -
      u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (x z) g))‖ ≤ Real.exp (-p) / 2 := by
    intro z _
    rw [norm_sub_rev]
    exact (herr (x z)).trans (exp_sub_one_le_half_exp (-p))
  let summand := exists_correlating_summand (J := Fin N) hQ f
    (fun z => u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (x z) g)))
    (fun j z => (A j).eval (x z) * (B' j).eval (x z))
    (Real.exp_pos (-p)) (Real.exp_pos ((p + b) ^ b))
    (by simpa only [Fintype.card_fin] using hNbound) hf herror hcorr
  let j := summand.choose
  have hj := summand.choose_spec
  have hcorrbound : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-p) / (2 * Real.exp ((p + b) ^ b)) := by
    calc
      _ ≤ Real.exp (-(p + (p + b) ^ b) - 1) :=
        Real.exp_le_exp.mpr (by linarith only [hcost])
      _ ≤ Real.exp (-(p + (p + b) ^ b)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by
        rw [show -(p + (p + b) ^ b) = -p - (p + b) ^ b by ring, Real.exp_sub]
        ring
  exact ⟨r, hpr, hr.trans hcost', B, hB, hstable, fun i => (hE i).mono _ hcost',
    hdim, hterminal, h, hh, A j, B' j, hAnorm j, hBnorm j,
    (hA j).mono hcost', (hB' j).mono hcost', hAg j, hBg j, hcorrbound.trans hj⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_two_downset_precision (s t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoDownsetPrecisionStatement s t C := by
  obtain ⟨b, _, hsplit⟩ := exists_two_downset_splitting s t 1
  let P : Polynomial ℕ := (Polynomial.X + 2 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d D bound M J _ hJ _ _ _ _ p ht hM hcover g epsilon hepsilon
  let q := p + |Real.log epsilon|
  let R := q + 2
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpR : p ≤ R := by dsimp [R, q]; linarith only [abs_nonneg (Real.log epsilon)]
  have hcost : (R + b) ^ b ≤ (q + C) ^ C := by
    simpa [P, R, Polynomial.eval₂_pow] using hbudget q hq
  have hscale : 1 / epsilon ≤ Real.exp ((R + 2) ^ 1) := by
    rw [pow_one]
    calc
      1 / epsilon = Real.exp (-Real.log epsilon) := by
        rw [Real.exp_neg, Real.exp_log hepsilon]
        exact one_div epsilon
      _ ≤ Real.exp (R + 2) := by
        apply Real.exp_le_exp.mpr
        dsimp [R, q]
        linarith only [hp, neg_le_abs (Real.log epsilon)]
  obtain ⟨r, hRr, hr, B, hB, hstable, hresult⟩ :=
    hsplit (σ := σ) (L := L) M J hJ R ht (hM.mono M hpR) hcover g epsilon hepsilon hscale
  obtain ⟨hE, hdim, hterminal, h, hh, happrox⟩ := hresult
  refine ⟨r, hpR.trans hRr, hr.trans hcost, B, hB, hstable,
    fun i => (hE i).mono _ hcost, hdim, hterminal, h, hh, ?_⟩
  intro u ell hell hu hub
  obtain ⟨N, hNpos, hNbound, A, B', hAnorm, hBnorm, hA, hB', hAg, hBg, herr⟩ :=
    happrox u ell (hell.trans (Real.exp_le_exp.mpr hpR)) hu hub
  exact ⟨N, hNpos, hNbound.trans (Real.exp_le_exp.mpr hcost), A, B', hAnorm, hBnorm,
    fun j => (hA j).mono hcost, fun j => (hB' j).mono hcost, hAg, hBg, herr⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end OAI
