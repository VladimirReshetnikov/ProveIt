/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.InducedMarkedBudget
import OAI.Combinatorics.Progressions.Estimates.CommonDependentCoveredModel
import OAI.Combinatorics.Progressions.Lattices.MarkedShiftLattice
import OAI.Combinatorics.Progressions.Lattices.NormalizedMarkedLattice

namespace OAI

section

namespace Erdos3

open Module

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_evaluation_model_with_budget (t : ℕ)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
    (hcoef : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card ι : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
      ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
        ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
          M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
          M.ComplexityLE (markedShiftModelBudget s p) ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          (∀ i j, rationalLogHeight
            (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
              markedShiftModelBudget s p) ∧
          (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤
            markedShiftModelBudget s p) ∧
          ∀ i j, rationalLogHeight (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
            markedShiftModelBudget s p := by
  classical
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  have ha : a ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t :=
    F.associatedDegree.polynomialShift_finrank_le b ω hF hω t
  have hd : d ≤ a := (markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le
  have hi : finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ≤ d :=
    (markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_le
  let R := markedShiftInputBudget s p
  let Q := markedShiftHeightBudget s p
  have hpR : p ≤ R := le_markedShiftInputBudget s hp
  have hR : 0 ≤ R := markedShiftInputBudget_nonneg s hp
  have hRQ : R ≤ Q := markedShiftInputBudget_le_height s hp
  have hQS : Q ≤ markedShiftModelBudget s p := markedShiftHeightBudget_le_model s hp
  have haR : (a : ℝ) ≤ R := (Nat.cast_le.mpr ha).trans
    (markedShift_dimension_budget s (Fintype.card ι) t hp hn ht)
  have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr hd).trans haR
  obtain ⟨m, hm, q, hq, f, hstructure, hlayers, hdirection, hphase, heval⟩ :=
    exists_markedShiftQuotient_bounded_evaluation_data F b ω hF hω v w marked hw hv hH hc hgen
      t J hJ c hcoef
  choose c' hc' using hlayers
  let M₀ := markedShiftMultidegree F v w marked hw hv t
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, hDf, hgrid, hcoords, hcomplex⟩ :=
    M₀.exists_bounded_integral_model f c' hc' hstructure l hl
  have hmR : (m : ℝ) ≤ R := (Nat.cast_le.mpr (hm.trans hi)).trans hdR
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq).trans hdR
  have hheight : (markedEvaluationHeight s (Fintype.card ι) a d m q H K : ℝ) ≤ Real.exp Q :=
    markedEvaluationHeight_le_exp s (Fintype.card ι) a d m q H K hR
      (step_le_markedShiftInputBudget s hp) (hn.trans hpR) haR hdR hmR hqR
      (hHp.trans (Real.exp_le_exp.mpr hpR)) (hKp.trans (Real.exp_le_exp.mpr hpR))
  have hgridS : (B : ℝ) ≤ Real.exp (markedShiftModelBudget s p) := by
    have hb := integral_grid_allowance_le_exp (bchIntegralDenominatorBound (s + 1)) q
      (markedEvaluationHeight s (Fintype.card ι) a d m q H K) l
      (hR.trans hRQ) (hqR.trans hRQ) hheight
      (hlp.trans (Real.exp_le_exp.mpr (hpR.trans hRQ)))
    exact (Nat.cast_le.mpr hbound).trans (hb.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hR.trans hRQ))))
  refine ⟨q, hq.trans (hd.trans ha), D, M, hMF,
    hcomplex _ (hqR.trans (hRQ.trans hQS)) hgridS
      (hheight.trans (Real.exp_le_exp.mpr hQS)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgrid]
    exact hdiv
  · simpa only [hgrid] using hcoords
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (hdirection i j) hheight).trans hQS
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (hphase i j) hheight).trans hQS
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (heval i j) hheight).trans hQS

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_compatible_marked_evaluation_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap J (b j)) i) ≤ p) →
      ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
        ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
            M.ComplexityLE ((p + C) ^ C) ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
            (∀ i j, rationalLogHeight
              (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤
              (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight
              (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
                (p + C) ^ C) ∧
            (∀ z : D.filtration.Group, z ∈ D.lattice →
              (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
            (∀ z : D.filtration.Group, z ∈ D.lattice →
              IntegralVector (markedQuotientPhase F v w marked t z.coord)) ∧
            (∀ z : D.RealGroup, z ∈ D.realLattice →
              (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
                E.realLattice) ∧
            ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∀ a : Fin t → ℤ,
                (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                  D.filtration.Group) ∈ D.lattice := by
  obtain ⟨a, ha, hmodelbudget⟩ := exists_markedShiftModel_budget s
  obtain ⟨c, hcoverC, hcover⟩ := exists_marked_evaluation_lattice s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 1 + Polynomial.C a) ^ a
  let Q₀ := (P₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + Q₀ + (Q₀ + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro I ι L _ _ _ _ r t e u F b ω hF hω v w marked hw hv J hJ E p hp hn ht hc hgen hE hcoef
  let P := (p + 1 + a) ^ a
  let Q := (P + c) ^ c
  have hp1 : p ≤ p + 1 := by linarith
  have hp1P : p + 1 ≤ P := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      p + 1 ≤ p + 1 + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + 1 + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  have hpP : p ≤ P := hp1.trans hp1P
  have hP : 0 ≤ P := hp.trans hpP
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by
    have hc1 : 1 ≤ c := by omega
    have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    calc
      P ≤ P + c := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (P + c) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hc1
  have htotal : P + Q + (Q + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa [X, P₀, Q₀, P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := by
    have hn3 : 0 ≤ (Q + 3) ^ 3 := by positivity
    linarith
  have hQC : Q ≤ (p + C) ^ C := by
    have hn3 : 0 ≤ (Q + 3) ^ 3 := by positivity
    linarith
  have hmC : (Q + 3) ^ 3 ≤ (p + C) ^ C := by linarith
  have hS : markedShiftModelBudget s (p + 1) ≤ P := hmodelbudget (p + 1) (by linarith)
  obtain ⟨q, hqdim, D, M, hMF, hM, _, hcoords, hdir, hphase, heval⟩ :=
    exists_markedShift_evaluation_model_with_budget F b ω hF hω v w marked hw hv
      (one_le_ceil_exp p) (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
      (fun i j => rationalHeightLE_ceil_exp (hgen i j)) t J hJ E.basis
      (fun i j => rationalHeightLE_ceil_exp (hcoef i j)) 1 (by decide)
      (by linarith : 0 ≤ p + 1) (hn.trans hp1) (ht.trans hp1)
      (ceil_exp_le_exp_add_one hp) (ceil_exp_le_exp_add_one hp)
      (by exact_mod_cast Real.one_le_exp (by linarith : 0 ≤ p + 1))
  have hMP : M.ComplexityLE P := hM.mono M hS
  have hdirP (i j) := (hdir i j).trans hS
  have hphaseP (i j) := (hphase i j).trans hS
  have hevalP (i j) := (heval i j).trans hS
  obtain ⟨B, Λ, hB, hin, hout, _, _, hgrid, hMQ, hmap, hintegral, hrealmap⟩ :=
    hcover F v w marked D M J hJ E hP hMP (hE.mono E hpP) (ht.trans hpP) hevalP hphaseP
  let D' := D.withLattice Λ B hB hin hout
  let M' := M.withLattice Λ B hB hin hout
  have hdirQ : ∀ i j, rationalLogHeight
      (D'.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ Q :=
    fun i j => (hdirP i j).trans hPQ
  have htQ : (t : ℝ) ≤ Q := (ht.trans hpP).trans hPQ
  obtain ⟨m, hm, hmb, hmlattice⟩ := exists_marked_direction_lattice_scale F v w marked t D'
    hQ hMQ.1.1 htQ hMQ.1.2.1 hdirQ
  refine ⟨q, hqdim, D', M', hMF, hMQ.mono M' hQC, hgrid,
    (fun i j => (hdirP i j).trans hPC), (fun i j => (hphaseP i j).trans hPC),
    (fun i j => (hevalP i j).trans hPC), hmap, hintegral, hrealmap,
    m, hm, hmb.trans (Real.exp_le_exp.mpr hmC), hmlattice⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_normalized_marked_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap J (b j)) i) ≤ p) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              (∀ i j, rationalLogHeight
                (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                  (p + C) ^ C) ∧
              (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤
                (p + C) ^ C) ∧
              (∀ i j, rationalLogHeight
                (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
                  (p + C) ^ C) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice →
                (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
              (∀ z : D.RealGroup, z ∈ D.realLattice →
                (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
                  E.realLattice) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice →
                IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
              ∀ a : Fin t → ℤ,
                (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                  D.filtration.Group) ∈ D.lattice := by
  obtain ⟨a, ha, hmodel⟩ := exists_compatible_marked_evaluation_model s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (2 * P₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro I ι L _ _ _ _ r t e u F b ω hF hω v w marked hw hv J hJ E p hp hn ht hc hgen hE hcoef
  let P := (p + a) ^ a
  let Q := (2 * P + 3) ^ 5
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpP : p ≤ P := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  have hTQ : 2 * P + 1 ≤ Q := by
    simpa only [show 2 * P + 1 + 2 = 2 * P + 3 by ring] using
      le_power_budget (by linarith : 0 ≤ 2 * P + 1) (by decide : 1 ≤ 5)
  have htotal : P + Q ≤ (p + C) ^ C := by
    simpa [X, P₀, P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := (le_add_of_nonneg_right hQ).trans htotal
  have hQC : Q ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  obtain ⟨q, hqdim, D, M, hMF, hM, _, hdir, hphase, heval, hmap, _, hrealmap,
      m, hm, hmb, hmlattice⟩ := hmodel F b ω hF hω v w marked hw hv J hJ E hp hn ht hc hgen hE hcoef
  obtain ⟨N, hN, hin, hout, _, hM'⟩ := exists_normalizedMarkedLattice_model F v w marked t D m M
    hP hM (ht.trans hpP) hm hmb hphase
  let Λ := normalizedMarkedLattice F v w marked t D m
  let D' := D.withLattice Λ N hN hin hout
  let M' := M.withLattice Λ N hN hin hout
  have hlatR : D'.realLattice ≤ D.realLattice :=
    Subgroup.map_mono (normalizedMarkedLattice_le F v w marked t D m)
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hPC), q, hqdim, D', M', hMF,
    hM'.mono M' hQC, (fun i j => (hdir i j).trans hPC), ?_,
    (fun i j => (heval i j).trans hPC), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (normalizedMarkedPhase_height F v w marked t m hm hP hmb (D.basis j) i
      (hphase i j)).trans (hTQ.trans hQC)
  · intro z hz
    exact hmap z hz.1
  · intro z hz
    exact hrealmap z (hlatR hz)
  · exact normalizedMarkedLattice_integral F v w marked t D m
  · exact fun a => normalizedMarkedLattice_direction F v w marked t D m hm a (hmlattice a)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_observable (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m e : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]
      (E : RationalFilteredNilmanifold (L ⧸ J) u e)
      (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
        (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (t : ℝ) ≤ p → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr
        (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ V : E.Space → ℂ, (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      letI := D.metricSpace
      ∃ G : D.Space → ℂ,
        LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ G ∧
        (∀ g : D.RealGroup,
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
          G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g) ∧
        ∀ x, ‖G x‖ ≤ 2 := by
  obtain ⟨A, _, hext⟩ := exists_induced_marked_observable_explicit s hs
  obtain ⟨C, hC, hbound⟩ := exists_inducedMarkedLipschitzBound_exp_bound s u A
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r d t m e F v w marked hw hv hm _ _ _ _ D J hJ _ _ _ _ E hmap p hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  let := D.metricSpace
  obtain ⟨G, hG, hGeq, hGnorm⟩ := hext F v w marked hw hv hm D J hJ E hmap
    hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  refine ⟨G, hG.weaken ?_, hGeq, hGnorm⟩
  change (inducedMarkedLipschitzBound s d u e p
    ⟨Real.exp ((p + A) ^ A), Real.exp_nonneg _⟩ : ℝ) ≤ Real.exp ((p + C) ^ C)
  exact hbound d e p ⟨Real.exp ((p + A) ^ A), Real.exp_nonneg _⟩ hp hD.1 hE.1 le_rfl

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_model (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι J L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (Q : LieIdeal ℚ L) (hQ : markedLieSpan v w marked 0 2 0 ≤ Q.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ Q))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ Q))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ Q))] [T2Space (ℝ ⊗[ℚ] (L ⧸ Q))]
      (E : RationalFilteredNilmanifold (L ⧸ Q) u e) (V : J → E.Space → ℂ) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap Q (b j)) i) ≤ p) →
      (∀ i x, ‖V i x‖ ≤ 1) →
      (letI := E.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i)) →
      ∃ (m : ℕ) (hm : 0 < m), (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              ∃ hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
                  (⟨(markedBaseEvaluation F v w marked t Q hQ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice,
                (∀ z : D.filtration.Group, z ∈ D.lattice →
                  IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
                (∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                    D.filtration.Group) ∈ D.lattice) ∧
                (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
                 letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
                   IsModuleTopology.topologicalAddGroup ℝ _
                 letI := realification_moduleTopology_t2 D.basis
                 letI := D.metricSpace
                 ∃ G : J → D.Space → ℂ,
                   (∀ i x, ‖G i x‖ ≤ 2) ∧
                   (∀ i, LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ (G i)) ∧
                   ∀ i (g : D.RealGroup),
                     (∀ j, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord j| ≤ 1 / 4) →
                     G i (QuotientGroup.mk g) =
                       markedLocalCoefficientValue F v w marked hw hv t m hm D Q hQ E hmap (V i) g) := by
  classical
  obtain ⟨A, hA, hmodel⟩ := exists_normalized_marked_model s
  obtain ⟨B, _, hext⟩ := exists_induced_marked_observable s u hs
  let P₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I ι J L _ _ _ _ r t e F b ω hF hω v w marked hw hv Q hQ _ _ _ _ E V p hp hd ht hc hgen hE hproj hVnorm hV
  let P := (p + A) ^ A
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p ≤ P := by
    apply (le_power_budget hp (a := A) (by omega)).trans
    change (p + 2) ^ A ≤ (p + A) ^ A
    exact pow_le_pow_left₀ (by linarith) (add_le_add le_rfl (by exact_mod_cast hA)) A
  have htotal : P + (P + B) ^ B ≤ (p + C) ^ C := by
    simpa [P₀, P, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hEC : (P + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  obtain ⟨m, hm, hmp, d, hdim, D, M, hMF, hM, hdir, hphase, heval, _, hmap, hint, hlat⟩ :=
    hmodel F b ω hF hω v w marked hw hv Q hQ E hp hd ht hc hgen hE hproj
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hPC), d, hdim, D, M, hMF,
    hM.mono M hPC, hmap, hint, hlat, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  let := E.metricSpace
  have hchoose (i : J) := hext F v w marked hw hv hm D Q hQ E hmap hP hM.1
    (hE.mono E hpP) (ht.trans hpP) hmp hdir hphase heval hint hlat (V i) (hVnorm i)
    ((hV i).weaken (show (⟨Real.exp p, Real.exp_nonneg p⟩ : ℝ≥0) ≤
      ⟨Real.exp P, Real.exp_nonneg P⟩ from Real.exp_le_exp.mpr hpP))
  choose G hG hGeq hGnorm using hchoose
  refine ⟨G, hGnorm, ?_, hGeq⟩
  intro i
  exact (hG i).weaken (show (⟨Real.exp ((P + B) ^ B), Real.exp_nonneg _⟩ : ℝ≥0) ≤
    ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hEC)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_induced_marked_model (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J L : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L] {r t e n : ℕ}
      (F : DegreeRankLieFiltration L s r) (A : RationalFilteredNilmanifold L s n)
      (_hFA : F.associatedDegree = A.filtration) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (Q : LieIdeal ℚ L) (hQ : markedLieSpan v w marked 0 2 0 ≤ Q.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ Q))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ Q))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ Q))] [T2Space (ℝ ⊗[ℚ] (L ⧸ Q))]
      (E : RationalFilteredNilmanifold (L ⧸ Q) u e) (V : J → E.Space → ℂ) {p : ℝ},
      0 ≤ p → A.GeometryComplexityLE p → (t : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (A.basis.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap Q (A.basis j)) i) ≤ p) →
      (∀ i x, ‖V i x‖ ≤ 1) →
      (letI := E.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i)) →
      ∃ (m : ℕ) (hm : 0 < m), (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ n * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              ∃ hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
                  (⟨(markedBaseEvaluation F v w marked t Q hQ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice,
                (∀ z : D.filtration.Group, z ∈ D.lattice →
                  IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
                (∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                    D.filtration.Group) ∈ D.lattice) ∧
                (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
                 letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
                   IsModuleTopology.topologicalAddGroup ℝ _
                 letI := realification_moduleTopology_t2 D.basis
                 letI := D.metricSpace
                 ∃ G : J → D.Space → ℂ,
                   (∀ i x, ‖G i x‖ ≤ 2) ∧
                   (∀ i, LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ (G i)) ∧
                   ∀ i (g : D.RealGroup),
                     (∀ j, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord j| ≤ 1 / 4) →
                     G i (QuotientGroup.mk g) =
                       markedLocalCoefficientValue F v w marked hw hv t m hm D Q hQ E hmap (V i) g) := by
  obtain ⟨B, _, hmodel⟩ := exists_induced_marked_model s u hs
  let X : Polynomial ℕ := Polynomial.X + (Polynomial.X + 3) ^ 11 + 1
  let P₀ := X + (X + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I J L _ _ _ r t e n F A hFA v w marked hw hv Q hQ _ _ _ _ E V p hp hA ht hgen hE hproj hVnorm hV
  obtain ⟨b, ω, N, _, _, hfil, hb, hbinv, hbc, _, _, _, _⟩ := A.exists_controlled_adapted_basis hp hA
  have hFb : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}) := by
    simpa only [hFA] using hfil
  have hω := F.associatedDegree.adaptedBasis_weight_le_step b ω hFb
  let x := p + (p + 3) ^ 11 + 1
  let P := x + (x + 2) ^ 4
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpx : p ≤ x := by dsimp [x]; linarith [pow_nonneg (by linarith : 0 ≤ p + 3) 11]
  have hpx1 : p + 1 ≤ x := by dsimp [x]; linarith [pow_nonneg (by linarith : 0 ≤ p + 3) 11]
  have hxP : x ≤ P := le_add_of_nonneg_right (by positivity)
  have hpP : p ≤ P := hpx.trans hxP
  have hpowP : (x + 2) ^ 4 ≤ P := by dsimp [P]; linarith
  have h5x : (p + 3) ^ 5 ≤ x := by
    have hh := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11)
    dsimp [x]
    linarith
  have h11P : (p + 3) ^ 11 ≤ P := by
    apply le_trans ?_ hxP
    dsimp [x]
    linarith
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ P := by
    rw [Fintype.card_fin, finrank_eq_card_basis A.basis, Fintype.card_fin]
    exact hA.1.trans hpP
  have hdimx : (Fintype.card (Fin n) : ℝ) ≤ x := by simpa only [Fintype.card_fin] using hA.1.trans hpx
  have hgenb (i j) : rationalLogHeight (b.repr (v i) j) ≤ P := by
    have hh := linearMap_coordinate_logHeight A.basis b (LinearMap.id : L →ₗ[ℚ] L) hx hdimx
      (fun a c => (hbinv a c).trans h5x) (v i) (fun a => (hgen i a).trans hpx) j
    exact hh.trans hpowP
  have hprojb (i j) : rationalLogHeight (E.basis.repr (lieQuotientMap Q (b j)) i) ≤ P := by
    exact (linearMap_coordinate_logHeight A.basis E.basis (lieQuotientMap Q).toLinearMap hx hdimx
      (fun a c => (hproj c a).trans hpx) (b j) (fun a => (hb j a).trans hpx1) i).trans hpowP
  have htotal : P + (P + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P₀, P, x, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : (P + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  let := E.metricSpace
  obtain ⟨m, hm, hmp, d, hdimd, D, M, hMF, hM, hmap, hint, hlat, hobs⟩ :=
    hmodel F b ω hFb hω v w marked hw hv Q hQ E V hP hdim (ht.trans hpP)
      (fun i j k => (hbc i j k).trans h11P) hgenb (hE.mono E hpP) hprojb hVnorm
      (fun i => (hV i).weaken (show (⟨Real.exp p, Real.exp_nonneg p⟩ : ℝ≥0) ≤
        ⟨Real.exp P, Real.exp_nonneg P⟩ from Real.exp_le_exp.mpr hpP))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbound), d, ?_, D, M, hMF,
    hM.mono M hbound, hmap, hint, hlat, ?_⟩
  · simpa only [Fintype.card_fin, finrank_eq_card_basis A.basis] using hdimd
  · let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    let := realification_moduleTopology_t2 D.basis
    let := D.metricSpace
    obtain ⟨G, hGn, hGL, hGe⟩ := hobs
    refine ⟨G, hGn, ?_, hGe⟩
    intro i
    exact (hGL i).weaken (show (⟨Real.exp ((P + B) ^ B), Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hbound)

end Erdos3

end

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

abbrev Seed := RationalTorus.Algebra 1

noncomputable def filtration : DegreeRankLieFiltration Seed 1 1 :=
  (RationalTorus.filtration 1).canonicalDegreeRank

noncomputable def generators : Fin 1 → Seed := RationalTorus.basis 1

def weights : Fin 1 → ℕ := fun _ => 1

def marked : Fin 1 → Bool := fun _ => true

theorem weight_pos (i : Fin 1) : 0 < weights i := by
  change 0 < (1 : ℕ)
  omega

theorem generator_mem (i : Fin 1) : generators i ∈ filtration.layer (weights i) 1 := by
  change generators i ∈ (RationalTorus.filtration 1).rankLayer 1 1
  rw [NilpotentLieFiltration.rankLayer_one, (RationalTorus.filtration 1).one_eq_top]
  trivial

theorem second_marked_span : markedLieSpan generators weights marked 0 2 0 ≤
    (⊥ : LieIdeal ℚ Seed).toSubmodule := by
  rw [markedLieSpan_marked_terminal filtration generators weights marked weight_pos generator_mem]
  exact bot_le

abbrev Algebra (t : ℕ) := MarkedShiftQuotient filtration generators weights marked t

noncomputable def multidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2) (Algebra t) 2 (mixedCorrelationDegree 1) :=
  markedShiftMultidegree filtration generators weights marked weight_pos generator_mem t

noncomputable def phase (t m : ℕ) := normalizedMarkedPhase filtration generators weights marked t m

noncomputable def evaluation (t : ℕ) :=
  markedBaseEvaluation filtration generators weights marked t (⊥ : LieIdeal ℚ Seed) second_marked_span 0

noncomputable def localCharacter {t d : ℕ} (m : ℕ)
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (g : D.RealGroup) : ℂ :=
  CircleFourier.character ((realifyFunctional η ((evaluation t).baseChange ℝ
    (normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D g).coord) : ℝ) :
      CircleFourier.Circle)

def Model (t : ℕ) (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (p : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
    ∃ (d : ℕ) (D : RationalFilteredNilmanifold (Algebra t) 2 d),
      d ≤ 3 * t + 2 ∧ ∃ M : D.MultidegreeStructure (mixedCorrelationDegree 1),
        M.filtration = multidegree t ∧ M.ComplexityLE p ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (phase t m z.coord)) ∧
        (∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
          filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice) ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 D.basis
         letI := D.metricSpace
         ∃ G : D.Space → ℂ, (∀ x, ‖G x‖ ≤ 2) ∧
           LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ G ∧
           ∀ g : D.RealGroup,
             (∀ i, |torusPhaseLinear (phase t m) g.coord i| ≤ 1 / 4) →
             G (QuotientGroup.mk g) = localCharacter m D η g)

theorem Model.mono {t : ℕ} {η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ}
    {p q : ℝ} (h : Model t η p) (hpq : p ≤ q) : Model t η q := by
  obtain ⟨m, hm, hmp, d, D, hd, M, hMF, hM, hint, hlat, hG⟩ := h
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpq), d, D, hd, M, hMF,
    hM.mono M hpq, hint, hlat, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  obtain ⟨G, hn, hl, he⟩ := hG
  exact ⟨G, hn, hl.weaken (Real.exp_le_exp.mpr hpq), he⟩

theorem filtration_layers (j : ℕ) : filtration.associatedDegree.layer j =
    Submodule.span ℚ (RationalTorus.basis 1 '' {i | j ≤ weights i}) := by
  simpa only [filtration, NilpotentLieFiltration.canonicalDegreeRank_associatedDegree_layer, weights]
    using RationalTorus.basis_layers 1 j

theorem structure_height {p : ℝ} (hp : 0 ≤ p) (i j k : Fin 1) :
    rationalLogHeight (lieStructureConstants (RationalTorus.basis 1) i j k) ≤ p := by
  simpa [lieStructureConstants, RationalTorus.lie_eq_zero, rationalLogHeight] using hp

theorem generator_height {p : ℝ} (hp : 0 ≤ p) (i j : Fin 1) :
    rationalLogHeight ((RationalTorus.basis 1).repr (generators i) j) ≤ p :=
  rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp)

theorem exists_model_from_seed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀
      [TopologicalSpace (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [T2Space (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)] {e : ℕ}
      (E : RationalFilteredNilmanifold (RationalTorus.BottomQuotient 1) 1 e)
      (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (V : E.Space → ℂ)
      {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap (⊥ : LieIdeal ℚ Seed)
        (RationalTorus.basis 1 j)) i) ≤ p) →
      (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      (∀ z : E.RealGroup, V (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z) →
      Model t η ((p + C) ^ C) := by
  obtain ⟨C, hC, hmodel⟩ := exists_induced_marked_model 1 1 (by decide)
  refine ⟨C, hC, ?_⟩
  intro _ _ _ _ e E η V p hp t ht hE hproj hVnorm hVLip hVeq
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  obtain ⟨m, hm, hmp, d, hdim, D, M, hMF, hM, hmap, hint, hlat, hG⟩ :=
    hmodel (t := t) filtration (RationalTorus.basis 1) weights filtration_layers (fun _ => le_rfl)
      generators weights marked weight_pos generator_mem (⊥ : LieIdeal ℚ Seed) second_marked_span
      E (fun _ : Unit => V) hp0 (by simpa only [Fintype.card_fin, Nat.cast_one] using hp)
      ht (structure_height hp0) (generator_height hp0) hE hproj
      (fun _ => hVnorm) (fun _ => hVLip)
  refine ⟨m, hm, hmp, d, D, ?_, M, hMF, hM, hint, hlat, ?_⟩
  · norm_num only [Fintype.card_fin, Nat.reduceAdd, pow_one, one_mul] at hdim
    omega
  · let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
    let := realification_moduleTopology_t2 D.basis
    let := D.metricSpace
    obtain ⟨G, hGnorm, hGLip, hGeq⟩ := hG
    refine ⟨G (), hGnorm (), hGLip (), ?_⟩
    intro g hg
    rw [hGeq () g hg, markedLocalCoefficientValue_apply, hVeq]
    rfl

theorem exists_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p →
      ∃ η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ,
        (∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0) ∧
        Model t η ((p + C) ^ C) := by
  obtain ⟨A, hA, hseed⟩ := RationalTorus.exists_bottom_quotient_character
  obtain ⟨B, _, hmodel⟩ := exists_model_from_seed
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p hp t ht
  classical
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_power_budget hp0 (a := A) (by omega)).trans
    change (p + 2) ^ A ≤ (p + A) ^ A
    exact pow_le_pow_left₀ (by linarith) (add_le_add le_rfl (by exact_mod_cast hA)) A
  have htotal : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans htotal
  have hspan : (⊥ : LieIdeal ℚ Seed).toSubmodule =
      Submodule.span ℚ (RationalTorus.basis 1 '' (∅ : Set (Fin 1))) := by simp
  let qb := NilpotentLieFiltration.quotientFinBasis (RationalTorus.basis 1)
    (⊥ : LieIdeal ℚ Seed) ∅ hspan
  let := moduleTopology ℝ (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 qb
  obtain ⟨e, E, hE, hproj, η, V, hη, hVLip, hVnorm, hVeq⟩ := hseed 1 0 hp0 (by simpa using hp)
  have hm : Model t η ((q + B) ^ B) := hmodel E η V (hp.trans hpq) t (ht.trans hpq)
    (hE.mono E hpq) (fun i j => (hproj i j).trans hpq) (fun x => (hVnorm x).le) hVLip hVeq
  exact ⟨η, hη, hm.mono hBC⟩

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasCommonInducedCorrelationFamily
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) (B : ℝ) : Prop :=
    ∃ (m : ℕ) (_hm : 0 < m), (m : ℝ) ≤ Real.exp B ∧
            ∃ d : ℕ, d ≤ n * (s + 1) * (t + 1) ^ s + t ∧
              ∃ E : RationalFilteredNilmanifold
                (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
                  D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
                ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
                  M.filtration = D.markedQuotientMultidegree t ∧ M.ComplexityLE B ∧
                  (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                     D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
                   letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                     D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                       IsModuleTopology.topologicalAddGroup ℝ _
                   letI := realification_moduleTopology_t2 E.basis
                   letI := E.metricSpace
                   ∃ G : J → E.Space → ℂ,
                     (∀ j z, ‖G j z‖ ≤ 2) ∧
                     (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
                     ∀ z, Nonempty (NativeVectorCorrelation degree N B
                       (fun ij : K × ((I × I) × (I × J)) => fun n =>
                         f z ij.1 n * star (G ij.2.2.2 (QuotientGroup.mk
                           ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
                             (correlationInput ((h z).val : ℤ) (n.val : ℤ))
                             (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
                         star (V.observable ij.2.1.1 (QuotientGroup.mk
                             (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                               (fun _ => (n.val : ℤ)) (v z))) *
                           star (V.observable ij.2.1.2 (QuotientGroup.mk
                             (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                               (fun _ => (n.val : ℤ)) (a z))))) *
                         star (mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2.2 (QuotientGroup.mk
                           (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                             (fun _ => (n.val : ℤ)) (a z)))))))

theorem hasCommonInducedCorrelationFamily_of_model
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) (B C : ℝ) (hs : 1 ≤ s)
    (hZ : 0 ≤ Z) (hI : (Fintype.card I : ℝ) ≤ Real.exp Z)
    (hJ : (Fintype.card J : ℝ) ≤ Real.exp Z)
    (hsmall : ∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4)
    (ha : ∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val))
    (hcorr : ∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun n =>
      f z ij.1 n * star (V.observable ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (n.val : ℤ)) (v z)))))))
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp B)
    (d : ℕ) (hdim : d ≤ n * (s + 1) * (t + 1) ^ s + t)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (M : E.MultidegreeStructure (mixedCorrelationDegree s))
    (hMF : M.filtration = D.markedQuotientMultidegree t) (hM : M.ComplexityLE B)
    (hmap : ∀ z : E.RealGroup, z ∈ E.realLattice →
      (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
    (hlat : ∀ b : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (b i : ℚ))⟩ : E.filtration.Group) ∈ E.lattice)
    (hobs :
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
          IsModuleTopology.topologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 E.basis
      letI := E.metricSpace
      ∃ G : J → E.Space → ℂ, (∀ j z, ‖G j z‖ ≤ 2) ∧
        (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
        ∀ j (g : E.RealGroup),
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t m) g.coord i| ≤ 1 / 4) →
          G j (QuotientGroup.mk g) = markedLocalCoefficientValue
            D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
            D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t m hm E
            (D.dependentWordIdeal 0 2 0) le_rfl Q hmap (U.observable j) g)
    (hBC : B ≤ C) (hthree : Z + Z + Z ≤ C) :
    D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f C := by
  unfold HasCommonInducedCorrelationFamily
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), d, hdim, E, M, hMF,
    hM.mono M hBC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hGe⟩ := hobs
  refine ⟨G, hGn, ?_, ?_⟩
  · intro j
    exact (hGL j).weaken (show (⟨Real.exp B, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp C, Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hBC)
  · intro z
    refine Nonempty.map (fun Cz => NativeVectorCorrelation.mono Cz hthree) ?_
    exact D.exists_local_induced_comparison_correlation
      (d := d) (e := e) (k := k) (l := n) (A := K) (I := I) (J := J)
      (degree := degree) (z := Z) (q₁ := Z) (q₂ := Z) (qV := Z) (S := S) (T := T)
      t x y u c h₀ m hm hs E A Q hφ hmap hlat
      V U G hGe (a z) (v z) (h z) (hsmall z) (ha z) (f z) hZ hZ hI hJ
      (Classical.choice (hcorr z))

theorem exists_common_induced_correlation_family (s k : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {τ K I J : Type*} [Fintype I] [Fintype J]
      {r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (t : ℕ)
      (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (_hFA : D.coefficientFreeFiltration.associatedDegree = A.filtration)
      (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
      [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
      {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
      (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
      (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
        (hL := A.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap)),
      0 ≤ Z → A.GeometryComplexityLE Z → Q.GeometryComplexityLE Z → (t : ℝ) ≤ Z →
      (∀ i j, rationalLogHeight (A.basis.repr (D.coefficientFreeGenerator i) j) ≤ Z) →
      (∀ i j, rationalLogHeight (Q.basis.repr (D.dependentQuotientMap (A.basis j)) i) ≤ Z) →
      (Fintype.card I : ℝ) ≤ Real.exp Z → (Fintype.card J : ℝ) ≤ Real.exp Z →
      ∀ (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
        (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
        (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4) →
        (∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
          ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val)) →
        ∀ f : τ → K → ZMod N → ℂ,
          (∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun n =>
            f z ij.1 n * star (V.observable ij.2 (QuotientGroup.mk
              (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) (v z))))))) →
          D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ
            x y u c h₀ h a v f ((Z + C) ^ C) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_induced_marked_model s k hs
  let P₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * Polynomial.X + P₀)
  refine ⟨C, hC, ?_⟩
  intro τ K I J _ _ r N n e degree _ b p q P Z W out H R D t A hFA Q _ _ _ _ _ _ _ _ S T V U hφ
    hZ hA hQ ht hgen hproj hI hJ x y u c h₀ h a v hsmall ha f hcorr
  let Q₀ := (Z + B) ^ B
  have hQ₀ : 0 ≤ Q₀ := by dsimp [Q₀]; positivity
  have htotal : 3 * Z + Q₀ ≤ (Z + C) ^ C := by
    simpa [P₀, Q₀, Polynomial.eval₂_pow] using hbudget Z hZ
  have hQC : Q₀ ≤ (Z + C) ^ C := by linarith
  have hthree : Z + Z + Z ≤ (Z + C) ^ C := by linarith
  let := Q.metricSpace
  obtain ⟨m, hm, hmp, d, hdim, E, M, hMF, hM, hmap, hint, hlat, hobs⟩ :=
    hmodel D.coefficientFreeFiltration A hFA D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer (D.dependentWordIdeal 0 2 0) le_rfl Q U.observable
      hZ hA ht hgen hQ hproj U.norm
      (fun j => (U.lipschitz j).weaken (show U.lipBound ≤ ⟨Real.exp Z, Real.exp_nonneg _⟩ from U.lip_bound))
  exact D.hasCommonInducedCorrelationFamily_of_model t A Q V U hφ x y u c h₀ h a v f
    Q₀ ((Z + C) ^ C) hs hZ hI hJ hsmall ha hcorr m hm hmp d hdim E M hMF hM hmap hlat hobs hQC hthree

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem HasCommonInducedCorrelationFamily.mono
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) {B C : ℝ}
    (hfamily : D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f B)
    (hBC : B ≤ C) :
    D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f C := by
  obtain ⟨m, hm, hmp, d, hdim, E, M, hMF, hM, hobs⟩ := hfamily
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), d, hdim, E, M, hMF,
    hM.mono M hBC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hobs
  refine ⟨G, hGn, ?_, ?_⟩
  · intro j
    exact (hGL j).weaken (show (⟨Real.exp B, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp C, Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hBC)
  · intro z
    exact (hcorr z).map (fun W => W.mono hBC)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (f : τ → K → ZMod N → ℂ)

def HasCoveredInducedCorrelationFamily (B : ℝ) : Prop :=
  ∃ Λ : Subgroup A.filtration.Group, Λ ≤ A.lattice ∧
    ∃ (m : ℕ) (hm : 0 < m)
      (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates A.basis Λ)
      (hout : bchSubgroupCoordinates A.basis Λ ⊆ denominatorGrid m),
      let A₀ := A.withLattice Λ m hm hin hout
      let T₀ := T.withLattice Λ m hm hin hout
      T₀.ComplexityLE B ∧
      ∃ e : ℕ, e ≤ n ∧ ∃ Q : RationalFilteredNilmanifold D.DependentQuotient s e,
        ∃ S : Q.DegreeRankStructure (r + 1),
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE B ∧
          ∃ hφ : A₀.lattice ≤ Q.lattice.comap (mapOfSteps
            (hL := A₀.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap),
            ∃ V₀ : A₀.UnitVerticalObservable (T₀.realSubgroup s (r + 1)) I B,
              V₀.frequency = V.frequency ∧
              (∀ i z, V₀.observable i (QuotientGroup.mk z) = V.observable i (QuotientGroup.mk z)) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
                 ∃ U : Q.UnitVerticalObservable (S.realSubgroup s (r + 1)) (Fin k) B,
                   D.HasCommonInducedCorrelationFamily (degree := degree)
                     t A₀ Q V₀ U hφ x y u c h₀ h a v f B ∧
                   A₀.HasLowerRankOrbitFamily T₀ (fun _ : Unit => 1)
                     (fun z ij w => mapDifferenceObservable V₀ U D.dependentQuotientMap hφ ij
                       (QuotientGroup.mk (A₀.filtration.realification.polynomialOrbitEval
                         (fun _ : Unit => 1) w (a z)))) B)

theorem exists_covered_induced_correlation_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {τ K I : Type} [Fintype I]
      {r N n degree : ℕ} [NeZero N] {b p q P Q₀ Z : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (J : D.CoefficientBases Q₀) (t : ℕ)
      (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : A.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z),
      T.filtration = D.coefficientFreeFiltration →
      V.frequency = J.freeFrequency D →
      0 ≤ Z → T.ComplexityLE Z → (t : ℝ) ≤ Z →
      (∀ i j, rationalLogHeight (A.basis.repr (D.coefficientFreeGenerator i) j) ≤ Z) →
      (Fintype.card I : ℝ) ≤ Real.exp Z →
      ∀ (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
        (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
        (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4) →
        (∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
          ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val)) →
        (∀ z, A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (a z) = 1) →
        ∀ f : τ → K → ZMod N → ℂ,
          (∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun w =>
            f z ij.1 w * star (V.observable ij.2 (QuotientGroup.mk
              (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                (fun _ => (w.val : ℤ)) (v z))))))) →
          D.HasCoveredInducedCorrelationFamily (degree := degree)
            t A T V x y u c h₀ h a v f ((Z + C) ^ C) := by
  obtain ⟨a₀, _, hcover⟩ := exists_covered_dependentQuotient_comparison s
  obtain ⟨b₀, _, hinduce⟩ := exists_common_induced_correlation_family s s hs
  let Y₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a₀) ^ a₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Y₀ + (Y₀ + Polynomial.C b₀) ^ b₀)
  refine ⟨C, hC, ?_⟩
  intro τ K I _ r N n degree _ b p q P Q₀ Z W out H R D J t A T _ _ _ _ V
    hTF hV hZ hT ht hgen hI x y u c h₀ h a v hsmall ha ha0 f hcorr
  let B := (Z + a₀) ^ a₀
  let Y := Z + B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hY : 0 ≤ Y := add_nonneg hZ hB
  have hZY : Z ≤ Y := le_add_of_nonneg_right hB
  have hBY : B ≤ Y := le_add_of_nonneg_left hZ
  have htotal : Y + (Y + b₀) ^ b₀ ≤ (Z + C) ^ C := by
    simpa [Y₀, Y, B, Polynomial.eval₂_pow] using hbudget Z hZ
  have hYC : Y ≤ (Z + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hBC : B ≤ (Z + C) ^ C := hBY.trans hYC
  have hindC : (Y + b₀) ^ b₀ ≤ (Z + C) ^ C := (le_add_of_nonneg_left hY).trans htotal
  obtain ⟨e, he, Q, S, hSF, hS, _, _, hproj, Λ, hΛ, _, _, _, _,
    m, hm, hin, hout, hT₀, hφ, V₀, hVfreq, _, hVobs, hcoeff⟩ :=
    hcover D J A T V hTF hZ hT hgen hV 1 (by decide) (by simpa using Real.one_le_exp hZ)
  let A₀ := A.withLattice Λ m hm hin hout
  let T₀ := T.withLattice Λ m hm hin hout
  refine ⟨Λ, hΛ, m, hm, hin, hout, hT₀.mono T₀ hBC, e, he, Q, S, hSF,
    hS.mono S hBC, hφ, V₀.mono hBC, hVfreq, hVobs, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨k, hk, hkB, U, _, _, hcomparison⟩ := hcoeff
  refine ⟨k, hk, hkB.trans (Real.exp_le_exp.mpr hBC), U.mono hBC, ?_, ?_⟩
  · have hFA : D.coefficientFreeFiltration.associatedDegree = A₀.filtration := by
      rw [← hTF]
      exact T.associated
    have hcorrY (z : τ) : Nonempty (NativeVectorCorrelation degree N Y
        (fun ij : K × I => fun w => f z ij.1 w *
          star ((V₀.mono hBY).observable ij.2 (QuotientGroup.mk
            (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z)))))) := by
      obtain ⟨Bz⟩ := hcorr z
      have hvalue (i : I) (w : ZMod N) :
          (V₀.mono hBY).observable i (QuotientGroup.mk
            (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z))) =
          V.observable i (QuotientGroup.mk
            (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z))) := hVobs i _
      simpa only [hvalue] using
        (show Nonempty (NativeVectorCorrelation degree N Y _) from ⟨Bz.mono hZY⟩)
    have hfamily := hinduce D t A₀ hFA Q (V₀.mono hBY) (U.mono hBY) hφ
      hY (hT₀.1.mono A₀ hBY) (hS.1.mono Q hBY) (ht.trans hZY)
      (fun i j => (hgen i j).trans hZY) (fun i j => (hproj i j).trans hBY)
      (hI.trans (Real.exp_le_exp.mpr hZY))
      (by simpa only [Fintype.card_fin] using hkB.trans (Real.exp_le_exp.mpr hBY))
      x y u c h₀ h a v hsmall ha f hcorrY
    exact HasCommonInducedCorrelationFamily.mono D t A₀ Q (V₀.mono hBY) (U.mono hBY)
      hφ x y u c h₀ h a v f hfamily hindC
  · apply ((hcomparison Unit (fun _ => 1)).mono hBC).realizeFamily
    intro z
    exact ⟨a z, ha0 z, fun _ _ => rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
