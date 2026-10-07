/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
import OAI.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_slow_polynomial_metric_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d n H : ℕ) (p M : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 ≤ M → M ≤ Real.exp ((p + 2) ^ r) →
      ∃ B : ℝ≥0, 1 ≤ B ∧
        ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M ≤ B ∧
        (bchBoxMetricConstant s d H B : ℝ) *
          (((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M * n * s) ≤
            Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r
  obtain ⟨a, _, hP⟩ := exists_natPolynomial_eval_budget P
  obtain ⟨b, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  let Q := (X + Polynomial.C a + Polynomial.C b) ^ b + P + X + Polynomial.C s
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro d n H p M hp hd hn hH hM hMp
  let q : ℝ := s * (p + 1) + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let B : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp hq
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hAM : ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M ≤ Real.exp q := by
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul (mul_le_mul (Real.add_one_le_exp (s : ℝ))
          (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          hMp hM (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [q]; ring
  have hpA : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hBa : (B : ℝ) ≤ Real.exp (((p + a) + 2) ^ a) := by
    apply Real.exp_le_exp.mpr
    have h := hP p hp
    have h' : q ≤ (p + a) ^ a := by simpa [P, X, q, Polynomial.eval₂_pow] using h
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hBC : (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + a + b) ^ b) :=
    hbox d H B (p + a) (hp.trans hpA) (hd.trans hpA)
      (hH.trans (Real.exp_le_exp.mpr hpA)) hBa
  have hnexp : (n : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hsexp : (s : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp (s : ℝ)]
  refine ⟨B, hB, hAM, ?_⟩
  calc
    _ ≤ Real.exp ((p + a + b) ^ b) * (Real.exp q * Real.exp p * Real.exp s) := by
      apply mul_le_mul hBC
        (mul_le_mul (mul_le_mul hAM hnexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hsexp (Nat.cast_nonneg _) (by positivity))
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (((p + a + b) ^ b) + q + p + s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + C) ^ C) := by
      apply Real.exp_le_exp.mpr
      simpa [Q, P, X, q, Polynomial.eval₂_pow] using hQ p hp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem adaptedPolynomial_coordinate_totalDegree (hw : ∀ i, 0 < w i)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (i : ι) :
    (coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).totalDegree ≤ s := by
  classical
  apply (degreeLE_one_iff_basis_totalDegree (b.baseChange ℝ) s _).mp ?_ i
  have hd := (F.realification.adaptedBCHToOrbit w g).degreeLE
  intro α hα
  apply hd α
  apply hα.trans_le
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Pi.one_apply, mul_one]
  exact Finset.sum_le_sum (fun j _ => Nat.le_mul_of_pos_right _ (hw j))

theorem polynomialSlowBound_value [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w v g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M := by
  let P := coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  have hdegree : P.totalDegree ≤ s := F.adaptedPolynomial_coordinate_totalDegree b w hw g i
  have hcoeff (α : σ →₀ ℕ) : |P.coeff α| ≤ M / monomialScale T α := by
    dsimp only [P]
    rw [coeff_coordinate]
    exact hg α i
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  change |((b.baseChange ℝ).coord i) (eval₂ v (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))| ≤ _
  rw [coordinate_eval₂]
  exact (abs_eval_le_scaled_box_bound P T v hT hM hcoeff hv).trans
    (mul_le_mul_of_nonneg_right hcard hM)

theorem polynomialSlowBound_difference [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v z : σ → ℝ)
    (hv : ∀ i, |v i| ≤ T i) (hz : ∀ i, |z i| ≤ T i)
    (hvz : ∀ i, |v i - z i| ≤ T i * δ) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w v g).coord i -
      (b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w z g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s * δ := by
  let P := coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  have hdegree : P.totalDegree ≤ s := F.adaptedPolynomial_coordinate_totalDegree b w hw g i
  have hcoeff (α : σ →₀ ℕ) : |P.coeff α| ≤ M / monomialScale T α := by
    dsimp only [P]
    rw [coeff_coordinate]
    exact hg α i
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  change |((b.baseChange ℝ).coord i) (eval₂ v (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) -
    ((b.baseChange ℝ).coord i) (eval₂ z (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))| ≤ _
  rw [coordinate_eval₂, coordinate_eval₂]
  apply (abs_eval_sub_eval_scaled_box_bound P T v z hT hM hδ hcoeff hv hz hvz hdegree).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) hδ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module MvPolynomial
open scoped TensorProduct

theorem exists_rational_polynomial_of_grid {σ : Type*} (P : MvPolynomial σ ℝ)
    (q : ℕ) (hq : 0 < q)
    (hP : ∀ α, ∃ a : ℤ, (a : ℝ) = (q : ℝ) * P.coeff α) :
    ∃ Q : MvPolynomial σ ℚ,
      Q.map (algebraMap ℚ ℝ) = P ∧ Q.totalDegree = P.totalDegree ∧
      ∀ α, (Q.coeff α).den ∣ q := by
  classical
  choose a ha using hP
  let Q : MvPolynomial σ ℚ := ∑ α ∈ P.support, monomial α ((a α : ℚ) / q)
  have hcoeff (α : σ →₀ ℕ) : Q.coeff α = if α ∈ P.support then (a α : ℚ) / q else 0 := by
    simp [Q, coeff_monomial]
  have hcast (α : σ →₀ ℕ) : (((a α : ℚ) / q : ℚ) : ℝ) = P.coeff α := by
    push_cast
    apply (div_eq_iff (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hq.ne')).mpr
    simpa only [mul_comm] using ha α
  have hmap : Q.map (algebraMap ℚ ℝ) = P := by
    ext α
    rw [coeff_map, hcoeff]
    by_cases hα : α ∈ P.support
    · rw [ite_eq_left hα]
      exact hcast α
    · rw [ite_eq_right hα, map_zero, notMem_support_iff.mp hα]
  refine ⟨Q, hmap, ?_, ?_⟩
  · rw [← hmap, totalDegree, totalDegree,
      support_map_of_injective Q (algebraMap ℚ ℝ).injective]
  · intro α
    rw [hcoeff]
    split_ifs
    · have h := Rat.den_dvd (a α) (q : ℤ)
      rw [Rat.divInt_eq_div, Int.cast_natCast] at h
      exact Int.natCast_dvd_natCast.mp h
    · simp

namespace NilpotentLieFiltration

open VectorPolynomial

theorem polynomialRationalGrid_exists_coordinates {σ ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (q : ℕ) (hq : 0 < q)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    ∃ P : ι → MvPolynomial σ ℚ,
      (∀ i, (P i).totalDegree ≤ s) ∧ (∀ i α, ((P i).coeff α).den ∣ q) ∧
      ∀ x : σ → ℝ,
        realPolynomialBCHMap (hnil := F.realification.lowerCentralSeries_eq_bot)
          (b.baseChange ℝ) P x = F.adaptedPolynomialRealValueHom w x g := by
  classical
  let R := fun i => coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  obtain ⟨a, ha⟩ := hg
  have hR (i : ι) : ∀ α, ∃ z : ℤ, (z : ℝ) = (q : ℝ) * (R i).coeff α := by
    intro α
    refine ⟨a (α, i), ?_⟩
    dsimp only [R]
    rw [coeff_coordinate]
    exact congrFun ha (α, i)
  choose P hmap hdeg hden using fun i => exists_rational_polynomial_of_grid (R i) q hq (hR i)
  refine ⟨P, fun i => (hdeg i).le.trans (F.adaptedPolynomial_coordinate_totalDegree b w hw g i), hden, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  apply (b.baseChange ℝ).equivFun.injective
  rw [realPolynomialBCHMap_coordinates]
  funext i
  change aeval x (P i) = ((b.baseChange ℝ).coord i)
    (VectorPolynomial.eval₂ x (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [coordinate_eval₂]
  change aeval x (P i) = MvPolynomial.eval x (R i)
  rw [← hmap i, MvPolynomial.eval_map]
  rfl

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_dist_le (hw : ∀ i, 0 < w i)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hMB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M ≤ B)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) (v z : σ → ℝ)
    (hv : ∀ i, |v i| ≤ T i) (hz : ∀ i, |z i| ≤ T i)
    (hvz : ∀ i, |v i - z i| ≤ T i * δ) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    dist (F.adaptedPolynomialRealValueHom w v g) (F.adaptedPolynomialRealValueHom w z g) ≤
      (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
        (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s) * δ := by
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  have h := dist_le_bchBoxMetricConstant (b.baseChange ℝ) (lieStructureConstants b)
    (fun i j k => (realLieBasis_structure b i j k).symm) hc B hB
    (show 0 ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * Fintype.card σ * s * δ by positivity)
    (F.adaptedPolynomialRealValueHom w v g) (F.adaptedPolynomialRealValueHom w z g)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hM g hg v hv i).trans hMB)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hM g hg z hz i).trans hMB)
    (fun i => F.polynomialSlowBound_difference b w hw T hT hM hδ g hg v z hv hz hvz i)
  simpa only [mul_assoc] using h

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_polynomialSlowBound_dist_exp (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
        D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) g →
        ∀ (v z : σ → ℝ) (δ : ℝ), 0 ≤ δ →
          (∀ i, |v i| ≤ T i) → (∀ i, |z i| ≤ T i) →
          (∀ i, |v i - z i| ≤ T i * δ) →
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
          dist (D.filtration.adaptedPolynomialRealValueHom w v g)
            (D.filtration.adaptedPolynomialRealValueHom w z g) ≤ Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hbound⟩ := exists_slow_polynomial_metric_budget s r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ T hT g hg v z δ hδ hv hz hvz
  let H := ⌈Real.exp p⌉₊
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨B, hB, hMB, hK⟩ := hbound d (Fintype.card σ) H (p + 1)
    (Real.exp ((p + 2) ^ r)) (by linarith) (hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) _))
  have hdist := D.filtration.polynomialSlowBound_dist_le D.basis w hw H
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) T hT (Real.exp_pos _).le
    hδ B hB hMB g hg v z hv hz hvz
  have hK' : (bchBoxMetricConstant s (Fintype.card (Fin d)) H B : ℝ) *
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp ((p + 2) ^ r) * Fintype.card σ * s) ≤
        Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    apply hK.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact hdist.trans (mul_le_mul_of_nonneg_right hK' hδ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module MvPolynomial
open scoped TensorProduct

theorem polynomial_integer_value_common_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (q : ℕ)
    (hP : ∀ α, ∃ a : ℤ, (a : ℝ) = (q : ℝ) * P.coeff α) (x : σ → ℤ) :
    ∃ a : ℤ, (a : ℝ) = (q : ℝ) * eval (fun j => (x j : ℝ)) P := by
  classical
  choose a ha using hP
  refine ⟨∑ α ∈ P.support, a α * ∏ j, x j ^ α j, ?_⟩
  rw [eval_eq', Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro α _
  rw [ha α]
  ring

namespace NilpotentLieFiltration

open VectorPolynomial

theorem polynomialRationalGrid_value {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ) (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) (x : σ → ℤ) :
    (b.baseChange ℝ).equivFun
      (F.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g).coord ∈ realDenominatorGrid q := by
  classical
  let P := fun i => coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  obtain ⟨a, ha⟩ := hg
  have hP (i : ι) : ∀ α, ∃ z : ℤ, (z : ℝ) = (q : ℝ) * (P i).coeff α := by
    intro α
    refine ⟨a (α, i), ?_⟩
    dsimp only [P]
    rw [coeff_coordinate]
    exact congrFun ha (α, i)
  choose z hz using fun i => polynomial_integer_value_common_denominator (P i) q (hP i) x
  refine ⟨z, funext fun i => ?_⟩
  change (z i : ℝ) = (q : ℝ) * ((b.baseChange ℝ).coord i)
    (eval₂ (fun j => (x j : ℝ)) (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [coordinate_eval₂]
  exact hz i

end NilpotentLieFiltration
end Erdos3

end

end OAI
