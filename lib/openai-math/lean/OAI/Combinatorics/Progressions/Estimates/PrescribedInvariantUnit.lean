import Mathlib.Analysis.SpecialFunctions.Sqrt
import OAI.Combinatorics.Progressions.Dynamics.UniformInvariantBudget
import OAI.Combinatorics.Progressions.Linear.NativePrescribedProjection
import OAI.Combinatorics.Progressions.Linear.NativeVerticalTranslateFrame

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem sqrt_complement_lipschitz {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hrhalf : r ≤ 1 / 2) (hthalf : t ≤ 1 / 2) :
    |Real.sqrt (1 - r ^ 2) - Real.sqrt (1 - t ^ 2)| ≤ |r - t| := by
  let a := Real.sqrt (1 - r ^ 2)
  let b := Real.sqrt (1 - t ^ 2)
  have hrq : 0 ≤ 1 - r ^ 2 := by nlinarith
  have htq : 0 ≤ 1 - t ^ 2 := by nlinarith
  have ha : 1 / 2 ≤ a := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb : 1 / 2 ≤ b := Real.le_sqrt_of_sq_le (by nlinarith)
  have ha2 : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hrq
  have hb2 : b ^ 2 = 1 - t ^ 2 := Real.sq_sqrt htq
  have heq : |a - b| * (a + b) = |r - t| * (r + t) := by
    calc
      _ = |(a - b) * (a + b)| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ a + b)]
      _ = |(t - r) * (r + t)| := congrArg abs (by nlinarith)
      _ = _ := by rw [abs_mul, abs_sub_comm t r, abs_of_nonneg (by linarith : 0 ≤ r + t)]
  calc
    _ ≤ |a - b| * (a + b) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |r - t| * (r + t) := heq
    _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) (by linarith)

theorem exists_complex_unit_completion {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (f : X → ℂ) (v : Fin n → X → ℂ) {K J : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ 1 / 2) (hfLip : LipschitzWith K f)
    (hv : ∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) (hvnorm : ∀ i x, ‖v i x‖ ≤ 1)
    (hvLip : ∀ i, LipschitzWith J (v i)) :
    ∃ u : Fin (n + 1) → X → ℂ,
      (∀ x, u 0 x = f x) ∧
      (∀ x, ∑ i, ‖u i x‖ ^ 2 = 1) ∧
      (∀ i x, ‖u i x‖ ≤ 1) ∧
      (∀ i, LipschitzWith (K + J) (u i)) ∧
      ∀ x y c, ‖c‖ = 1 → f x = c * f y → (∀ i, v i x = c * v i y) →
        ∀ i, u i x = c * u i y := by
  let t (x : X) : ℂ := Real.sqrt (1 - ‖f x‖ ^ 2)
  have ht (x : X) : ‖t x‖ = Real.sqrt (1 - ‖f x‖ ^ 2) := by
    exact (Complex.norm_real _).trans (Real.norm_of_nonneg (Real.sqrt_nonneg _))
  have htbound (x : X) : ‖t x‖ ≤ 1 := by
    rw [ht]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ‖f x‖])
  have htsq (x : X) : ‖t x‖ ^ 2 = 1 - ‖f x‖ ^ 2 := by
    rw [ht]
    exact Real.sq_sqrt (by nlinarith [hf x, norm_nonneg (f x)])
  have htLip : LipschitzWith K t := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    change ‖(Real.sqrt (1 - ‖f x‖ ^ 2) : ℂ) - (Real.sqrt (1 - ‖f y‖ ^ 2) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (sqrt_complement_lipschitz (norm_nonneg _) (norm_nonneg _) (hf x) (hf y)).trans
      ((abs_norm_sub_norm_le (f x) (f y)).trans (by
        simpa only [dist_eq_norm] using hfLip.dist_le_mul x y))
  let u : Fin (n + 1) → X → ℂ := Fin.cases f (fun i x => t x * v i x)
  have htailLip (i : Fin n) : LipschitzWith (K + J) (fun x => t x * v i x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    calc
      _ = ‖(t x - t y) * v i x + t y * (v i x - v i y)‖ := by congr 1; ring
      _ ≤ ‖(t x - t y) * v i x‖ + ‖t y * (v i x - v i y)‖ := norm_add_le _ _
      _ ≤ ‖t x - t y‖ + ‖v i x - v i y‖ := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_of_le_one_right (norm_nonneg _) (hvnorm i x))
          (mul_le_of_le_one_left (norm_nonneg _) (htbound y))
      _ ≤ (K : ℝ) * dist x y + (J : ℝ) * dist x y := add_le_add
        (by simpa only [dist_eq_norm] using htLip.dist_le_mul x y)
        (by simpa only [dist_eq_norm] using (hvLip i).dist_le_mul x y)
      _ = _ := by push_cast; ring
  refine ⟨u, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Fin.sum_univ_succ, u, Fin.cases_zero, Fin.cases_succ, norm_mul, mul_pow]
    rw [← Finset.mul_sum, hv, mul_one, htsq]
    ring
  · intro i x
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hf x).trans (by norm_num)
    · change ‖t x * v j x‖ ≤ 1
      rw [norm_mul]
      exact (mul_le_mul (htbound x) (hvnorm j x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro i
    refine Fin.cases ?_ htailLip i
    exact hfLip.weaken (le_add_of_nonneg_right (show 0 ≤ J by positivity))
  · intro x y c hc hfc hvc i
    have htx : t x = t y := by
      dsimp [t]
      rw [hfc, norm_mul, hc, one_mul]
    refine Fin.cases hfc (fun j => ?_) i
    change t x * v j x = c * (t y * v j y)
    rw [htx, hvc]
    ring

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_prescribed_scalar (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ f : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K f) ∧
        (∀ x, ‖f x‖ ≤ 2) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
          f (z • x) = logCharacter (realifyFunctional η) z * f x) ∧
        f (QuotientGroup.mk (1 : D.RealGroup)) = 1 := by
  obtain ⟨C, hC, hseed⟩ := exists_native_central_seed s
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  obtain ⟨K, hK, f, hf, hb, hcentral⟩ := hseed D hp hD η hη hint
  obtain ⟨g, hg, hgb, hvertical, hone⟩ :=
    D.exists_native_prescribed_projection hp hD η f hf hb hcentral
  exact ⟨K, hK, g, hg, hgb, hvertical, hone⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct NNReal BigOperators

theorem exists_native_unit_vertical_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ v : Fin n → D.Space → ℂ,
        (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
        (∀ i x, ‖v i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (v i)) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          v i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x := by
  obtain ⟨a, _, hframe⟩ := exists_native_vertical_translate_frame s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 2 * (X + Polynomial.C a) ^ a + 3)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have htotal : p + 2 * P + 3 ≤ (p + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨n, hn, hnc, K, hK, u, _, hLip, hlower, hphase⟩ :=
    hframe D T hp hT hnorm eta hvertical y hy
  let rho : ℝ≥0 := ⟨Real.exp (-(p + 1)), (Real.exp_pos _).le⟩
  have hrho : 0 < rho := Real.exp_pos _
  obtain ⟨v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    exists_normalized_complex_family u hrho hLip hlower
  let B : ℝ≥0 := 2 / rho * ((n + 1 : ℝ≥0) * K)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hnplus : (n : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hscale : 2 / (rho : ℝ) ≤ Real.exp (p + 2) := by
    calc
      _ = 2 * Real.exp (p + 1) := by
        change 2 / Real.exp (-(p + 1)) = _
        rw [Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (p + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hB : (B : ℝ) ≤ Real.exp (p + 2 * P + 3) := by
    calc
      _ ≤ Real.exp (p + 2) * (Real.exp (P + 1) * Real.exp P) := by
        dsimp [B]
        push_cast
        exact mul_le_mul hscale (mul_le_mul hnplus hK K.coe_nonneg (Real.exp_nonneg _))
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr (by dsimp [P] at *; linarith)),
    B, hB.trans (Real.exp_le_exp.mpr htotal), v, hvunit, hvnorm, ?_, ?_⟩
  · intro i
    simpa only [Fintype.card_fin] using hvLip i
  · intro i z hz x
    exact hvphase (z • x) x _ (norm_character _) (fun j => hphase j z hz x) i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_prescribed_unit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) (Fin n)
        ((p + C) ^ C), V.frequency = η := by
  obtain ⟨a, _, hscalar⟩ := exists_native_prescribed_scalar s
  obtain ⟨b, _, hfamily⟩ := exists_native_unit_vertical_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + (X + Polynomial.C a) ^ a + 4 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  obtain ⟨K, hK, f, hf, hb, hvertical, hone⟩ := hscalar D hp hD η hη hint
  let P := (p + a) ^ a
  let q := p + P + 4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  let T : D.Niltest (fun _ : Unit => 1) := {
    orbit := 1
    observable := fun x => f x / 2
    normBound := 1
    lipBound := K
    norm_le := fun x => by
      rw [norm_div, htwoNorm]
      simpa only [NNReal.coe_one, div_self (by norm_num : (2 : ℝ) ≠ 0)] using
        div_le_div_of_nonneg_right (hb x) (by norm_num : (0 : ℝ) ≤ 2)
    lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, ← sub_div, norm_div, htwoNorm]
      have h := hf.dist_le_mul x y
      rw [dist_eq_norm] at h
      linarith [norm_nonneg (f x - f y)] }
  have hT : T.ComplexityLE q := by
    refine ⟨hD.mono D hpq, ?_⟩
    have h := niltest_log_bound_of_exp (1 : ℝ≥0) K (a := 0) (b := P)
      (by norm_num) hP (by simp) hK
    simp only [NNReal.coe_one, zero_add] at h
    change Real.log (2 + ((1 : ℝ≥0) : ℝ) + K) ≤ q
    dsimp [q]
    linarith
  have hphase : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x := by
    intro z hz x
    change f (z • x) / 2 = _ * (f x / 2)
    rw [hvertical z hz]
    exact mul_div_assoc _ _ _
  have hy : Real.exp (-q) ≤ ‖T.observable (QuotientGroup.mk (1 : D.RealGroup))‖ := by
    change Real.exp (-q) ≤ ‖f (QuotientGroup.mk (1 : D.RealGroup)) / 2‖
    rw [hone, norm_div, norm_one, htwoNorm]
    have htwo : (2 : ℝ) ≤ Real.exp q := by
      have he := Real.add_one_le_exp q
      dsimp [q] at *
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) htwo
  obtain ⟨n, hn, hnc, K', hK', v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    hfamily D T hq hT (by exact le_rfl) η hphase
      (QuotientGroup.mk (1 : D.RealGroup)) hy
  have htotal : p + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, P, Polynomial.eval₂_pow] using hbudget p hp
  have hqb : (q + b) ^ b ≤ (p + C) ^ C := by linarith
  have hpc : p ≤ (p + C) ^ C := by
    have : 0 ≤ (q + b) ^ b := by positivity
    linarith
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hqb), ?_⟩
  exact ⟨{
    observable := v
    unit := hvunit
    norm := hvnorm
    lipBound := K'
    lip_bound := hK'.trans (Real.exp_le_exp.mpr hqb)
    lipschitz := hvLip
    frequency := η
    height := fun i => (hη i).trans hpc
    vertical := hvphase
    integral := fun z _ hz => hint z hz }, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct NNReal BigOperators

theorem exists_native_unit_vertical_completion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ v : Fin (n + 1) → D.Space → ℂ,
        (∀ x, v 0 x = T.observable x / 2) ∧
        (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
        (∀ i x, ‖v i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (v i)) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          v i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x := by
  obtain ⟨a, _, hfamily⟩ := exists_native_unit_vertical_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C a) ^ a + 1)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have htotal : p + P + 1 ≤ (p + C) ^ C := by
    simpa [X, P, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨n, hn, hnc, K, hK, v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    hfamily D T hp hT hnorm eta hvertical y hy
  let f (x : D.Space) := T.observable x / 2
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have hf (x : D.Space) : ‖f x‖ ≤ 1 / 2 := by
    have hn' : (T.normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hnorm
    dsimp [f]
    rw [norm_div, htwoNorm]
    exact div_le_div_of_nonneg_right ((T.norm_le x).trans hn') (by norm_num)
  have hfLip : LipschitzWith T.lipBound f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (T.observable x / 2) (T.observable y / 2) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div, htwoNorm]
    have h := T.lipschitz.dist_le_mul x y
    rw [dist_eq_norm] at h
    linarith [norm_nonneg (T.observable x - T.observable y)]
  obtain ⟨u, hu0, huunit, hunorm, huLip, huphase⟩ :=
    exists_complex_unit_completion f v hf hfLip hvunit hvnorm hvLip
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hcount : (n : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hsum : ((T.lipBound + K : ℝ≥0) : ℝ) ≤ Real.exp (p + P + 1) := by
    have hTlip : (T.lipBound : ℝ) ≤ Real.exp p := by
      linarith [Niltest.observable_budget hT, T.normBound.coe_nonneg]
    have ht := hTlip.trans (Real.exp_le_exp.mpr (show p ≤ p + P by linarith))
    have hk := hK.trans (Real.exp_le_exp.mpr (show (p + a) ^ a ≤ p + P by dsimp [P]; linarith))
    calc
      _ ≤ 2 * Real.exp (p + P) := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp (p + P) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨n, hn, hcount.trans (Real.exp_le_exp.mpr (by linarith)),
    T.lipBound + K, hsum.trans (Real.exp_le_exp.mpr htotal), u, hu0, huunit, hunorm, huLip, ?_⟩
  intro i z hz x
  apply huphase (z • x) x _ (norm_character _) ?_ (fun j => hvphase j z hz x) i
  dsimp [f]
  rw [hvertical z hz]
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_canonical_prescribed_unit_with_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, η z.coord = n) →
      ∀ q : ℝ, (p + C) ^ C ≤ q →
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] L)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] L) := IsModuleTopology.isTopologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 D.basis
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp q ∧
        ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) (Fin n)
          q, V.frequency = η := by
  obtain ⟨C, hC, hunit⟩ := exists_native_prescribed_unit s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD η hη hint q hq
  let := moduleTopology ℝ (ℝ ⊗[ℚ] L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] L) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  obtain ⟨n, hn, hnc, V, hV⟩ := hunit D hp hD η hη (D.realLattice_functional_integral η hint)
  exact ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hq), V.mono hq, hV⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_prescribed_invariant_unit (s M : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Γ L : Type*} [Group Γ] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) [MulAction Γ D.Space],
      Fintype.card Γ ≤ M → ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (letI := D.metricSpace; ∀ a : Γ,
        LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (fun x : D.Space => a • x)) →
      (∀ (a : Γ) (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x : D.Space,
        a • (z • x) = z • (a • x)) →
      ∀ η : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ n : ℕ, 0 < n ∧
        (Fintype.card (SymmetricEvaluationIndex (Fintype.card Γ) (Fin n)) : ℝ) ≤
          Real.exp ((p + C) ^ C) ∧
      ∃ W : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
          (SymmetricEvaluationIndex (Fintype.card Γ) (Fin n)) ((p + C) ^ C),
        W.frequency = Fintype.card Γ • η ∧
        ∀ (a : Γ) k x, W.observable k (a • x) = W.observable k x := by
  obtain ⟨a, _, hunit⟩ := exists_native_prescribed_unit s
  obtain ⟨b, _, hcost⟩ := exists_uniform_invariantVertical_cost M
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a) ^ a + (X + 3) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro Γ L _ _ _ _ _ _ _ _ d D _ hM p hp hD hact hcomm η hη hint
  let := D.metricSpace
  obtain ⟨n, hn, hnc, V, hV⟩ := hunit D hp hD η hη hint
  let P := (p + a) ^ a
  let r := p + P + (p + 3) ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hPr : P ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 3)]
  have hAr : (p + 3) ^ 2 ≤ r := by dsimp [r]; linarith
  let V' := V.mono hPr
  have hn' : (Fintype.card (Fin n) : ℝ) ≤ Real.exp r := by
    simpa only [Fintype.card_fin] using hnc.trans (Real.exp_le_exp.mpr hPr)
  obtain ⟨W, hW, hWinv, hWcard⟩ := V'.exists_invariant hr hn'
    ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (Real.exp_le_exp.mpr hAr) hact hcomm
  have htotal : invariantVerticalBudget (Fintype.card Γ) r ≤ (p + C) ^ C := by
    apply (hcost (Fintype.card Γ) hM r hr).trans
    simpa [R, X, r, P, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hWcard.trans (Real.exp_le_exp.mpr htotal), W.mono htotal, ?_, hWinv⟩
  change W.frequency = _
  rw [hW]
  change Fintype.card Γ • V.frequency = _
  rw [hV]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
