import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest
import OAI.Combinatorics.Progressions.Estimates.IteratedCircleAverageIntegral

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_mean_sub_le {G : Type*} [Fintype G] [Nonempty G]
    (w f g : G → ℂ) {B rho : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (hfg : ∀ n, ‖f n - g n‖ ≤ rho) :
    ‖(𝔼 n, w n * f n) - (𝔼 n, w n * g n)‖ ≤ B * rho := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const Finset.univ_nonempty _)
  intro n _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hw n) (hfg n) (norm_nonneg _) hB

theorem finite_projection_tested_error {G J : Type*} [Fintype G] [Nonempty G] [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hw : ∀ n, ‖w n‖ ≤ B)
    (hfull : ∀ n, ‖f n - ∑ j, v j n‖ ≤ rho)
    (hprojected : ∀ n, ‖(∑ j, if keep j then v j n else 0) - projected n‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖𝔼 n, w n * v j n‖ ≤ tau) :
    ‖(𝔼 n, w n * f n) - (𝔼 n, w n * projected n)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := norm_weighted_mean_sub_le w f (fun n => ∑ j, v j n) hB hw hfull
  have hlast := norm_weighted_mean_sub_le w
    (fun n => ∑ j, if keep j then v j n else 0) projected hB hw hprojected
  have hid : (𝔼 n, w n * ∑ j, v j n) -
      (𝔼 n, w n * ∑ j, if keep j then v j n else 0) =
      ∑ j, if keep j then 0 else (𝔼 n, w n * v j n) := by
    calc
      _ = 𝔼 n, w n * ((∑ j, v j n) - ∑ j, if keep j then v j n else 0) := by
        simp only [mul_sub, Finset.expect_sub_distrib]
      _ = 𝔼 n, ∑ j, if keep j then 0 else w n * v j n := by
        apply Finset.expect_congr rfl
        intro n _
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, 𝔼 n, if keep j then 0 else w n * v j n := Finset.expect_sum_comm _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
  have hmiddle : ‖(𝔼 n, w n * ∑ j, v j n) -
      (𝔼 n, w n * ∑ j, if keep j then v j n else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 n, w n * f n) (𝔼 n, w n * ∑ j, v j n) (𝔼 n, w n * projected n)
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 n, w n * ∑ j, v j n) (𝔼 n, w n * ∑ j, if keep j then v j n else 0)
    (𝔼 n, w n * projected n)
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_finiteWeightedSum_sub_le {G : Type*} [Fintype G]
    (w f g : G → ℂ) {B rho : ℝ}
    (hmass : (∑ x, ‖w x‖) ≤ B) (hrho : 0 ≤ rho)
    (hfg : ∀ x, ‖f x - g x‖ ≤ rho) :
    ‖(∑ x, w x * f x) - (∑ x, w x * g x)‖ ≤ B * rho := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, ‖w x * f x - w x * g x‖ := norm_sum_le _ _
    _ ≤ ∑ x, ‖w x‖ * rho := by
      apply Finset.sum_le_sum
      intro x _
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hfg x) (norm_nonneg _)
    _ = (∑ x, ‖w x‖) * rho := (Finset.sum_mul ..).symm
    _ ≤ B * rho := mul_le_mul_of_nonneg_right hmass hrho

theorem finiteWeightedProjection_error {G J : Type*} [Fintype G] [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hmass : (∑ x, ‖w x‖) ≤ B) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hfull : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (hprojected : ∀ x, ‖(∑ j, if keep j then v j x else 0) - projected x‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖∑ x, w x * v j x‖ ≤ tau) :
    ‖(∑ x, w x * f x) - (∑ x, w x * projected x)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := norm_finiteWeightedSum_sub_le w f (fun x => ∑ j, v j x) hmass hrho hfull
  have hlast := norm_finiteWeightedSum_sub_le w
    (fun x => ∑ j, if keep j then v j x else 0) projected hmass hrho hprojected
  have hid : (∑ x, w x * ∑ j, v j x) -
      (∑ x, w x * ∑ j, if keep j then v j x else 0) =
      ∑ j, if keep j then 0 else (∑ x, w x * v j x) := by
    calc
      _ = ∑ x, w x * ((∑ j, v j x) - ∑ j, if keep j then v j x else 0) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ = ∑ x, ∑ j, if keep j then 0 else w x * v j x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, ∑ x, if keep j then 0 else w x * v j x := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
  have hmiddle : ‖(∑ x, w x * ∑ j, v j x) -
      (∑ x, w x * ∑ j, if keep j then v j x else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, w x * f x) (∑ x, w x * ∑ j, v j x) (∑ x, w x * projected x)
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, w x * ∑ j, v j x) (∑ x, w x * ∑ j, if keep j then v j x else 0)
    (∑ x, w x * projected x)
  linarith

end Erdos3

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem lipschitz_finite_complex_sum {X J : Type*} [PseudoMetricSpace X] [Fintype J]
    (v : J → X → ℂ) (L : J → ℝ≥0) (hv : ∀ j, LipschitzWith (L j) (v j)) :
    LipschitzWith (∑ j, L j) (fun x => ∑ j, v j x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖v j x - v j y‖ := norm_sum_le _ _
    _ ≤ ∑ j, (L j : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [dist_eq_norm] using (hv j).dist_le_mul x y
    _ = _ := by simp only [NNReal.coe_sum, Finset.sum_mul]

theorem iteratedCircleAverage_tested_error
    {X α G J : Type*} [PseudoMetricSpace X] [Fintype G] [Nonempty G] [Fintype J]
    (A : α → IsometricCircleAction X) (is : List α) (f : X → ℂ)
    (v : J → X → ℂ) (n : J → α → ℤ) (path : G → X) (weight : G → ℂ)
    (Lf : ℝ≥0) (Lv : J → ℝ≥0) (hf : LipschitzWith Lf f)
    (hv : ∀ j, LipschitzWith (Lv j) (v j))
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x, v j ((A i).act t x) = character (n j i • t) * v j x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖𝔼 x, weight x * v j (path x)‖ ≤ tau) :
    ‖(𝔼 x, weight x * f (path x)) -
      (𝔼 x, weight x * iteratedCircleAverage A is f (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  have hsum (x : X) : iteratedCircleAverage A is (fun y => ∑ j, v j y) x =
      ∑ j, if keep j then v j x else 0 := by
    rw [iteratedCircleAverage_sum A is Finset.univ v Lv (fun j _ => hv j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j) (heigen j)]
    dsimp only [keep]
    split_ifs <;> rfl
  apply finite_projection_tested_error weight (fun x => f (path x))
    (fun x => iteratedCircleAverage A is f (path x))
    (fun j x => v j (path x)) keep hB htau hweight (fun x => happrox (path x)) _ hdiscard
  intro x
  rw [← hsum, norm_sub_rev]
  exact iteratedCircleAverage_sub_norm_le A is hf (lipschitz_finite_complex_sum v Lv hv)
    happrox (path x)

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace FiniteProbabilityWeights

variable {G : Type*} [Fintype G] (p : FiniteProbabilityWeights G)

theorem norm_tested_difference_le (w f g : G → ℂ) {B rho : ℝ} (hB : 0 ≤ B)
    (hw : ∀ x, ‖w x‖ ≤ B) (hfg : ∀ x, ‖f x - g x‖ ≤ rho) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤ B * rho := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => B * rho) ?_).trans_eq (p.mean_const _)
  intro x _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hw x) (hfg x) (norm_nonneg _) hB

theorem finite_projection_tested_error {J : Type*} [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hw : ∀ x, ‖w x‖ ≤ B)
    (hfull : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (hprojected : ∀ x, ‖(∑ j, if keep j then v j x else 0) - projected x‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * v j x)‖ ≤ tau) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * projected x)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := p.norm_tested_difference_le w f (fun x => ∑ j, v j x) hB hw hfull
  have hlast := p.norm_tested_difference_le w
    (fun x => ∑ j, if keep j then v j x else 0) projected hB hw hprojected
  have hid : p.complexMean (fun x => w x * ∑ j, v j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0) =
      ∑ j, if keep j then 0 else p.complexMean (fun x => w x * v j x) := by
    rw [← p.complexMean_sub]
    calc
      _ = ∑ x, ∑ j, if keep j then 0 else (p.weight x : ℂ) * (w x * v j x) := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only
        rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, ∑ x, if keep j then 0 else (p.weight x : ℂ) * (w x * v j x) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj, complexMean]
  have hmiddle : ‖p.complexMean (fun x => w x * ∑ j, v j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x)) (p.complexMean (fun x => w x * ∑ j, v j x))
    (p.complexMean (fun x => w x * projected x))
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * ∑ j, v j x))
    (p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0))
    (p.complexMean (fun x => w x * projected x))
  linarith

end FiniteProbabilityWeights

namespace CircleFourier

theorem iteratedCircleAverage_tested_weighted_error
    {X α G J : Type*} [PseudoMetricSpace X] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G)
    (A : α → IsometricCircleAction X) (is : List α) (f : X → ℂ)
    (v : J → X → ℂ) (n : J → α → ℤ) (path : G → X) (weight : G → ℂ)
    (Lf : ℝ≥0) (Lv : J → ℝ≥0) (hf : LipschitzWith Lf f)
    (hv : ∀ j, LipschitzWith (Lv j) (v j))
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x, v j ((A i).act t x) = character (n j i • t) * v j x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖p.complexMean (fun x => weight x * v j (path x))‖ ≤ tau) :
    ‖p.complexMean (fun x => weight x * f (path x)) -
      p.complexMean (fun x => weight x * iteratedCircleAverage A is f (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  have hsum (x : X) : iteratedCircleAverage A is (fun y => ∑ j, v j y) x =
      ∑ j, if keep j then v j x else 0 := by
    rw [iteratedCircleAverage_sum A is Finset.univ v Lv (fun j _ => hv j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j) (heigen j)]
    dsimp only [keep]
    split_ifs <;> rfl
  apply p.finite_projection_tested_error weight (fun x => f (path x))
    (fun x => iteratedCircleAverage A is f (path x))
    (fun j x => v j (path x)) keep hB htau hweight (fun x => happrox (path x)) _ hdiscard
  intro x
  rw [← hsum, norm_sub_rev]
  exact iteratedCircleAverage_sub_norm_le A is hf (lipschitz_finite_complex_sum v Lv hv)
    happrox (path x)

theorem iteratedCircleAverage_weighted_error
    {X α G J : Type*} [PseudoMetricSpace X] [Fintype G] [Fintype J]
    (A : α → IsometricCircleAction X) (is : List α) (f : X → ℂ)
    (v : J → X → ℂ) (n : J → α → ℤ) (path : G → X) (weight : G → ℂ)
    (Lf : ℝ≥0) (Lv : J → ℝ≥0) (hf : LipschitzWith Lf f)
    (hv : ∀ j, LipschitzWith (Lv j) (v j))
    {B rho tau : ℝ} (hmass : (∑ x, ‖weight x‖) ≤ B)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (happrox : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x, v j ((A i).act t x) = character (n j i • t) * v j x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖∑ x, weight x * v j (path x)‖ ≤ tau) :
    ‖(∑ x, weight x * f (path x)) -
      (∑ x, weight x * iteratedCircleAverage A is f (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  let full : X → ℂ := fun x => ∑ j, v j x
  let retained : X → ℂ := fun x => ∑ j, if keep j then v j x else 0
  have hsum (x : X) : iteratedCircleAverage A is full x = retained x := by
    rw [iteratedCircleAverage_sum A is Finset.univ v Lv (fun j _ => hv j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j) (heigen j)]
    dsimp only [keep]
    split_ifs <;> rfl
  have htested (a b : X → ℂ) (hab : ∀ x, ‖a x - b x‖ ≤ rho) :
      ‖(∑ x, weight x * a (path x)) - (∑ x, weight x * b (path x))‖ ≤ B * rho := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x, ‖weight x * a (path x) - weight x * b (path x)‖ := norm_sum_le _ _
      _ ≤ ∑ x, ‖weight x‖ * rho := by
        apply Finset.sum_le_sum
        intro x _
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hab (path x)) (norm_nonneg _)
      _ = (∑ x, ‖weight x‖) * rho := (Finset.sum_mul ..).symm
      _ ≤ B * rho := mul_le_mul_of_nonneg_right hmass hrho
  have hfirst := htested f full happrox
  have hlast := htested retained (iteratedCircleAverage A is f) (fun x => by
    rw [← hsum, norm_sub_rev]
    exact iteratedCircleAverage_sub_norm_le A is hf (lipschitz_finite_complex_sum v Lv hv)
      happrox x)
  have hid : (∑ x, weight x * full (path x)) - (∑ x, weight x * retained (path x)) =
      ∑ j, if keep j then 0 else ∑ x, weight x * v j (path x) := by
    simp only [full, retained, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x j => weight x * if keep j then v j (path x) else 0),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j <;> simp [hj]
  have hmiddle : ‖(∑ x, weight x * full (path x)) - (∑ x, weight x * retained (path x))‖ ≤
      Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, weight x * f (path x)) (∑ x, weight x * full (path x))
    (∑ x, weight x * iteratedCircleAverage A is f (path x))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, weight x * full (path x)) (∑ x, weight x * retained (path x))
    (∑ x, weight x * iteratedCircleAverage A is f (path x))
  linarith

end CircleFourier
end Erdos3

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem iteratedCircleAverage_family_tested_weighted_error
    {X Y α G J : Type*} [PseudoMetricSpace Y] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G)
    (A : α → IsometricCircleAction Y) (is : List α) (f : X → Y → ℂ)
    (v : J → X → Y → ℂ) (n : J → α → ℤ)
    (physical : G → X) (path : G → Y) (weight : G → ℂ)
    (Lf : X → ℝ≥0) (Lv : J → X → ℝ≥0)
    (hf : ∀ x, LipschitzWith (Lf x) (f x))
    (hv : ∀ j x, LipschitzWith (Lv j x) (v j x))
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ g, ‖weight g‖ ≤ B)
    (happrox : ∀ x y, ‖f x y - ∑ j, v j x y‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x y,
      v j x ((A i).act t y) = character (n j i • t) * v j x y)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖p.complexMean (fun g => weight g * v j (physical g) (path g))‖ ≤ tau) :
    ‖p.complexMean (fun g => weight g * f (physical g) (path g)) -
      p.complexMean (fun g =>
        weight g * iteratedCircleAverage A is (f (physical g)) (path g))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  have hsum (x : X) (y : Y) :
      iteratedCircleAverage A is (fun z => ∑ j, v j x z) y =
        ∑ j, if keep j then v j x y else 0 := by
    rw [iteratedCircleAverage_sum A is Finset.univ
      (fun j => v j x) (fun j => Lv j x) (fun j _ => hv j x)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j x)
      (fun i hi t y => heigen j i hi t x y)]
    dsimp only [keep]
    split_ifs <;> rfl
  apply p.finite_projection_tested_error weight
    (fun g => f (physical g) (path g))
    (fun g => iteratedCircleAverage A is (f (physical g)) (path g))
    (fun j g => v j (physical g) (path g)) keep hB htau hweight
    (fun g => happrox (physical g) (path g)) _ hdiscard
  intro g
  rw [← hsum, norm_sub_rev]
  exact iteratedCircleAverage_sub_norm_le A is (hf (physical g))
    (lipschitz_finite_complex_sum (fun j => v j (physical g))
      (fun j => Lv j (physical g)) (fun j => hv j (physical g)))
    (happrox (physical g)) (path g)

end Erdos3.CircleFourier

end

end OAI
