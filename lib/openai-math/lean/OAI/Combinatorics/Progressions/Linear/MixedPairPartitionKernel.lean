/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.MixedPairPartitionPrecision
import OAI.Combinatorics.Progressions.Estimates.QuarticPairPartitionPrecision

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem norm_unit_prod_sub_prod_le_sum {I : Type*} (S : Finset I) (f g : I → ℂ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) (hg : ∀ i ∈ S, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ ∑ i ∈ S, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
    intro hf hg
    have hrec := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    have hprod : ‖∏ j ∈ S, g j‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = ‖f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) +
          (f i - g i) * ∏ j ∈ S, g j‖ := by congr 1; ring
      _ ≤ ‖f i‖ * ‖(∏ j ∈ S, f j) - ∏ j ∈ S, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ S, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          (f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)) ((f i - g i) * ∏ j ∈ S, g j)
      _ ≤ ‖(∏ j ∈ S, f j) - ∏ j ∈ S, g j‖ + ‖f i - g i‖ :=
        add_le_add (mul_le_of_le_one_left (norm_nonneg _) (hf i (Finset.mem_insert_self _ _)))
          (mul_le_of_le_one_right (norm_nonneg _) hprod)
      _ ≤ _ := by linarith

theorem norm_cubic_pair_product_sub_le (a b c d A B C D : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) (hD : ‖D‖ ≤ 1) :
    ‖(star a * b) * (star c * d) - (star A * B) * (star C * D)‖ ≤
      ‖a - A‖ + ‖b - B‖ + ‖c - C‖ + ‖d - D‖ := by
  have h := norm_unit_prod_sub_prod_le_sum Finset.univ ![star a, b, star c, d] ![star A, B, star C, D]
    (by intro k _; fin_cases k
        · simpa using ha
        · simpa using hb
        · simpa using hc
        · simpa using hd)
    (by intro k _; fin_cases k
        · simpa using hA
        · simpa using hB
        · simpa using hC
        · simpa using hD)
  rw [Fin.prod_univ_four, Fin.prod_univ_four, Fin.sum_univ_four] at h
  change ‖star a * b * star c * d - star A * B * star C * D‖ ≤
    ‖star a - star A‖ + ‖b - B‖ + ‖star c - star C‖ + ‖d - D‖ at h
  rw [← star_sub, ← star_sub, norm_star, norm_star] at h
  simpa only [mul_assoc] using h

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

namespace NativeCubicPairPartition

attribute [local instance] NativeCubicPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}
  (P : NativeCubicPairPartition R b ε)

noncomputable def cellWeight (a : Fin 3 → P.I) (x : Fin 3 → ZMod N) : ℝ :=
  ∏ l, P.weight (a l) (x l)

theorem cellWeight_nonneg (a : Fin 3 → P.I) (x : Fin 3 → ZMod N) : 0 ≤ P.cellWeight a x :=
  Finset.prod_nonneg (fun l _ => ((P.positive (a l)).unit_interval (x l)).1)

theorem cellWeight_total (x : Fin 3 → ZMod N) : ∑ a, P.cellWeight a x = 1 :=
  sum_productPartitionWeight (fun _ : Fin 3 => P.weight) (fun _ => P.total) x

noncomputable def cellVector (a : Fin 3 → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 3 → ZMod N) : ℂ :=
  R.cubicPairAnchoredVector (fun l => ((P.anchor a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))

theorem cellVector_norm (a : Fin 3 → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 3 → ZMod N) : ‖P.cellVector a k out x‖ ≤ 1 :=
  R.cubicPairAnchoredVector_norm _ _ _ _

noncomputable def cellKernel (a : Fin 3 → P.I) (x : Fin 3 → ZMod N) : ℂ :=
  (star (P.cellVector a 0 i.1 x) * P.cellVector a 1 j.1 x) *
    (star (P.cellVector a 0 i.2 x) * P.cellVector a 1 j.2 x)

theorem weighted_kernel_error :
    (𝔼 x : Fin 3 → ZMod N, ∑ a, P.cellWeight a x *
      ‖W.cubicAntisymmetricPair i j (x 1).val (x 2).val (((x 0).val : ℤ) + shift) - P.cellKernel a x‖) ≤
        4 * ε := by
  let F := fun (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ZMod N) =>
    W.eval out (cubicTrilinearInput (x k.succ).val (x k.rev.succ).val (((x 0).val : ℤ) + shift))
  let e := fun k out a x => ‖F k out x - P.cellVector a k out x‖
  have he (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x, ∑ a, P.cellWeight a x * e k out a x) ≤ ε :=
    P.weighted_approximation k out
  have hpoint (a : Fin 3 → P.I) (x : Fin 3 → ZMod N) :
      ‖W.cubicAntisymmetricPair i j (x 1).val (x 2).val (((x 0).val : ℤ) + shift) - P.cellKernel a x‖ ≤
        e 0 i.1 a x + e 1 j.1 a x + e 0 i.2 a x + e 1 j.2 a x :=
    norm_cubic_pair_product_sub_le _ _ _ _ _ _ _ _
      (W.norm_eval _ _) (W.norm_eval _ _) (W.norm_eval _ _) (W.norm_eval _ _)
      (P.cellVector_norm _ _ _ _) (P.cellVector_norm _ _ _ _)
      (P.cellVector_norm _ _ _ _) (P.cellVector_norm _ _ _ _)
  calc
    _ ≤ 𝔼 x, ∑ a, P.cellWeight a x *
        (e 0 i.1 a x + e 1 j.1 a x + e 0 i.2 a x + e 1 j.2 a x) :=
      Finset.expect_le_expect (fun x _ => Finset.sum_le_sum
        (fun a _ => mul_le_mul_of_nonneg_left (hpoint a x) (P.cellWeight_nonneg a x)))
    _ = (𝔼 x, ∑ a, P.cellWeight a x * e 0 i.1 a x) +
        (𝔼 x, ∑ a, P.cellWeight a x * e 1 j.1 a x) +
        (𝔼 x, ∑ a, P.cellWeight a x * e 0 i.2 a x) +
        (𝔼 x, ∑ a, P.cellWeight a x * e 1 j.2 a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ ε + ε + ε + ε := add_le_add (add_le_add (add_le_add (he _ _) (he _ _)) (he _ _)) (he _ _)
    _ = _ := by ring

theorem kernel_approximation :
    (𝔼 x : Fin 3 → ZMod N,
      ‖W.cubicAntisymmetricPair i j (x 1).val (x 2).val (((x 0).val : ℤ) + shift) -
        ∑ a, (P.cellWeight a x : ℂ) * P.cellKernel a x‖) ≤ 4 * ε := by
  apply le_trans _ P.weighted_kernel_error
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.cellWeight a x) (fun a => P.cellKernel a x) _
    (fun a => P.cellWeight_nonneg a x) (P.cellWeight_total x))

theorem exists_correlating_cell (f : (Fin 3 → ZMod N) → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hf : ∀ x, ‖f x‖ ≤ 1) (herr : 4 * ε ≤ δ / 2)
    (hcorr : δ ≤ ‖𝔼 x, f x * star
      (W.cubicAntisymmetricPair i j (x 1).val (x 2).val (((x 0).val : ℤ) + shift))‖) :
    ∃ a : Fin 3 → P.I, δ / (2 * Real.exp b) ≤
      ‖𝔼 x, f x * star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ :=
  exists_correlating_summand_of_mean f _ (fun a x => (P.cellWeight a x : ℂ) * P.cellKernel a x)
    hδ (Real.exp_pos b) P.card_bound hf (P.kernel_approximation.trans herr) hcorr

end NativeCubicPairPartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem norm_unit_pair_products_sub_le {I : Type*} [Fintype I]
    (f g F G : I → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hG : ∀ i, ‖G i‖ ≤ 1) :
    ‖(∏ i, f i) * star (∏ i, g i) - (∏ i, F i) * star (∏ i, G i)‖ ≤
      (∑ i, ‖f i - F i‖) + ∑ i, ‖g i - G i‖ := by
  have hnorm (u : I → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1) : ‖∏ i, u i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hu i)
  have h := norm_unit_prod_sub_prod_le_sum Finset.univ
    ![∏ i, f i, star (∏ i, g i)] ![∏ i, F i, star (∏ i, G i)]
    (by intro k _; fin_cases k
        · exact hnorm f hf
        · change ‖star (∏ i, g i)‖ ≤ 1
          rw [norm_star]
          exact hnorm g hg)
    (by intro k _; fin_cases k
        · exact hnorm F hF
        · change ‖star (∏ i, G i)‖ ≤ 1
          rw [norm_star]
          exact hnorm G hG)
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.sum_univ_two] at h
  change ‖(∏ i, f i) * star (∏ i, g i) - (∏ i, F i) * star (∏ i, G i)‖ ≤
    ‖(∏ i, f i) - ∏ i, F i‖ + ‖star (∏ i, g i) - star (∏ i, G i)‖ at h
  rw [← star_sub, norm_star] at h
  exact h.trans (add_le_add
    (norm_unit_prod_sub_prod_le_sum Finset.univ f F (fun i _ => hf i) (fun i _ => hF i))
    (norm_unit_prod_sub_prod_le_sum Finset.univ g G (fun i _ => hg i) (fun i _ => hG i)))

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticTensorIndex (i : Fin (W.tensorPower 6).outputDim) : Fin 6 → Fin W.outputDim :=
  (tensorIndexEquiv W.outputDim 6).symm i

theorem quarticTensor_eval (i : Fin (W.tensorPower 6).outputDim) (x : QuarticReplicatedIndex → ℤ) :
    (W.tensorPower 6).eval i x = ∏ l, W.eval (W.quarticTensorIndex i l) x := rfl

end NativeMultidegreeNilcharacter

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}

namespace NativeQuarticPairPartition

attribute [local instance] NativeQuarticPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}
  (P : NativeQuarticPairPartition R b ε)

noncomputable def cellWeight (a : Fin 4 → P.I) (x : Fin 4 → ZMod N) : ℝ :=
  ∏ l, P.weight (a l) (x l)

theorem cellWeight_nonneg (a : Fin 4 → P.I) (x : Fin 4 → ZMod N) : 0 ≤ P.cellWeight a x :=
  Finset.prod_nonneg (fun l _ => ((P.positive (a l)).unit_interval (x l)).1)

theorem cellWeight_total (x : Fin 4 → ZMod N) : ∑ a, P.cellWeight a x = 1 :=
  sum_productPartitionWeight (fun _ : Fin 4 => P.weight) (fun _ => P.total) x

noncomputable def cellVector (a : Fin 4 → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 4 → ZMod N) : ℂ :=
  R.quarticPairAnchoredVector (fun l => ((P.anchor a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))

theorem cellVector_norm (a : Fin 4 → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 4 → ZMod N) : ‖P.cellVector a k out x‖ ≤ 1 :=
  R.quarticPairAnchoredVector_norm _ _ _ _

noncomputable def cellKernel (a : Fin 4 → P.I) (x : Fin 4 → ZMod N) : ℂ :=
  (∏ l, P.cellVector a 0 (W.quarticTensorIndex i l) x) *
    star (∏ l, P.cellVector a 1 (W.quarticTensorIndex j l) x)

theorem weighted_kernel_error :
    (𝔼 x : Fin 4 → ZMod N, ∑ a, P.cellWeight a x *
      ‖(W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ)) - P.cellKernel a x‖) ≤
        12 * ε := by
  let F := fun (k : Fin 2) (out : Fin W.outputDim) (x : Fin 4 → ZMod N) =>
    W.eval out (quarticInput ((x (![0, 1] k)).val : ℤ)
      ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)])
  let e := fun k out a x => ‖F k out x - P.cellVector a k out x‖
  have he (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x, ∑ a, P.cellWeight a x * e k out a x) ≤ ε := P.weighted_approximation k out
  have hpoint (a : Fin 4 → P.I) (x : Fin 4 → ZMod N) :
      ‖(W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ)) - P.cellKernel a x‖ ≤
        (∑ l, e 0 (W.quarticTensorIndex i l) a x) + ∑ l, e 1 (W.quarticTensorIndex j l) a x := by
    change ‖(∏ l, F 0 (W.quarticTensorIndex i l) x) * star (∏ l, F 1 (W.quarticTensorIndex j l) x) -
      (∏ l, P.cellVector a 0 (W.quarticTensorIndex i l) x) *
        star (∏ l, P.cellVector a 1 (W.quarticTensorIndex j l) x)‖ ≤ _
    exact norm_unit_pair_products_sub_le _ _ _ _
      (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun _ => P.cellVector_norm _ _ _ _) (fun _ => P.cellVector_norm _ _ _ _)
  have hsum (E : Fin 6 → (Fin 4 → P.I) → (Fin 4 → ZMod N) → ℝ) :
      (𝔼 x, ∑ a, P.cellWeight a x * ∑ l, E l a x) =
        ∑ l, 𝔼 x, ∑ a, P.cellWeight a x * E l a x := by
    calc
      _ = 𝔼 x, ∑ l, ∑ a, P.cellWeight a x * E l a x := by
        apply Finset.expect_congr rfl
        intro x _
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := Finset.expect_sum_comm _ _ _
  calc
    _ ≤ 𝔼 x, ∑ a, P.cellWeight a x *
        ((∑ l, e 0 (W.quarticTensorIndex i l) a x) + ∑ l, e 1 (W.quarticTensorIndex j l) a x) :=
      Finset.expect_le_expect (fun x _ => Finset.sum_le_sum
        (fun a _ => mul_le_mul_of_nonneg_left (hpoint a x) (P.cellWeight_nonneg a x)))
    _ = (∑ l, 𝔼 x, ∑ a, P.cellWeight a x * e 0 (W.quarticTensorIndex i l) a x) +
        ∑ l, 𝔼 x, ∑ a, P.cellWeight a x * e 1 (W.quarticTensorIndex j l) a x := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
      rw [hsum, hsum]
    _ ≤ (∑ _l : Fin 6, ε) + ∑ _l : Fin 6, ε :=
      add_le_add (Finset.sum_le_sum (fun l _ => he _ _)) (Finset.sum_le_sum (fun l _ => he _ _))
    _ = _ := by simp; ring

theorem kernel_approximation :
    (𝔼 x : Fin 4 → ZMod N,
      ‖(W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ)) -
        ∑ a, (P.cellWeight a x : ℂ) * P.cellKernel a x‖) ≤ 12 * ε := by
  apply le_trans _ P.weighted_kernel_error
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.cellWeight a x) (fun a => P.cellKernel a x) _
    (fun a => P.cellWeight_nonneg a x) (P.cellWeight_total x))

theorem exists_correlating_cell (f : (Fin 4 → ZMod N) → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hf : ∀ x, ‖f x‖ ≤ 1) (herr : 12 * ε ≤ δ / 2)
    (hcorr : δ ≤ ‖𝔼 x, f x * star
      ((W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ)))‖) :
    ∃ a : Fin 4 → P.I, δ / (2 * Real.exp b) ≤
      ‖𝔼 x, f x * star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ :=
  exists_correlating_summand_of_mean f _ (fun a x => (P.cellWeight a x : ℂ) * P.cellKernel a x)
    hδ (Real.exp_pos b) P.card_bound hf (P.kernel_approximation.trans herr) hcorr

end NativeQuarticPairPartition
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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

namespace NativeMixedPairPartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPairPartition R b ε)

noncomputable def cellWeight (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : ℝ :=
  ∏ l, P.weight (a l) (x l)

theorem cellWeight_nonneg (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : 0 ≤ P.cellWeight a x :=
  Finset.prod_nonneg (fun l _ => ((P.positive (a l)).unit_interval (x l)).1)

theorem cellWeight_total (x : Fin (n + 2) → ZMod N) : ∑ a, P.cellWeight a x = 1 :=
  sum_productPartitionWeight (fun _ : Fin (n + 2) => P.weight) (fun _ => P.total) x

noncomputable def cellVector (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ℂ :=
  R.mixedPairAnchoredVector (fun l => ((P.anchor a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))

theorem cellVector_norm (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ‖P.cellVector a k out x‖ ≤ 1 :=
  R.mixedPairAnchoredVector_norm _ _ _ _

noncomputable def cellKernel (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : ℂ :=
  (∏ l, P.cellVector a 0 ((tensorIndexEquiv W.outputDim m).symm i l) x) *
    star (∏ l, P.cellVector a 1 ((tensorIndexEquiv W.outputDim m).symm j l) x)

theorem weighted_kernel_error :
    (𝔼 x : Fin (n + 2) → ZMod N, ∑ a, P.cellWeight a x *
      ‖(W.tensorPower m).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)) - P.cellKernel a x‖) ≤
        2 * (m : ℝ) * ε := by
  let F := fun (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ZMod N) =>
    W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ)))
  let e := fun k out a x => ‖F k out x - P.cellVector a k out x‖
  have he (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x, ∑ a, P.cellWeight a x * e k out a x) ≤ ε := P.weighted_approximation k out
  have hpoint (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) :
      ‖(W.tensorPower m).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)) - P.cellKernel a x‖ ≤
        (∑ l, e 0 ((tensorIndexEquiv W.outputDim m).symm i l) a x) + ∑ l, e 1 ((tensorIndexEquiv W.outputDim m).symm j l) a x := by
    change ‖(∏ l, F 0 ((tensorIndexEquiv W.outputDim m).symm i l) x) * star (∏ l, F 1 ((tensorIndexEquiv W.outputDim m).symm j l) x) -
      (∏ l, P.cellVector a 0 ((tensorIndexEquiv W.outputDim m).symm i l) x) *
        star (∏ l, P.cellVector a 1 ((tensorIndexEquiv W.outputDim m).symm j l) x)‖ ≤ _
    exact norm_unit_pair_products_sub_le _ _ _ _
      (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun _ => P.cellVector_norm _ _ _ _) (fun _ => P.cellVector_norm _ _ _ _)
  have hsum (E : Fin m → (Fin (n + 2) → P.I) → (Fin (n + 2) → ZMod N) → ℝ) :
      (𝔼 x, ∑ a, P.cellWeight a x * ∑ l, E l a x) =
        ∑ l, 𝔼 x, ∑ a, P.cellWeight a x * E l a x := by
    calc
      _ = 𝔼 x, ∑ l, ∑ a, P.cellWeight a x * E l a x := by
        apply Finset.expect_congr rfl
        intro x _
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := Finset.expect_sum_comm _ _ _
  calc
    _ ≤ 𝔼 x, ∑ a, P.cellWeight a x *
        ((∑ l, e 0 ((tensorIndexEquiv W.outputDim m).symm i l) a x) + ∑ l, e 1 ((tensorIndexEquiv W.outputDim m).symm j l) a x) :=
      Finset.expect_le_expect (fun x _ => Finset.sum_le_sum
        (fun a _ => mul_le_mul_of_nonneg_left (hpoint a x) (P.cellWeight_nonneg a x)))
    _ = (∑ l, 𝔼 x, ∑ a, P.cellWeight a x * e 0 ((tensorIndexEquiv W.outputDim m).symm i l) a x) +
        ∑ l, 𝔼 x, ∑ a, P.cellWeight a x * e 1 ((tensorIndexEquiv W.outputDim m).symm j l) a x := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
      rw [hsum, hsum]
    _ ≤ (∑ _l : Fin m, ε) + ∑ _l : Fin m, ε :=
      add_le_add (Finset.sum_le_sum (fun l _ => he _ _)) (Finset.sum_le_sum (fun l _ => he _ _))
    _ = _ := by simp; ring

theorem kernel_approximation :
    (𝔼 x : Fin (n + 2) → ZMod N,
      ‖(W.tensorPower m).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)) -
        ∑ a, (P.cellWeight a x : ℂ) * P.cellKernel a x‖) ≤ 2 * (m : ℝ) * ε := by
  apply le_trans _ P.weighted_kernel_error
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.cellWeight a x) (fun a => P.cellKernel a x) _
    (fun a => P.cellWeight_nonneg a x) (P.cellWeight_total x))

theorem exists_correlating_cell (f : (Fin (n + 2) → ZMod N) → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hf : ∀ x, ‖f x‖ ≤ 1) (herr : 2 * (m : ℝ) * ε ≤ δ / 2)
    (hcorr : δ ≤ ‖𝔼 x, f x * star
      ((W.tensorPower m).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))‖) :
    ∃ a : Fin (n + 2) → P.I, δ / (2 * Real.exp b) ≤
      ‖𝔼 x, f x * star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ :=
  exists_correlating_summand_of_mean f _ (fun a x => (P.cellWeight a x : ℂ) * P.cellKernel a x)
    hδ (Real.exp_pos b) P.card_bound hf (P.kernel_approximation.trans herr) hcorr

end NativeMixedPairPartition
end Erdos3

end

end OAI
