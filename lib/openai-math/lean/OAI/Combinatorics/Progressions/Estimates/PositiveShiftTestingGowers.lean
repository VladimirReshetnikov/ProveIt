import OAI.Combinatorics.Progressions.Nilpotent.CyclicPairNiltestDetection
import OAI.Combinatorics.Progressions.Nilpotent.PositiveShiftTestingNiltests

namespace OAI

section

namespace Erdos3

theorem shift_detection_exponential_gap {p : ℝ} (hp : 2 ≤ p) :
    Real.exp (-6 * p) ≤
      Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) - Real.exp (-6 * p) := by
  have hthree : 3 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have htwo : 8 ≤ Real.exp (2 * p) := by
    have he : Real.exp (2 * p) = Real.exp p ^ 2 := by
      simpa using Real.exp_nat_mul p 2
    rw [he]
    nlinarith
  have hratio : Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) = Real.exp (-4 * p) / 4 := by
    calc
      _ = (Real.exp (-p) / Real.exp p) ^ 2 / 4 := by field_simp
      _ = _ := by
        rw [← Real.exp_sub, ← Real.exp_nat_mul]
        congr 2
        ring
  have hprod : Real.exp (-4 * p) = Real.exp (-6 * p) * Real.exp (2 * p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hratio, hprod]
  nlinarith [Real.exp_pos (-6 * p)]

def shiftDetectionLoss (s C : ℕ) (p : ℝ) : ℝ :=
  6 * p + (2 ^ (s + 1) : ℕ) * (6 * p + C) ^ C

theorem shiftDetectionLoss_nonneg (s C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ shiftDetectionLoss s C p := by unfold shiftDetectionLoss; positivity

theorem shift_detection_exponential_product (s C : ℕ) (p : ℝ) :
    Real.exp (-shiftDetectionLoss s C p) =
      Real.exp (-((6 * p + C) ^ C)) ^ (2 ^ (s + 1)) * Real.exp (-6 * p) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold shiftDetectionLoss
  ring

noncomputable def shiftDetectionPolynomial (s C : ℕ) : Polynomial ℕ :=
  Polynomial.C 6 * Polynomial.X + Polynomial.C (2 ^ (s + 1)) *
    (Polynomial.C 6 * Polynomial.X + Polynomial.C C) ^ C

theorem shiftDetectionPolynomial_eval (s C : ℕ) (p : ℝ) :
    (shiftDetectionPolynomial s C).eval₂ (Nat.castRingHom ℝ) p = shiftDetectionLoss s C p := by
  simp [shiftDetectionPolynomial, shiftDetectionLoss, Polynomial.eval₂_pow]

theorem exists_shiftDetectionLoss_fixed_power (s C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 2 ≤ p → shiftDetectionLoss s C p ≤ (p + 2) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_fixed_power_budget (shiftDetectionPolynomial s C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa only [shiftDetectionPolynomial_eval] using hbound p (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def CyclicShiftTestingDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Nonempty ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    2 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N], (∀ i (x : ZMod N), ‖(T i).eval (fun _ => (x.val : ℤ))‖ ≤ 1) →
    ∀ (v B : ZMod N → ℂ), (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖B x‖ ≤ Real.exp p) →
    Real.exp (-p) ≤ shiftTestingSeminorm B (fun i x => (T i).eval (fun _ => (x.val : ℤ))) v →
    Real.exp (-F p) ≤ gowersNorm (s + 2) v

theorem cyclicShiftTestingDetection_of_product.{u,v} {s C : ℕ}
    (hdet : CyclicProductNiltestDetection.{u,0} s (fun p => (p + C) ^ C)) :
    CyclicShiftTestingDetection.{u,v} s (shiftDetectionLoss s C) := by
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  have hp0 : 0 ≤ p := by linarith
  have hG : Real.exp (-((6 * p + C) ^ C)) ^ (2 ^ (s + 1)) *
      (Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) - Real.exp (-6 * p)) ≤
        gowersNorm (s + 2) v ^ (2 ^ (s + 2)) := by
    apply shiftTestingSeminorm_gowers_lower s v B
      (fun i x => (T i).eval (fun _ => (x.val : ℤ)))
      (Real.exp_pos _) (Real.exp_pos _) (Real.exp_nonneg _) (Real.exp_nonneg _)
      hv hB hunit hlarge
    intro i j a f hf hc
    apply cyclic_pair_niltest_detection hdet D (p := 6 * p) (by linarith) w hw T
      (fun i => (hT i).mono (by linarith)) N f hf i j a
    simpa only [neg_mul] using hc
  apply exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) v)
    (shiftDetectionLoss_nonneg s C hp0) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  rw [shift_detection_exponential_product]
  exact (mul_le_mul_of_nonneg_left (shift_detection_exponential_gap hp)
    (pow_nonneg (Real.exp_nonneg _) _)).trans hG

theorem exists_cyclicShiftTestingDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftTestingDetection.{u,v} s (fun p => (p + 2) ^ C) := by
  obtain ⟨c, _, hdet⟩ : ∃ c : ℕ, 2 ≤ c ∧
      CyclicProductNiltestDetection.{u,0} s (fun p => (p + c) ^ c) :=
    exists_cyclicProductNiltestDetection s
  obtain ⟨C, hC, hbudget⟩ := exists_shiftDetectionLoss_fixed_power s c
  have hraw : CyclicShiftTestingDetection.{u,v} s (shiftDetectionLoss s c) :=
    cyclicShiftTestingDetection_of_product (s := s) (C := c) (hdet := @hdet)
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (hraw D p hp w hw T hT N hunit v B hv hB hlarge)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem cyclic_translated_pair_niltest_detection.{u,v}
    {s : ℕ} {F : ℝ → ℝ} (hdet : CyclicProductNiltestDetection.{u,0} s F)
    {ι : Type v} {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {d : ι → ℕ} [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {p : ℝ} (hp : 2 ≤ p) (w : Fin 1 → ℕ) (hw : ∀ j, 0 < w j)
    (T : ∀ i, (D i).Niltest w) (hT : ∀ i, (T i).ComplexityLE p)
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (i j : ι) (b c : ZMod N)
    (hc : Real.exp (-p) ≤ ‖𝔼 x, f x * (T i).eval (fun _ => ((x + b).val : ℤ)) *
      star ((T j).eval (fun _ => ((x + c).val : ℤ)))‖) :
    Real.exp (-F p) ≤ gowersNorm (s + 1) f := by
  let index : Fin 2 → ι := ![i, j]
  let D' := fun k : Fin 2 => D (index k)
  let U : ∀ k : Fin 2, (D' k).Niltest w := fun k =>
    if k = 0 then (T (index k)).conjugate else T (index k)
  have hU : ∀ k, (U k).ComplexityLE p := by
    intro k
    dsimp only [U]
    split_ifs <;> exact hT (index k)
  let shifts : Fin 2 → ZMod N := ![b, c]
  have heval (x : ZMod N) :
      translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)) x =
        star ((T i).eval (fun _ => ((x + b).val : ℤ))) *
          (T j).eval (fun _ => ((x + c).val : ℤ)) := by
    simp [translatedCyclicProduct, Fin.prod_univ_two, shifts, U, D', index, add_comm]
    rfl
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)))‖ := by
    convert hc using 1
    congr 1
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro x _
    rw [heval]
    simp only [star_mul, star_star]
    ring
  exact hdet D' p (by linarith) (by simpa using hp) w hw U hU N shifts f hf hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def CyclicTranslatedShiftTestingDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Nonempty ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    2 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N], (∀ i (x : ZMod N), ‖(T i).eval (fun _ => (x.val : ℤ))‖ ≤ 1) →
    ∀ (v B : ZMod N → ℂ), (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖B x‖ ≤ Real.exp p) →
    Real.exp (-p) ≤ shiftTestingSeminorm B
      (translatedTestFamily (fun i x => (T i).eval (fun _ => (x.val : ℤ)))) v →
    Real.exp (-F p) ≤ gowersNorm (s + 2) v

theorem cyclicTranslatedShiftTestingDetection_of_product.{u,v} {s C : ℕ}
    (hdet : CyclicProductNiltestDetection.{u,0} s (fun p => (p + C) ^ C)) :
    CyclicTranslatedShiftTestingDetection.{u,v} s (shiftDetectionLoss s C) := by
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  have hp0 : 0 ≤ p := by linarith
  have hG : Real.exp (-((6 * p + C) ^ C)) ^ (2 ^ (s + 1)) *
      (Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) - Real.exp (-6 * p)) ≤
        gowersNorm (s + 2) v ^ (2 ^ (s + 2)) := by
    apply shiftTestingSeminorm_gowers_lower s v B
      (translatedTestFamily (fun i x => (T i).eval (fun _ => (x.val : ℤ))))
      (Real.exp_pos _) (Real.exp_pos _) (Real.exp_nonneg _) (Real.exp_nonneg _)
      hv hB (translatedTestFamily_norm_le_one _ hunit) hlarge
    intro i j a f hf hc
    apply cyclic_translated_pair_niltest_detection hdet D (p := 6 * p) (by linarith) w hw T
      (fun i => (hT i).mono (by linarith)) N f hf i.2 j.2 i.1 (a + j.1)
    simpa only [neg_mul, translatedTestFamily, add_assoc] using hc
  apply exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) v)
    (shiftDetectionLoss_nonneg s C hp0) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  rw [shift_detection_exponential_product]
  exact (mul_le_mul_of_nonneg_left (shift_detection_exponential_gap hp)
    (pow_nonneg (Real.exp_nonneg _) _)).trans hG

theorem exists_cyclicTranslatedShiftTestingDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicTranslatedShiftTestingDetection.{u,v} s (fun p => (p + 2) ^ C) := by
  obtain ⟨c, _, hdet⟩ : ∃ c : ℕ, 2 ≤ c ∧
      CyclicProductNiltestDetection.{u,0} s (fun p => (p + c) ^ c) :=
    exists_cyclicProductNiltestDetection s
  obtain ⟨C, hC, hbudget⟩ := exists_shiftDetectionLoss_fixed_power s c
  have hraw : CyclicTranslatedShiftTestingDetection.{u,v} s (shiftDetectionLoss s c) :=
    cyclicTranslatedShiftTestingDetection_of_product (s := s) (C := c) (hdet := @hdet)
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (hraw D p hp w hw T hT N hunit v B hv hB hlarge)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u

theorem shiftTestingSeminorm_eq_zero_of_isEmpty {G ι : Type*}
    [AddCommGroup G] [Fintype G] [IsEmpty ι] (B : G → ℂ) (T : ι → G → ℂ) (v : G → ℂ) :
    shiftTestingSeminorm B T v = 0 := by
  simp [shiftTestingSeminorm, shiftTestSeminormAt, Seminorm.sSup_empty]
  rfl

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_testingFamily_gowers_detection (s : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {p : ℝ}, 2 ≤ p → q + 2 ≤ p →
      ∀ v W : ZMod N → ℂ, (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖W x‖ ≤ Real.exp p) →
      (Real.exp (-p) ≤ shiftTestingSeminorm W B.testingFamily v →
        Real.exp (-((p + 2) ^ A)) ≤ gowersNorm (s + 2) v) ∧
      (Real.exp (-p) ≤ shiftTestingSeminorm W (translatedTestFamily B.testingFamily) v →
        Real.exp (-((p + 2) ^ A)) ≤ gowersNorm (s + 2) v) := by
  obtain ⟨A₁, hA₁, h₁⟩ : ∃ A : ℕ, 2 ≤ A ∧
      CyclicShiftTestingDetection.{u,0} s (fun p => (p + 2) ^ A) :=
    exists_cyclicShiftTestingDetection s
  obtain ⟨A₂, _, h₂⟩ : ∃ A : ℕ, 2 ≤ A ∧
      CyclicTranslatedShiftTestingDetection.{u,0} s (fun p => (p + 2) ^ A) :=
    exists_cyclicTranslatedShiftTestingDetection s
  refine ⟨max A₁ A₂, hA₁.trans (le_max_left _ _), ?_⟩
  intro N _ q a J B p hp hqp v W hv hW
  cases isEmpty_or_nonempty (ZMod N × Fin B.count) with
  | inl he =>
    let := he
    constructor <;> intro hlarge
    · rw [shiftTestingSeminorm_eq_zero_of_isEmpty] at hlarge
      exact False.elim ((not_le_of_gt (Real.exp_pos _)) hlarge)
    · rw [shiftTestingSeminorm_eq_zero_of_isEmpty] at hlarge
      exact False.elim ((not_le_of_gt (Real.exp_pos _)) hlarge)
  | inr he =>
    let := he
    have hT (i : ZMod N × Fin B.count) : (B.testingNiltest i).ComplexityLE p :=
      (B.testingNiltest_complexity i).mono hqp
    have hunit (i : ZMod N × Fin B.count) (x : ZMod N) :
        ‖(B.testingNiltest i).eval (fun _ => (x.val : ℤ))‖ ≤ 1 := by
      rw [B.testingNiltest_eval]
      exact B.testingFamily_norm_le i x
    have hbase : 1 ≤ p + 2 := by linarith
    constructor
    · intro hlarge
      apply (Real.exp_le_exp.mpr (neg_le_neg
        (pow_le_pow_right₀ hbase (le_max_left A₁ A₂)))).trans
      exact h₁ (ι := ZMod N × Fin B.count) (L := fun _ => B.L)
        (d := fun _ => B.dim) (fun _ => B.model) p hp (fun _ => 1)
        (fun _ => Nat.zero_lt_one) B.testingNiltest hT N hunit v W hv hW
        (by simpa only [B.testingNiltest_eval] using hlarge)
    · intro hlarge
      apply (Real.exp_le_exp.mpr (neg_le_neg
        (pow_le_pow_right₀ hbase (le_max_right A₁ A₂)))).trans
      exact h₂ (ι := ZMod N × Fin B.count) (L := fun _ => B.L)
        (d := fun _ => B.dim) (fun _ => B.model) p hp (fun _ => 1)
        (fun _ => Nat.zero_lt_one) B.testingNiltest hT N hunit v W hv hW
        (by simpa only [B.testingNiltest_eval] using hlarge)

end PositiveShiftBasis
end Erdos3

end

end OAI
