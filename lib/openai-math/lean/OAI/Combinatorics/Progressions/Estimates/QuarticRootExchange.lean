/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CoefficientTensorApproximation
import OAI.Combinatorics.Progressions.Estimates.QuarticDiagonalWrap
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerDivision

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_complex_inner_le_one {K : Type*} [Fintype K]
    (u v : K → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ k, ‖v k‖ ^ 2 = 1) :
    ‖∑ k, star (u k) * v k‖ ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖u k‖) (fun k => ‖v k‖)
  rw [hu, hv, one_mul] at hcs
  have hs : (∑ k, ‖u k‖ * ‖v k‖) ≤ 1 := by nlinarith
  exact (norm_sum_le _ _).trans (by simpa only [norm_mul, norm_star] using hs)

noncomputable def complexCrossContraction {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) : ℂ :=
  ∑ kl : K × L, (a * star (u kl.1)) * star (b * star (v kl.2)) * G kl.1 kl.2

theorem complexCrossContraction_rank_one {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u f : K → ℂ) (v g : L → ℂ) :
    complexCrossContraction a b u v (fun k l => f k * star (g l)) =
      (a * star b) * (∑ k, star (u k) * f k) * star (∑ l, star (v l) * g l) := by
  simp only [complexCrossContraction, Fintype.sum_prod_type, star_sum,
    star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem complexCrossContraction_unit {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1) :
    complexCrossContraction a b u v (fun k l => u k * star (v l)) = a * star b := by
  rw [complexCrossContraction_rank_one]
  have hU : ∑ k, star (u k) * u k = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution u hu 1).symm
  have hV : ∑ l, star (v l) * v l = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution v hv 1).symm
  rw [hU, hV, star_one, mul_one, mul_one]

theorem complexCrossContraction_sum {K L I : Type*}
    [Fintype K] [Fintype L] [Fintype I]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (w : I → ℂ) (G : I → K → L → ℂ) :
    complexCrossContraction a b u v (fun k l => ∑ i, w i * G i k l) =
      ∑ i, w i * complexCrossContraction a b u v (G i) := by
  simp only [complexCrossContraction, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro kl _
  ring

theorem norm_complexCrossContraction_positive_mixture {K L I : Type*}
    [Fintype K] [Fintype L] [Fintype I]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (w : I → ℝ)
    (f : I → K → ℂ) (g : I → L → ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1)
    (hw : ∀ i, 0 ≤ w i) (htotal : ∑ i, w i = 1)
    (hf : ∀ i, ∑ k, ‖f i k‖ ^ 2 = 1) (hg : ∀ i, ∑ l, ‖g i l‖ ^ 2 = 1) :
    ‖complexCrossContraction a b u v
      (fun k l => ∑ i, (w i : ℂ) * (f i k * star (g i l)))‖ ≤ 1 := by
  rw [complexCrossContraction_sum]
  apply norm_positive_partition_sum_le_one w _ hw htotal
  intro i
  rw [complexCrossContraction_rank_one, norm_mul, norm_mul, norm_mul, norm_star, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    (norm_unit_complex_inner_le_one v (g i) hv (hg i))
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    (norm_unit_complex_inner_le_one u (f i) hu (hf i))
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb

theorem norm_sub_complexCrossContraction_le_sum {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1)
    (hucap : ∀ k, ‖u k‖ ≤ 1) (hvcap : ∀ l, ‖v l‖ ≤ 1) :
    ‖a * star b - complexCrossContraction a b u v G‖ ≤
      ∑ kl : K × L, ‖u kl.1 * star (v kl.2) - G kl.1 kl.2‖ := by
  have hid : a * star b - complexCrossContraction a b u v G =
      ∑ kl : K × L, ((a * star (u kl.1)) * star (b * star (v kl.2))) *
        (u kl.1 * star (v kl.2) - G kl.1 kl.2) := by
    rw [← complexCrossContraction_unit a b u v hu hv]
    simp only [complexCrossContraction, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro kl _
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_star, norm_star, norm_mul, norm_star]
  refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
  · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hucap kl.1)
  · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvcap kl.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_complexCrossContraction_le_card {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) {B : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hv : ∀ l, ‖v l‖ ≤ 1) (hG : ∀ k l, ‖G k l‖ ≤ B) :
    ‖complexCrossContraction a b u v G‖ ≤ (Fintype.card (K × L) : ℝ) * B := by
  unfold complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : K × L, B := by
      apply Finset.sum_le_sum
      intro kl _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hG kl.1 kl.2)
      rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
      refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
      · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hu kl.1)
      · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hv kl.2)
    _ = _ := by simp

theorem mean_complexCrossContraction_error_le_card {K L X : Type*}
    [Fintype K] [Fintype L] [Fintype X]
    (a b : X → ℂ) (u : K → X → ℂ) (v : L → X → ℂ) (G : K → L → X → ℂ) {ε : ℝ}
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hu : ∀ x, ∑ k, ‖u k x‖ ^ 2 = 1) (hv : ∀ x, ∑ l, ‖v l x‖ ^ 2 = 1)
    (hucap : ∀ k x, ‖u k x‖ ≤ 1) (hvcap : ∀ l x, ‖v l x‖ ≤ 1)
    (herr : ∀ k l, (𝔼 x, ‖u k x * star (v l x) - G k l x‖) ≤ ε) :
    (𝔼 x, ‖a x * star (b x) - complexCrossContraction (a x) (b x)
      (fun k => u k x) (fun l => v l x) (fun k l => G k l x)‖) ≤
      (Fintype.card (K × L) : ℝ) * ε := by
  calc
    _ ≤ 𝔼 x, ∑ kl : K × L, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ := by
      apply Finset.expect_le_expect
      intro x _
      exact norm_sub_complexCrossContraction_le_sum (a x) (b x)
        (fun k => u k x) (fun l => v l x) (fun k l => G k l x)
        (ha x) (hb x) (hu x) (hv x) (fun k => hucap k x) (fun l => hvcap l x)
    _ = ∑ kl : K × L, 𝔼 x, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : K × L, ε := Finset.sum_le_sum (fun kl _ => herr kl.1 kl.2)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_cross_contraction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {a : J → (σ → ℤ) → ℂ} {u : K → (σ → ℤ) → ℂ}
      {b : L → (σ → ℤ) → ℂ} {v : M → (σ → ℤ) → ℂ}
      (G : K → M → (σ → ℤ) → ℂ),
      0 ≤ p → NativeIntegerVectorEquivalence s p a u → NativeIntegerVectorEquivalence s p b v →
      (∀ k m, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (G k m))) →
      ∀ j l, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
        (fun x => complexCrossContraction (a j x) (b l x)
          (fun k => u k x) (fun m => v m x) (fun k m => G k m x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p a u b v G hp E F hG j l
  classical
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hAt : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hterm (km : K × M) : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      ((t + A) ^ A) (fun x =>
        (a j x * star (u km.1 x)) * star (b l x * star (v km.2 x)) * G km.1 km.2 x)) := by
    obtain ⟨H⟩ := hmul hp (Classical.choice (E.expansion j km.1))
      (Classical.choice (F.expansion l km.2)).conjugate
    exact hmul ht (H.mono hAt) ((Classical.choice (hG km.1 km.2)).mono hpt)
  have hcard : (Fintype.card (K × M) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.right_dimension F.right_dimension (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  have hc : (∑ _ : K × M, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun km => Classical.choice (hterm km))
    (fun _ => 1) (by positivity : 0 ≤ 2 * p) hcard hc
  have hcost : (t + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by simpa only [one_mul, complexCrossContraction] using H.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

def quarticSampledInput (π : Fin 4 → Fin 2) (x : Fin 2 → ℤ) : QuarticReplicatedIndex → ℤ :=
  quarticInput (x (π 0)) ![x (π 1), x (π 2), x (π 3)]

theorem quarticSampledInput_map (π : Fin 4 → Fin 2) (g : ℤ → ℤ) (x : Fin 2 → ℤ) :
    quarticSampledInput π (fun k => g (x k)) = fun k => g (quarticSampledInput π x k) := by
  funext k
  rcases k with ⟨k, l⟩
  fin_cases k <;> fin_cases l <;> rfl

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem division_dilation_integer_representative (d : ℕ) [NeZero d]
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (x : σ → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      W.eval j (fun i => x i / (d : ℤ)) := by
  have hx : (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      (fun i => (d : ℤ) * (x i / (d : ℤ))) := by
    funext i
    rw [ZMod.val_intCast, sub_eq_iff_eq_add]
    simpa only [add_comm] using (Int.emod_add_mul_ediv (x i) (d : ℤ)).symm
  rw [hx]
  apply W.rationalDilation_eval_rescaled
  rw [Int.cast_natCast]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

theorem exists_quartic_rational_division_equivalence (d : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (π : Fin 4 → Fin 2),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) => (W.rationalDilation ((d : ℚ)⁻¹)).eval j (quarticSampledInput π x))
        (fun j x => W.eval j (quarticSampledInput π (fun k => x k / (d : ℤ)))) := by
  obtain ⟨A, _, hshift⟩ := exists_quartic_integer_translation_equivalence
  obtain ⟨B, _, hresidue⟩ := exists_pairResidueIndicator_expansion d 3 (by decide)
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro p W π
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation ((d : ℚ)⁻¹)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by
    have hpt : p ≤ t := by dsimp [t]; linarith
    linarith [sq_nonneg (d : ℝ)]
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let ρ : QuarticReplicatedIndex → Fin 2 := fun k =>
    if k.1 = 0 then π 0 else if k.2.val = 0 then π 1 else if k.2.val = 1 then π 2 else π 3
  let inp := quarticSampledInput π
  have hinput (x : Fin 2 → ℤ) : (fun k => x (ρ k)) = inp x := by
    funext k
    rcases k with ⟨k, l⟩
    fin_cases k <;> fin_cases l <;> rfl
  let F (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :=
    V.eval i (inp x) * star (V.eval j (inp (fun k => x k - ((r k).val : ℤ))))
  have hF (r : Fin 2 → ZMod d) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 t (F r)) := by
    obtain ⟨E⟩ := ((hshift V 0 (fun k => -((r (ρ k)).val : ℤ))).coordinatePullback ρ).expansion i j
    have hr (x : Fin 2 → ℤ) :
        (fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ)) =
          inp (fun k => x k - ((r k).val : ℤ)) := by
      calc
        _ = (fun k => x (ρ k) - ((r (ρ k)).val : ℤ)) := by
          funext k
          simp only [Pi.add_apply, sub_eq_add_neg]
        _ = _ := hinput (fun k => x k - ((r k).val : ℤ))
    have heq : (fun x : Fin 2 → ℤ => V.eval i ((fun k => x (ρ k)) + 0) *
        star (V.eval j ((fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ))))) = F r := by
      funext x
      rw [add_zero, hr, hinput]
    exact ⟨heq ▸ E.mono hat⟩
  have hterm (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
      ((t + D) ^ D) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hbt) (Classical.choice (hF r))
  have hcoeff : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcoeff
  have hrep (x : Fin 2 → ℤ) :
      V.eval j (inp (fun k => x k - ((x k : ZMod d).val : ℤ))) =
        W.eval j (inp (fun k => x k / (d : ℤ))) := by
    have hm := quarticSampledInput_map π (fun z => z - ((z : ZMod d).val : ℤ)) x
    have hd := quarticSampledInput_map π (fun z => z / (d : ℤ)) x
    have h := division_dilation_integer_representative d W (quarticSampledInput π x) j
    exact (congrArg ((W.rationalDilation ((d : ℚ)⁻¹)).eval j) hm).trans
      (h.trans (congrArg (W.eval j) hd).symm)
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => V.eval i (inp x) * star (W.eval j (inp (fun k => x k / (d : ℤ))))) := by
    funext x
    let r : Fin 2 → ZMod d := fun k => (x k : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul, F, hrep]
    · intro z _ hz
      have hne : (fun k => (x k : ZMod d)) ≠ z := fun h => hz h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticSwapSample (π : Fin 4 → Fin 2) : Fin 4 → Fin 2 := ![π 1, π 0, π 2, π 3]

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def divisionQuarticExchangeCorrection (d : ℕ)
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin 4 → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval a (quarticSampledInput π x))
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (quarticSampledInput (quarticSwapSample π) x))
    (fun i => W.eval i (quarticSampledInput π (fun k => x k / (d : ℤ))))
    (fun j => W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => x k / (d : ℤ))))
    (fun i j => G π i j (fun k => x k / (d : ℤ)))

theorem divisionQuarticExchangeCorrection_pointwise_error (d : ℕ)
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin 4 → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (quarticSampledInput π x) *
        star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (quarticSampledInput (quarticSwapSample π) x)) -
      W.divisionQuarticExchangeCorrection d G π a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.eval ij.1 (quarticSampledInput π (fun k => x k / (d : ℤ))) *
            star (W.eval ij.2 (quarticSampledInput (quarticSwapSample π) (fun k => x k / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => x k / (d : ℤ))‖ := by
  exact norm_sub_complexCrossContraction_le_sum _ _ _ _ _
    ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _) ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)

theorem divisionQuarticExchangeCorrection_mean_error (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin 4 → Fin 2) (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b
            (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.divisionQuarticExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.divisionQuarticExchangeCorrection_pointwise_error d G π a b
      (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.eval ij.1 (quarticSampledInput π (fun k => ((x k).val : ℤ) / (d : ℤ))) *
            star (W.eval ij.2 (quarticSampledInput (quarticSwapSample π)
              (fun k => ((x k).val : ℤ) / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => ((x k).val : ℤ) / (d : ℤ))‖) ≤ (d : ℝ) ^ 2 * ε := by
    have h := expect_pair_cyclicDivision_le d (fun x : Fin 2 → ZMod N =>
      ‖W.eval ij.1 (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval ij.2 (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicDivision_val, Int.natCast_ediv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr π ij.1 ij.2) (sq_nonneg _))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, (d : ℝ) ^ 2 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem divisionQuarticExchangeCorrection_norm (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin 4 → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.divisionQuarticExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold divisionQuarticExchangeCorrection complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      · have h := hG π ij.1 ij.2 (fun k => cyclicDivision d (x k))
        simpa only [cyclicDivision_val, Int.natCast_ediv] using h
      · rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
        refine (mul_le_of_le_one_left
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
        · exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _)
        · exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

theorem exists_divisionQuarticExchangeCorrection_expansion (d : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p), 0 ≤ q →
      ∀ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + C) ^ C)
        (W.divisionQuarticExchangeCorrection d G π a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_quartic_rational_division_equivalence d
  obtain ⟨B, _, hdivision⟩ := NativeIntegerExpansion.exists_division_expansion d 3 (by decide)
  obtain ⟨D, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) B
  have hF (i j : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 t
      (fun x => G π i j (fun k => x k / (d : ℤ)))) :=
    ⟨(Classical.choice (hdivision hq (Classical.choice (hG π i j)))).mono hBt⟩
  have H := hcontract (fun i j x => G π i j (fun k => x k / (d : ℤ))) ht
    ((hcompare W π).mono hAt) ((hcompare W (quarticSwapSample π)).mono hAt) hF a b
  have hcost : (t + D) ^ D ≤ (p + q + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨(Classical.choice H).mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_sampled_rational_division_equivalence (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ k, bound k) = s + 1 → ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter bound p) (ρ : σ → Fin 2),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) => (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun k => x (ρ k)))
        (fun j x => W.eval j (fun k => x (ρ k) / (d : ℤ))) := by
  obtain ⟨A, _, hshift⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W ρ
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation ((d : ℚ)⁻¹)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by
    have hpt : p ≤ t := by dsimp [t]; linarith
    linarith [sq_nonneg (d : ℝ)]
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let inp (x : Fin 2 → ℤ) : σ → ℤ := fun k => x (ρ k)
  have hinput (x : Fin 2 → ℤ) : (fun k => x (ρ k)) = inp x := rfl
  let F (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :=
    V.eval i (inp x) * star (V.eval j (inp (fun k => x k - ((r k).val : ℤ))))
  have hF (r : Fin 2 → ZMod d) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (F r)) := by
    obtain ⟨E⟩ := ((hshift bound hdegree V 0 (fun k => -((r (ρ k)).val : ℤ))).coordinatePullback ρ).expansion i j
    have hr (x : Fin 2 → ℤ) :
        (fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ)) =
          inp (fun k => x k - ((r k).val : ℤ)) := by
      calc
        _ = (fun k => x (ρ k) - ((r (ρ k)).val : ℤ)) := by
          funext k
          simp only [Pi.add_apply, sub_eq_add_neg]
        _ = _ := hinput (fun k => x k - ((r k).val : ℤ))
    have heq : (fun x : Fin 2 → ℤ => V.eval i ((fun k => x (ρ k)) + 0) *
        star (V.eval j ((fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ))))) = F r := by
      funext x
      rw [add_zero, hr, hinput]
    exact ⟨heq ▸ E.mono hat⟩
  have hterm (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + D) ^ D) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hbt) (Classical.choice (hF r))
  have hcoeff : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcoeff
  have hrep (x : Fin 2 → ℤ) :
      V.eval j (inp (fun k => x k - ((x k : ZMod d).val : ℤ))) =
        W.eval j (inp (fun k => x k / (d : ℤ))) := by
    exact division_dilation_integer_representative d W (inp x) j
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => V.eval i (inp x) * star (W.eval j (inp (fun k => x k / (d : ℤ))))) := by
    funext x
    let r : Fin 2 → ZMod d := fun k => (x k : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul, F, hrep]
    · intro z _ hz
      have hne : (fun k => (x k : ZMod d)) ≠ z := fun h => hz h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticTensorExchangeCorrection (n : ℕ)
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin 4 → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) : ℂ :=
  ∏ k : Fin n, G π ((tensorIndexEquiv W.outputDim n).symm a k)
    ((tensorIndexEquiv W.outputDim n).symm b k) x

theorem quarticTensorExchange_kernel (n : ℕ) (π : Fin 4 → Fin 2)
    (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) :
    (W.tensorPower n).eval a (quarticSampledInput π x) *
        star ((W.tensorPower n).eval b (quarticSampledInput (quarticSwapSample π) x)) =
      ∏ k : Fin n, W.eval ((tensorIndexEquiv W.outputDim n).symm a k) (quarticSampledInput π x) *
        star (W.eval ((tensorIndexEquiv W.outputDim n).symm b k)
          (quarticSampledInput (quarticSwapSample π) x)) := by
  simp only [tensorPower_eval, star_prod, Finset.prod_mul_distrib]

theorem quarticTensorExchangeCorrection_norm (n : ℕ) {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin 4 → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ZMod N) :
    ‖W.quarticTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖ ≤ B ^ n := by
  rw [quarticTensorExchangeCorrection, norm_prod]
  calc
    _ ≤ ∏ _ : Fin n, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hG _ _ _ x)
    _ = _ := by simp

theorem quarticTensorExchangeCorrection_mean_error (n : ℕ) {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin 4 → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower n).eval a (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.tensorPower n).eval b
            (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.quarticTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖) ≤ B ^ n * (n * ε) := by
  let i := (tensorIndexEquiv W.outputDim n).symm a
  let j := (tensorIndexEquiv W.outputDim n).symm b
  have h := mean_prod_error_le
    (fun k (x : Fin 2 → ZMod N) =>
      W.eval (i k) (quarticSampledInput π (fun l => ((x l).val : ℤ))) *
        star (W.eval (j k) (quarticSampledInput (quarticSwapSample π) (fun l => ((x l).val : ℤ)))))
    (fun k (x : Fin 2 → ZMod N) => G π (i k) (j k) (fun l => ((x l).val : ℤ))) hB
    (fun k x => (by
      rw [norm_mul, norm_star]
      exact ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
        (W.norm_eval _ _)).trans hB))
    (fun _ x => hG _ _ _ x) (fun k => herr π (i k) (j k))
  simpa only [Fintype.card_fin, quarticTensorExchange_kernel, quarticTensorExchangeCorrection, i, j] using h

theorem exists_quarticTensorExchangeCorrection_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p), 0 ≤ q →
      ∀ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((q + C) ^ C)
        (W.quarticTensorExchangeCorrection n G π a b)) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  exact hprod _ hq (fun _ => hG _ _ _)

theorem dilationTensorQuarticExchangeCorrection_mean_error (d n : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin 4 → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval a
            (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval b
            (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        (W.rationalDilation ((d : ℚ)⁻¹)).quarticTensorExchangeCorrection n
          (W.divisionQuarticExchangeCorrection d G) π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * n) * (n * ((d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hH (π : Fin 4 → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionQuarticExchangeCorrection d G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionQuarticExchangeCorrection_norm d G hG π i j x
  have h := (W.rationalDilation ((d : ℚ)⁻¹)).quarticTensorExchangeCorrection_mean_error n
    (W.divisionQuarticExchangeCorrection d G) hB hH
    (W.divisionQuarticExchangeCorrection_mean_error d G herr) π a b
  simpa only [← pow_mul] using h

noncomputable def quarticRootExchangeCorrection
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (((4 : ℕ) : ℚ)⁻¹)).quarticTensorExchangeCorrection 64 (W.divisionQuarticExchangeCorrection 4 G)

theorem quarticRootExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (π : Fin 4 → Fin 2) (a b : Fin W.quarticRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quarticRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 128 := by
  have hH (π : Fin 4 → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionQuarticExchangeCorrection 4 G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionQuarticExchangeCorrection_norm 4 G hG π i j x
  simpa only [quarticRootExchangeCorrection, ← pow_mul] using
    (W.rationalDilation (((4 : ℕ) : ℚ)⁻¹)).quarticTensorExchangeCorrection_norm 64
      (W.divisionQuarticExchangeCorrection 4 G) hH π a b x

theorem quarticRootExchangeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin 4 → Fin 2) (a b : Fin W.quarticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRoot.eval a (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.quarticRoot.eval b
            (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.quarticRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖) ≤
      1024 * (W.outputDim : ℝ) ^ 130 * ε := by
  have h := W.dilationTensorQuarticExchangeCorrection_mean_error 4 64 G hG herr π a b
  exact h.trans_eq (by
    norm_num only [Nat.cast_ofNat]
    change (W.outputDim : ℝ) ^ 128 * (64 * (16 * (W.outputDim : ℝ) ^ 2 * ε)) = _
    calc
      _ = (64 * 16 : ℝ) * ((W.outputDim : ℝ) ^ 128 * (W.outputDim : ℝ) ^ 2) * ε := by ac_rfl
      _ = _ := by rw [← pow_add]; norm_num)

theorem exists_quarticRootExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p), 0 ≤ q →
      ∀ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + C) ^ C)
        (W.quarticRootExchangeCorrection G π a b)) := by
  obtain ⟨A, _, hdivision⟩ := exists_divisionQuarticExchangeCorrection_expansion 4
  obtain ⟨B, _, htensor⟩ := exists_quarticTensorExchangeCorrection_expansion 64
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := htensor (W.rationalDilation (((4 : ℕ) : ℚ)⁻¹)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.divisionQuarticExchangeCorrection 4 G) (hdivision W hq G hG) π a b
  have hcost : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
