import OAI.Combinatorics.Progressions.Lattices.BufferedIntegerLift

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem positive_score_discount_pointwise {a b W w δ ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w)
    (hlower : (1 - δ) * w ≤ W) (hupper : W ≤ (1 + δ) * w)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ) :
    (a - b) * W ≤ (1 + δ) * (a - (1 - ε) * b) * w := by
  have hpos := mul_le_mul_of_nonneg_left hupper ha
  have hneg := mul_le_mul_of_nonneg_left hlower hb
  have hbase := mul_le_mul_of_nonneg_right hdiscount (mul_nonneg hb hw)
  nlinarith

theorem positive_score_discount {Ω : Type*} [Fintype Ω]
    (a b W w : Ω → ℝ) {δ ε S : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hw : ∀ x, 0 ≤ w x)
    (hlower : ∀ x, (1 - δ) * w x ≤ W x) (hupper : ∀ x, W x ≤ (1 + δ) * w x)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : S ≤ 𝔼 x, (a x - b x) * W x) :
    S / (1 + δ) ≤ 𝔼 x, (a x - (1 - ε) * b x) * w x := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr
  calc
    S ≤ 𝔼 x, (a x - b x) * W x := hscore
    _ ≤ 𝔼 x, (1 + δ) * ((a x - (1 - ε) * b x) * w x) := by
      apply Finset.expect_le_expect
      intro x _
      simpa only [mul_assoc] using positive_score_discount_pointwise
        (ha x) (hb x) (hw x) (hlower x) (hupper x) hdiscount
    _ = _ := by rw [← Finset.mul_expect, mul_comm]

theorem quarter_discount_condition {ε : ℝ} (hε : 0 ≤ ε) :
    (1 + ε / 4) * (1 - ε) ≤ 1 - ε / 4 := by
  nlinarith [sq_nonneg ε]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem buffered_score_discount {Ω : Type*} [Fintype Ω] {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T W w : Ω → (Fin m → ℤ) → ℝ) (f : Ω → ℝ) {lam δ ε S : ℝ}
    (hδ : 0 ≤ δ) (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam)
    (hT : ∀ u β, 0 ≤ T u β) (hw : ∀ u β, 0 ≤ w u β)
    (hlower : ∀ u β, (1 - δ) * w u β ≤ W u β)
    (hupper : ∀ u β, W u β ≤ (1 + δ) * w u β)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : S ≤ 𝔼 u, (f u - lam) * ∑' β,
      χ.value (fun i => x u i - (β i : ℝ)) * W u β * T u β) :
    S / (1 + δ) ≤ 𝔼 u, (f u - (1 - ε) * lam) * ∑' β,
      χ.value (fun i => x u i - (β i : ℝ)) * w u β * T u β := by
  let β : Ω → Fin m → ℤ := fun u => nearestIntegerLift (x u)
  let cut : Ω → ℝ := fun u => χ.value (fun i => x u i - (β u i : ℝ)) * T u (β u)
  have hcut (u) : 0 ≤ cut u := mul_nonneg (χ.nonneg _) (hT u _)
  have hsum (U : Ω → (Fin m → ℤ) → ℝ) (u) :
      (∑' b, χ.value (fun i => x u i - (b i : ℝ)) * U u b * T u b) =
        χ.value (fun i => x u i - (β u i : ℝ)) * U u (β u) * T u (β u) := by
    simpa only [mul_assoc] using χ.buffered_sum_eq_nearest (x u) (fun b => U u b * T u b)
  have hsource : S ≤ 𝔼 u, (f u * cut u - lam * cut u) * W u (β u) := by
    apply hscore.trans_eq
    apply Finset.expect_congr rfl
    intro u _
    rw [hsum W]
    dsimp only [cut]
    ring
  have h := positive_score_discount (fun u => f u * cut u) (fun u => lam * cut u)
    (fun u => W u (β u)) (fun u => w u (β u)) hδ
    (fun u => mul_nonneg (hf u) (hcut u)) (fun u => mul_nonneg hlam (hcut u))
    (fun u => hw u _) (fun u => hlower u _) (fun u => hupper u _) hdiscount hsource
  apply h.trans_eq
  apply Finset.expect_congr rfl
  intro u _
  rw [hsum w]
  dsimp only [cut]
  ring

end Erdos3

end

end OAI
