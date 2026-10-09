import GowersSzemeredi.Proofs16BipartiteQuasirandom

/-! One-sided quasirandomness implies quasirandomness: a sharper [49]
Lemma 44.

[49] Lemma 44 assumes, for a bipartite graph on `X × Y`,
* (19) `E_x ||N_x| − δ|Y|| ≤ ε|Y|` (degrees), and
* (20) `E_{x,x′} ||N_x ∩ N_{x′}| − δ²|Y|| ≤ ε|Y|` (codegrees),

and concludes that the graph is `3ε^{1/8}`-quasirandom. Its proof uses
Markov's inequality on the good pairs, and the triangle inequality for the
box norm to pass from `δ` to the actual density.

A direct argument gives more. With `f = G − δ` and `c(x,x′) = Σ_y f(x,y)f(x′,y)`,
* `c = (codeg − δ²|Y|) − δ(deg x − δ|Y|) − δ(deg x′ − δ|Y|)`
  (`codegree_correlation_eq`), and
* `|c| ≤ |Y|`, since `|f| ≤ 1`.

So `c² ≤ |Y|·|c|`, and summing over pairs gives
`boxSum (G − δ) ≤ 3ε|X|²|Y|²` (`boxSum_le_of_codegrees`). That is,
`‖G − δ‖□ ≤ (3ε)^{1/4}` with respect to the given `δ`. No Markov step and
no box-norm triangle inequality are needed. The density statement
`|δ′ − δ| ≤ ε` is `total_mass_sub_le_of_degrees`.

`common_neighbourhood_deviation_of_codegrees` combines this with
`common_neighbourhood_deviation_card` (Lemma 43): degree and codegree
control alone bound the number of `I`-tuples with an atypical common
neighbourhood count by `4|I||J|(3ε)^{1/4}η⁻²|X^I|`. The hypotheses are
stated for `[0,1]`-valued `G`, which includes graphs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The correlation of two rows of `G − δ` in terms of degrees and codegrees. -/
theorem codegree_correlation_eq (G : X → Y → ℝ) (δ : ℝ) (x x' : X) :
    ∑ y, (G x y - δ) * (G x' y - δ) =
      (∑ y, G x y * G x' y - δ ^ 2 * Fintype.card Y) -
        δ * (∑ y, G x y - δ * Fintype.card Y) - δ * (∑ y, G x' y - δ * Fintype.card Y) := by
  have h : ∀ y, (G x y - δ) * (G x' y - δ) =
      G x y * G x' y - δ * G x y - δ * G x' y + δ ^ 2 := fun y => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **The density is close to `δ`.** -/
theorem total_mass_sub_le_of_degrees {G : X → Y → ℝ} {δ ε : ℝ}
    (h19 : ∑ x, |∑ y, G x y - δ * Fintype.card Y| ≤ ε * Fintype.card X * Fintype.card Y) :
    |∑ x, ∑ y, G x y - δ * Fintype.card X * Fintype.card Y| ≤
      ε * Fintype.card X * Fintype.card Y := by
  have h : ∑ x, ∑ y, G x y - δ * Fintype.card X * Fintype.card Y =
      ∑ x, (∑ y, G x y - δ * Fintype.card Y) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [h]
  exact (Finset.abs_sum_le_sum_abs _ _).trans h19

/-- **[49] Lemma 44, sharpened.** Degree and codegree control give
`boxSum (G − δ) ≤ 3ε|X|²|Y|²`. -/
theorem boxSum_le_of_codegrees {G : X → Y → ℝ} {δ ε : ℝ}
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h19 : ∑ x, |∑ y, G x y - δ * Fintype.card Y| ≤ ε * Fintype.card X * Fintype.card Y)
    (h20 : ∑ x, ∑ x', |∑ y, G x y * G x' y - δ ^ 2 * Fintype.card Y| ≤
      ε * (Fintype.card X : ℝ) ^ 2 * Fintype.card Y) :
    boxSum (fun x y => G x y - δ) ≤
      3 * ε * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 := by
  obtain ⟨NX, hNX⟩ : ∃ NX : ℝ, NX = Fintype.card X := ⟨_, rfl⟩
  obtain ⟨NY, hNY⟩ : ∃ NY : ℝ, NY = Fintype.card Y := ⟨_, rfl⟩
  rw [← hNX, ← hNY] at h19 h20 ⊢
  obtain ⟨B, hB⟩ : ∃ B : X → ℝ, B = fun x => ∑ y, G x y - δ * NY := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : X → X → ℝ, A = fun x x' => ∑ y, G x y * G x' y - δ ^ 2 * NY :=
    ⟨_, rfl⟩
  have hNY0 : 0 ≤ NY := by rw [hNY]; positivity
  have hNX0 : 0 ≤ NX := by rw [hNX]; positivity
  -- each row correlation is bounded by `|Y|` and by the degree/codegree defects
  have hpair : ∀ x x', (∑ y, (G x y - δ) * (G x' y - δ)) ^ 2 ≤
      NY * (|A x x'| + δ * |B x| + δ * |B x'|) := by
    intro x x'
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ y, (G x y - δ) * (G x' y - δ) := ⟨_, rfl⟩
    rw [← hc]
    have hcY : |c| ≤ NY := by
      rw [hc]
      calc |∑ y, (G x y - δ) * (G x' y - δ)| ≤ ∑ y, |(G x y - δ) * (G x' y - δ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y : Y, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro y _
            rw [abs_mul]
            have h1 : |G x y - δ| ≤ 1 := abs_le.mpr ⟨by linarith [hG0 x y], by linarith [hG1 x y]⟩
            have h2 : |G x' y - δ| ≤ 1 :=
              abs_le.mpr ⟨by linarith [hG0 x' y], by linarith [hG1 x' y]⟩
            exact mul_le_one₀ h1 (abs_nonneg _) h2
        _ = NY := by rw [hNY]; simp
    have hcdef : |c| ≤ |A x x'| + δ * |B x| + δ * |B x'| := by
      rw [hc, codegree_correlation_eq, ← hNY]
      have e : (∑ y, G x y * G x' y - δ ^ 2 * NY) - δ * (∑ y, G x y - δ * NY) -
          δ * (∑ y, G x' y - δ * NY) = A x x' - δ * B x - δ * B x' := by
        rw [hA, hB]
      rw [e]
      calc |A x x' - δ * B x - δ * B x'| ≤ |A x x' - δ * B x| + |δ * B x'| := abs_sub _ _
        _ ≤ |A x x'| + |δ * B x| + |δ * B x'| := by linarith [abs_sub (A x x') (δ * B x)]
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hδ0]
    calc c ^ 2 = |c| * |c| := by rw [← sq_abs, sq]
      _ ≤ NY * |c| := mul_le_mul_of_nonneg_right hcY (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hcdef hNY0
  have hsumB : ∑ x, |B x| ≤ ε * NX * NY := by rw [hB]; exact h19
  have hsumA : ∑ x, ∑ x', |A x x'| ≤ ε * NX ^ 2 * NY := by rw [hA]; exact h20
  have hcardX : (Fintype.card X : ℝ) = NX := hNX.symm
  have hexpand : ∑ x, ∑ x', NY * (|A x x'| + δ * |B x| + δ * |B x'|) =
      NY * (∑ x, ∑ x', |A x x'|) + 2 * (NY * δ * NX) * ∑ x, |B x| := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcardX]
    ring
  have hB0 : 0 ≤ ∑ x, |B x| := by positivity
  have hδB : δ * ∑ x, |B x| ≤ ε * NX * NY := by
    calc δ * ∑ x, |B x| ≤ 1 * ∑ x, |B x| := mul_le_mul_of_nonneg_right hδ1 hB0
      _ ≤ _ := by rw [one_mul]; exact hsumB
  unfold boxSum
  calc ∑ x, ∑ x', (∑ y, (G x y - δ) * (G x' y - δ)) ^ 2
      ≤ ∑ x, ∑ x', NY * (|A x x'| + δ * |B x| + δ * |B x'|) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hpair x x'
    _ = NY * (∑ x, ∑ x', |A x x'|) + 2 * (NY * NX) * (δ * ∑ x, |B x|) := by
        rw [hexpand]; ring
    _ ≤ NY * (ε * NX ^ 2 * NY) + 2 * (NY * NX) * (ε * NX * NY) := by
        have hNYNX : 0 ≤ 2 * (NY * NX) := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hsumA hNY0)
          (mul_le_mul_of_nonneg_left hδB hNYNX)
    _ = 3 * ε * NX ^ 2 * NY ^ 2 := by ring

/-- **Lemma 43 from degree and codegree control.** -/
theorem common_neighbourhood_deviation_of_codegrees {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [DecidableEq Y] [Nonempty Y] {G : X → Y → ℝ} {δ ε : ℝ}
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε)
    (h19 : ∑ x, |∑ y, G x y - δ * Fintype.card Y| ≤ ε * Fintype.card X * Fintype.card Y)
    (h20 : ∑ x, ∑ x', |∑ y, G x y * G x' y - δ ^ 2 * Fintype.card Y| ≤
      ε * (Fintype.card X : ℝ) ^ 2 * Fintype.card Y)
    (M : Finset (J → Y)) {η : ℝ} (hη : 0 ≤ η) :
    ((Finset.univ.filter fun x : I → X => η * Fintype.card (J → Y) ≤
        |commonCount G M x - δ ^ (Fintype.card I * Fintype.card J) * M.card|).card : ℝ) *
        η ^ 2 ≤
      4 * Fintype.card I * Fintype.card J * (3 * ε) ^ ((1 : ℝ) / 4) *
        Fintype.card (I → X) := by
  have h3 : (0 : ℝ) ≤ 3 * ε := by positivity
  have hroot : ((3 * ε) ^ ((1 : ℝ) / 4)) ^ 4 = 3 * ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h3]
    norm_num
  have hbox := boxSum_le_of_codegrees hG0 hG1 hδ0 hδ1 h19 h20
  apply common_neighbourhood_deviation_card hG0 hG1 hδ0 hδ1 (by positivity) _ M hη
  rw [hroot]
  exact hbox

end LeanProofs.GowersSzemeredi
