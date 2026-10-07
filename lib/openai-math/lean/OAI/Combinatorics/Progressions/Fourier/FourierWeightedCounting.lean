import OAI.Combinatorics.Progressions.Estimates.ConfigurationCenteredCounting
import OAI.Combinatorics.Progressions.Estimates.WeightedCenteredExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def configurationFourierWeight {R J : Type*} [AddMonoid R] [Fintype J]
    (c : J → ℂ) (Psi : J → AddChar (R × R) ℂ) (z : R × R) : ℂ :=
  ∑ j, c j * Psi j z

theorem exists_fourier_weighted_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ∀ S : Finset I, S.card ≤ s + 2 →
      ∀ {J : Type} [Fintype J] (c : J → ℂ) (Psi : J → AddChar (ZMod N × ZMod N) ℂ),
        ‖(𝔼 x, 𝔼 d, configurationFourierWeight c Psi (x, d) *
            (∏ i ∈ S, (mu (x + slopes i * d) : ℂ))) -
          (𝔼 x, 𝔼 d, configurationFourierWeight c Psi (x, d))‖ ≤ (∑ j, ‖c j‖) * epsilon := by
  let delta := epsilon / (2 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_configuration_centered_counting s hs hdelta
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes hsep S hS J _ c Psi
  let F : I → (ZMod N × ZMod N) → ℂ := fun i z => (mu (z.1 + slopes i * z.2) : ℂ)
  let W := configurationFourierWeight c Psi
  let L : ℝ := ∑ j, ‖c j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hcenter (U : Finset I) (hUS : U ⊆ S) (hU : U.Nonempty) :
      ‖𝔼 z, W z * (∏ i ∈ U, (F i z - 1))‖ ≤ L * delta := by
    let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
    apply norm_expect_finite_weighted_sum_le c (fun j z => Psi j z) (fun z => ∏ i ∈ U, (F i z - 1))
    intro j
    have hcard : Fintype.card U ≤ s + 2 := by
      simpa only [Fintype.card_coe] using (Finset.card_le_card hUS).trans hS
    have h := hcount hp hodd hN mu hmu hmean hcompare (I := U) hcard
      (fun i => slopes i.val)
      (fun i k hik => hsep i.val k.val (fun h => hik (Subtype.ext h))) (Psi j)
    have hprod (x d : ZMod N) :
        (∏ i : U, ((mu (x + slopes i.val * d) - 1 : ℝ) : ℂ)) =
          ∏ i ∈ U, ((mu (x + slopes i * d) - 1 : ℝ) : ℂ) :=
      Finset.prod_coe_sort (s := U) (f := fun i : I => ((mu (x + slopes i * d) - 1 : ℝ) : ℂ))
    simp only [hprod] at h
    rw [expect_prod_split]
    simpa only [F, Complex.ofReal_sub, Complex.ofReal_one] using h
  have h := weighted_product_count_of_centered S F W (mul_nonneg hL hdelta.le) hcenter
  have hbound : (2 : ℝ) ^ S.card * (L * delta) ≤ L * epsilon := by
    calc
      _ = L * ((2 : ℝ) ^ S.card * delta) := by ring
      _ ≤ L * ((2 : ℝ) ^ (s + 2) * delta) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hS) hdelta.le) hL
      _ = L * epsilon := by congr 1; dsimp [delta]; field_simp
  simpa only [expect_prod_split, F, W, L] using h.trans hbound

end Erdos3

end

end OAI
