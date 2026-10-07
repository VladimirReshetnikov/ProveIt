import GowersSzemeredi.Proofs13EndpointFourierTransfer
import GowersSzemeredi.Proofs13FejerRelations

/-! Normalized Fourier coefficients and a coherent dominant-frequency
choice. For a unit-modulus function its selected squared coefficient is
at least the normalized second cube mean. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def endpointFourierCoefficient {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) : Complex := fourier g r / (N : Complex)

theorem endpointFourierCoefficient_norm {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) :
    ‖endpointFourierCoefficient g r‖ = ‖fourier g r‖ / (N : Real) := by
  simp [endpointFourierCoefficient]

theorem endpointFourierCoefficient_eq_expect {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) :
    endpointFourierCoefficient g r = 𝔼 x : ZMod N, exponential ((-r) * x) * g x := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [endpointFourierCoefficient, fourier, ZMod.dft_apply, ZMod.card, smul_eq_mul, exponential]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  ring

theorem endpointFourierCoefficient_norm_le_one {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (r : ZMod N) :
    ‖endpointFourierCoefficient g r‖ ≤ 1 := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  rw [endpointFourierCoefficient_norm, div_le_one hn]
  have h0 : fourier (fun _ : ZMod N => (0 : Complex)) r = 0 := by simp [fourier, ZMod.dft_apply]
  have ht := fourier_norm_sub_le_L1 g (fun _ => 0) r
  rw [h0, sub_zero] at ht
  have he : endpointL1Distance g (fun _ => 0) ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [sub_zero] using hg x
  exact ht.trans ((mul_le_mul_of_nonneg_left he hn.le).trans_eq (mul_one _))

theorem endpointFourierCoefficient_parseval {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) :
    ∑ r : ZMod N, ‖endpointFourierCoefficient g r‖ ^ 2 = 1 := by
  have hn : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp_rw [endpointFourierCoefficient_norm, div_pow]
  rw [← Finset.sum_div, identity_2_3_holds N g]
  simp only [hg, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  field_simp

private theorem endpoint_fourthMoment {N : Nat} [NeZero N] (g : ZMod N → Complex) :
    (∑ r : ZMod N, ‖fourier g r‖ ^ 4) =
      (N : Real) * ∑ a : Point N 1, ‖∑ x : ZMod N, cubeDifference g a x‖ ^ 2 := by
  have hone (a : Point N 1) : cubeDifference g a = difference g (a 0) := by
    funext x
    simp only [cubeDifference, List.ofFn_succ, List.ofFn_zero, iteratedDifference]
  have he := (Equiv.funUnique (Fin 1) (ZMod N)).sum_comp
    (fun r => ‖∑ x : ZMod N, difference g r x‖ ^ 2)
  have he' : (∑ a : Point N 1, ‖∑ x : ZMod N, cubeDifference g a x‖ ^ 2) =
      ∑ r : ZMod N, ‖∑ x : ZMod N, difference g r x‖ ^ 2 := by
    simpa [hone, Equiv.funUnique] using he
  rw [he']
  simpa only [difference, ← pow_add] using lemma_2_1_holds N g g

theorem endpointFourierCoefficient_fourthMoment {N : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ r : ZMod N, ‖endpointFourierCoefficient g r‖ ^ 4 = endpointCubeMean g 2 := by
  have hn : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp_rw [endpointFourierCoefficient_norm, div_pow]
  rw [← Finset.sum_div, endpoint_fourthMoment, endpointCubeMean_succ (d := 1)]
  field_simp
  ring

theorem endpoint_exists_dominantFrequency {N : Nat} [NeZero N] (g : ZMod N → Complex) :
    ∃ r : ZMod N, ∀ s, ‖endpointFourierCoefficient g s‖ ≤ ‖endpointFourierCoefficient g r‖ := by
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun r => ‖endpointFourierCoefficient g r‖) Finset.univ_nonempty
  exact ⟨r, fun s => hr s (Finset.mem_univ _)⟩

def endpointDominantFrequency {N : Nat} [NeZero N] (g : ZMod N → Complex) : ZMod N :=
  Classical.choose (endpoint_exists_dominantFrequency g)

theorem endpointDominantFrequency_max {N : Nat} [NeZero N] (g : ZMod N → Complex) (s : ZMod N) :
    ‖endpointFourierCoefficient g s‖ ≤ ‖endpointFourierCoefficient g (endpointDominantFrequency g)‖ :=
  Classical.choose_spec (endpoint_exists_dominantFrequency g) s

theorem endpointDominantFrequency_concentration {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) :
    endpointCubeMean g 2 ≤ ‖endpointFourierCoefficient g (endpointDominantFrequency g)‖ ^ 2 := by
  rw [← endpointFourierCoefficient_fourthMoment]
  calc
    _ ≤ ∑ r : ZMod N,
        ‖endpointFourierCoefficient g (endpointDominantFrequency g)‖ ^ 2 * ‖endpointFourierCoefficient g r‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _ = ‖endpointFourierCoefficient g r‖ ^ 2 * ‖endpointFourierCoefficient g r‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (endpointDominantFrequency_max g r) 2) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, endpointFourierCoefficient_parseval g hg, mul_one]

theorem endpointFourierCoefficient_one {N : Nat} [NeZero N] (r : ZMod N) :
    endpointFourierCoefficient (fun _ : ZMod N => 1) r = if r = 0 then 1 else 0 := by
  rw [endpointFourierCoefficient_eq_expect]
  simp only [mul_one]
  simpa only [neg_eq_zero] using fejer_expect_exponential_mul (-r)

theorem endpointDominantFrequency_one {N : Nat} [NeZero N] :
    endpointDominantFrequency (fun _ : ZMod N => 1) = 0 := by
  have ht := endpointDominantFrequency_max (fun _ : ZMod N => 1) 0
  simp only [endpointFourierCoefficient_one] at ht
  by_contra h
  norm_num [h] at ht

end LeanProofs.GowersSzemeredi
