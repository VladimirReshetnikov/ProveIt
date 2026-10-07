import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_weighted_term {I : Type*} [Fintype I] (c z : I → ℂ)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : (∑ i, ‖c i‖) ≤ M) (hsum : delta ≤ ‖∑ i, c i * z i‖) :
    ∃ i, delta / M ≤ ‖z i‖ := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, norm_zero] at hsum
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    delta ≤ ‖∑ j, c j * z j‖ := hsum
    _ ≤ ∑ j, ‖c j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * ‖z i‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * ‖z i‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ M * ‖z i‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖z i‖ * M := mul_comm _ _

theorem sum_pair_coefficient_norms_le {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d : ∀ i, J i → ℂ)
    {C D : ℝ} (hD : 0 ≤ D) (hc : (∑ i, ‖c i‖) ≤ C)
    (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D) :
    (∑ p : Sigma J, ‖c p.1 * d p.1 p.2‖) ≤ C * D := by
  rw [Fintype.sum_sigma]
  simp_rw [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ i, ‖c i‖ * D := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _))
    _ = (∑ i, ‖c i‖) * D := (Finset.sum_mul _ _ _).symm
    _ ≤ C * D := mul_le_mul_of_nonneg_right hc hD

theorem exists_large_weighted_pair {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d z : ∀ i, J i → ℂ)
    {delta C D : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hsum : delta ≤ ‖∑ i, ∑ j, (c i * d i j) * z i j‖) :
    ∃ i j, delta / (C * D) ≤ ‖z i j‖ := by
  obtain ⟨p, hp⟩ := exists_large_weighted_term
    (fun p : Sigma J => c p.1 * d p.1 p.2) (fun p => z p.1 p.2)
    hdelta (mul_pos hC hD) (sum_pair_coefficient_norms_le c d hD.le hc hd)
    (by simpa only [Fintype.sum_sigma] using hsum)
  exact ⟨p.1, p.2, hp⟩

theorem exists_large_weighted_pair_nonzero {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d z : ∀ i, J i → ℂ)
    {delta C D : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hsum : delta ≤ ‖∑ i, ∑ j, (c i * d i j) * z i j‖) :
    ∃ i j, c i ≠ 0 ∧ d i j ≠ 0 ∧ delta / (C * D) ≤ ‖z i j‖ := by
  classical
  let w := fun i j => if c i * d i j = 0 then 0 else z i j
  have he : ∀ i j, (c i * d i j) * w i j = (c i * d i j) * z i j := by
    intro i j
    dsimp only [w]
    split_ifs with h
    · simp only [h, zero_mul]
    · rfl
  obtain ⟨i, j, hj⟩ := exists_large_weighted_pair c d w hdelta hC hD hc hd
    (by simpa only [he] using hsum)
  have hn : c i * d i j ≠ 0 := by
    intro h
    have hpos := div_pos hdelta (mul_pos hC hD)
    simp only [w, h, ite_true, norm_zero] at hj
    exact (not_le_of_gt hpos) hj
  exact ⟨i, j, (mul_ne_zero_iff.mp hn).1, (mul_ne_zero_iff.mp hn).2,
    by simpa only [w, hn, ite_false] using hj⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlating_components_on_finset {X I J : Type*} [Fintype I] [Fintype J]
    (s : Finset X) (hs : s.Nonempty) (U Q R : X → ℂ) (V : I → X → ℂ) (W : J → X → ℂ)
    {delta C D rho eta : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hrho : 0 ≤ rho) (_heta : 0 ≤ eta)
    (hI : (Fintype.card I : ℝ) ≤ C) (hJ : (Fintype.card J : ℝ) ≤ D)
    (hU : ∀ x ∈ s, ‖U x‖ ≤ 1) (hR : ∀ x ∈ s, ‖R x‖ ≤ 1)
    (hV : ∀ i x, x ∈ s → ‖V i x‖ ≤ 1)
    (hQa : ∀ x ∈ s, ‖Q x - ∑ i, V i x‖ ≤ rho)
    (hRa : ∀ x ∈ s, ‖R x - ∑ j, W j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 x ∈ s, U x * Q x * R x‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 x ∈ s, U x * V i x * W j x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      ‖U x * Q x * R x - ∑ i, ∑ j, U x * V i x * W j x‖ ≤ rho + C * eta := by
    have hsum : ‖∑ i, V i x‖ ≤ C := by
      apply (norm_sum_le _ _).trans
      exact (Finset.sum_le_sum (fun i _ => hV i x hx)).trans (by simpa using hI)
    have hid : U x * Q x * R x - ∑ i, ∑ j, U x * V i x * W j x =
        U x * (Q x - ∑ i, V i x) * R x +
          U x * (∑ i, V i x) * (R x - ∑ j, W j x) := by
      rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
      ring
    rw [hid]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simp only [norm_mul]
      calc
        _ ≤ 1 * rho * 1 := mul_le_mul
          (mul_le_mul (hU x hx) (hQa x hx) (norm_nonneg _) (by norm_num))
          (hR x hx) (norm_nonneg _) (by positivity)
        _ = rho := by ring
    · simp only [norm_mul]
      calc
        _ ≤ 1 * C * eta := mul_le_mul
          (mul_le_mul (hU x hx) hsum (norm_nonneg _) (by norm_num))
          (hRa x hx) (norm_nonneg _) (by positivity)
        _ = C * eta := by ring
  have hsum : (𝔼 x ∈ s, ∑ i, ∑ j, U x * V i x * W j x) =
      ∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x := by
    simp_rw [Finset.expect_sum_comm]
  have herr : ‖(𝔼 x ∈ s, U x * Q x * R x) -
      (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x)‖ ≤ delta / 2 := by
    rw [← hsum, ← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans ((Finset.expect_le hs hpoint).trans hsmall)
  apply exists_large_weighted_pair (fun _ : I => (1 : ℂ)) (fun (_ : I) (_ : J) => (1 : ℂ))
    (fun i j => 𝔼 x ∈ s, U x * V i x * W j x) (by positivity) hC hD
  · simpa using hI
  · intro _
    simpa using hJ
  · simp only [one_mul]
    have htri := norm_add_le
      ((𝔼 x ∈ s, U x * Q x * R x) - (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x))
      (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x)
    rw [sub_add_cancel] at htri
    linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem two_site_model_identity {G I : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)]
    (a b ea U : G → ℂ) (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n) (h : G) :
    (𝔼 n, U n * a n * b (n + h)) =
      (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h))) +
      (𝔼 n, U n * ea n * b (n + h)) +
      (∑ i, c i * (𝔼 n, U n * Q i n * eb i (n + h))) := by
  have hpoint (n : G) : U n * a n * b (n + h) =
      (∑ i, ∑ j, (c i * d i j) * (U n * Q i n * R i j (n + h))) +
      U n * ea n * b (n + h) + (∑ i, c i * (U n * Q i n * eb i (n + h))) := by
    rw [ha n]
    calc
      _ = (∑ i, c i * (U n * Q i n * b (n + h))) + U n * ea n * b (n + h) := by
        simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, ((∑ j, (c i * d i j) * (U n * Q i n * R i j (n + h))) +
          c i * (U n * Q i n * eb i (n + h)))) + U n * ea n * b (n + h) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hb i (n + h)]
        simp only [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_add_distrib]; ring
  simp_rw [hpoint, Finset.expect_add_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]

theorem two_site_model_error_bound {G I : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)]
    (a b ea U : G → ℂ) (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    (h : G) {A : ℝ} {B : I → ℝ}
    (hfirst : ‖𝔼 n, U n * ea n * b (n + h)‖ ≤ A)
    (hsecond : ∀ i, ‖𝔼 n, U n * Q i n * eb i (n + h)‖ ≤ B i) :
    ‖(𝔼 n, U n * a n * b (n + h)) -
      (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h)))‖ ≤
        A + ∑ i, ‖c i‖ * B i := by
  rw [two_site_model_identity a b ea U Q R eb c d ha hb h]
  rw [show ∀ x y z : ℂ, x + y + z - x = y + z by intros; ring]
  apply (norm_add_le _ _).trans
  apply add_le_add hfirst
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hsecond i) (norm_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem complex_unit_vector_resolution {K : Type*} [Fintype K] (u : K → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (z : ℂ) : z = ∑ k, (z * star (u k)) * u k := by
  have hunit : (∑ k, star (u k) * u k) = (1 : ℂ) := by
    calc
      _ = ∑ k, ((‖u k‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∑ k, ‖u k‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum _ _).symm
      _ = 1 := by rw [hu, Complex.ofReal_one]
  rw [show (∑ k, (z * star (u k)) * u k) = z * ∑ k, star (u k) * u k by
    rw [Finset.mul_sum]; simp only [mul_assoc], hunit, mul_one]

theorem exists_unit_expansion_correlation {X K : Type*} {A : K → Type*}
    [Fintype K] [∀ k, Fintype (A k)] (s : Finset X)
    (f Q : X → ℂ) (P : K → X → ℂ) (c : ∀ k, A k → ℂ) (psi : ∀ k, A k → X → ℂ)
    (hunit : ∀ x ∈ s, ∑ k, ‖P k x‖ ^ 2 = 1)
    (hexp : ∀ k x, x ∈ s → Q x * star (P k x) = ∑ a, c k a * psi k a x)
    {rho D M : ℝ} (hrho : 0 < rho) (hD : 0 < D) (hM : 0 < M)
    (hcard : (Fintype.card K : ℝ) ≤ D) (hc : ∀ k, (∑ a, ‖c k a‖) ≤ M)
    (hcorr : rho ≤ ‖𝔼 x ∈ s, f x * Q x‖) :
    ∃ k a, rho / (D * M) ≤ ‖𝔼 x ∈ s, f x * P k x * psi k a x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      f x * Q x = ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) := by
    rw [complex_unit_vector_resolution (fun k => P k x) (hunit x hx) (Q x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hexp k x hx, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hmean : (𝔼 x ∈ s, f x * Q x) =
      ∑ k, ∑ a, c k a * (𝔼 x ∈ s, f x * P k x * psi k a x) := by
    calc
      _ = 𝔼 x ∈ s, ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) :=
        Finset.expect_congr rfl hpoint
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  apply exists_large_weighted_pair (fun _ : K => (1 : ℂ)) c
    (fun k a => 𝔼 x ∈ s, f x * P k x * psi k a x) hrho hD hM
  · simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard
  · exact hc
  · simpa only [one_mul, ← hmean] using hcorr

end Erdos3

end

end OAI
