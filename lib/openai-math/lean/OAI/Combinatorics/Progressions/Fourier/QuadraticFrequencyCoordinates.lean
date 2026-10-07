/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.SmallDifferenceGraphCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem finiteFourierCoeff_convolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (finiteConvolution f g) χ = finiteFourierCoeff f χ * finiteFourierCoeff g χ := by
  calc
    _ = 𝔼 x, f x * finiteFourierCoeff (fun y => g (y - x)) χ := by
      simp only [finiteFourierCoeff, finiteConvolution, Finset.expect_mul, Finset.mul_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      ring
    _ = 𝔼 x, f x * (star (χ x) * finiteFourierCoeff g χ) := by
      simp_rw [finiteFourierCoeff_translate]
    _ = _ := by
      change (𝔼 x, f x * (star (χ x) * finiteFourierCoeff g χ)) =
        (𝔼 x, f x * star (χ x)) * finiteFourierCoeff g χ
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro x _
      ring

theorem finiteFourierCoeff_reflected_conjugate (f : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (fun x => star (f (-x))) χ = star (finiteFourierCoeff f χ) := by
  rw [finiteFourierCoeff, star_finiteFourierCoeff]
  apply Fintype.expect_equiv (Equiv.neg G)
  intro x
  simp only [Equiv.neg_apply, AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  rfl

theorem gowersNorm_two_fourier (f : G → ℂ) :
    gowersNorm 2 f ^ 4 = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 4 := by
  let C := finiteConvolution f (fun x => star (f (-x)))
  calc
    _ = 𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x‖ ^ 2 := by
      simpa only [gowersNorm_one, Nat.zero_add, show 2 ^ 2 = 4 by norm_num,
        show 2 ^ 1 = 2 by norm_num] using gowersNorm_derivative 0 f
    _ = 𝔼 h, ‖C h‖ ^ 2 := by
      apply Fintype.expect_equiv (Equiv.neg G)
      intro h
      simp only [C, finiteConvolution, Equiv.neg_apply, neg_sub,
        sub_neg_eq_add, multiplicativeDerivative]
    _ = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff C χ‖ ^ 2 := (finiteFourier_parseval C).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [C, finiteFourierCoeff_convolution, finiteFourierCoeff_reflected_conjugate,
        norm_mul, norm_star]
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem cross_correlation_fourier_energy (f g : G → ℂ) :
    (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖ ^ 2) =
      ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 2 * ‖finiteFourierCoeff g χ‖ ^ 2 := by
  let C := finiteConvolution f (fun x => star (g (-x)))
  calc
    _ = 𝔼 h, ‖C h‖ ^ 2 := by
      apply Fintype.expect_equiv (Equiv.neg G)
      intro h
      simp only [C, finiteConvolution, Equiv.neg_apply, neg_sub, sub_neg_eq_add]
    _ = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff C χ‖ ^ 2 := (finiteFourier_parseval C).symm
    _ = _ := by
      simp only [C, finiteFourierCoeff_convolution, finiteFourierCoeff_reflected_conjugate,
        norm_mul, norm_star, mul_pow]

theorem exists_large_fourier_of_mean_cross_correlation (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖) ≤ ‖finiteFourierCoeff g χ‖ := by
  classical
  obtain ⟨χ, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun χ : AddChar G ℂ => ‖finiteFourierCoeff g χ‖) Finset.univ_nonempty
  have hmass : (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) ≤ 1 := by
    rw [finiteFourier_parseval]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
  have henergy : (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖ ^ 2) ≤ ‖finiteFourierCoeff g χ‖ ^ 2 := by
    rw [cross_correlation_fourier_energy]
    calc
      _ ≤ ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2 * ‖finiteFourierCoeff g χ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ψ _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hmax ψ (Finset.mem_univ ψ)) 2) (sq_nonneg _)
      _ = (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) * ‖finiteFourierCoeff g χ‖ ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ‖finiteFourierCoeff g χ‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hmass
  refine ⟨χ, (sq_le_sq₀ (Finset.expect_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)).mp ?_⟩
  exact (expect_square_le (fun h => ‖𝔼 x, f x * star (g (x + h))‖)).trans henergy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_fourier_of_gowers_two {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, gowersNorm 2 f ^ 2 ≤ ‖finiteFourierCoeff f χ‖ := by
  classical
  obtain ⟨χ, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun χ : AddChar G ℂ => ‖finiteFourierCoeff f χ‖) Finset.univ_nonempty
  have hmass : (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) ≤ 1 := by
    rw [finiteFourier_parseval]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (f x)) (hf x) 2
  have hfourth : gowersNorm 2 f ^ 4 ≤ ‖finiteFourierCoeff f χ‖ ^ 2 := by
    rw [gowersNorm_two_fourier]
    calc
      _ ≤ ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 2 * ‖finiteFourierCoeff f ψ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ψ _
        have h := pow_le_pow_left₀ (norm_nonneg (finiteFourierCoeff f ψ))
          (hmax ψ (Finset.mem_univ ψ)) 2
        nlinarith [sq_nonneg (‖finiteFourierCoeff f ψ‖)]
      _ = ‖finiteFourierCoeff f χ‖ ^ 2 * ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ ‖finiteFourierCoeff f χ‖ ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (sq_nonneg ‖finiteFourierCoeff f χ‖)
  refine ⟨χ, (sq_le_sq₀ (sq_nonneg (gowersNorm 2 f)) (norm_nonneg (finiteFourierCoeff f χ))).mp ?_⟩
  simpa only [← pow_mul, show 2 * 2 = 4 by norm_num] using hfourth

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_derivative_fourier_fourth_le_gowers_three {G : Type*}
    [AddCommGroup G] [Fintype G] (f : G → ℂ) (χ : G → AddChar G ℂ) :
    (𝔼 k, ‖finiteFourierCoeff (multiplicativeDerivative f k) (χ k)‖) ^ 4 ≤
      gowersNorm 3 f ^ 8 := by
  classical
  let z (k : G) := ‖finiteFourierCoeff (multiplicativeDerivative f k) (χ k)‖
  have hp (x : ℝ) : (x ^ 2) ^ 2 = x ^ 4 := by ring
  have hJ : (𝔼 k, z k) ^ 4 ≤ 𝔼 k, z k ^ 4 := by
    rw [← hp]
    apply (pow_le_pow_left₀ (sq_nonneg _) (expect_square_le z) 2).trans
    calc
      _ ≤ 𝔼 k, (z k ^ 2) ^ 2 := expect_square_le (fun k => z k ^ 2)
      _ = 𝔼 k, z k ^ 4 := by
        apply Finset.expect_congr rfl
        intro k _
        ring
  have hpoint (k : G) : z k ^ 4 ≤ gowersNorm 2 (multiplicativeDerivative f k) ^ 4 := by
    rw [gowersNorm_two_fourier]
    exact Finset.single_le_sum (fun ψ _ => pow_nonneg (norm_nonneg _) 4) (Finset.mem_univ (χ k))
  apply hJ.trans
  calc
    _ ≤ 𝔼 k, gowersNorm 2 (multiplicativeDerivative f k) ^ 4 :=
      Finset.expect_le_expect (fun k _ => hpoint k)
    _ = gowersNorm 3 f ^ 8 := by simpa using (gowersNorm_derivative 1 f).symm

theorem exp_le_gowers_three_of_mean_derivative_fourier {G : Type*}
    [AddCommGroup G] [Fintype G] (f : G → ℂ) (χ : G → AddChar G ℂ) {p : ℝ}
    (hp : 0 ≤ p)
    (hcorr : Real.exp (-p) ≤ 𝔼 k, ‖finiteFourierCoeff (multiplicativeDerivative f k) (χ k)‖) :
    Real.exp (-p) ≤ gowersNorm 3 f := by
  have hexp : Real.exp (-p) ^ 8 ≤ Real.exp (-p) ^ 4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hpower := hexp.trans ((pow_le_pow_left₀ (Real.exp_nonneg _) hcorr 4).trans
    (mean_derivative_fourier_fourth_le_gowers_three f χ))
  exact (pow_le_pow_iff_left₀ (Real.exp_nonneg _) (gowersNorm_nonneg 2 f) (by norm_num : (8 : ℕ) ≠ 0)).mp hpower

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem character_relation_of_quadruple_pos (χ : G → AddChar G ℂ) (a h k : G)
    (hpos : 0 < additiveQuadrupleCorrelation (fun h x => χ h x) a h k) :
    χ (h - a) + χ k = χ h + χ (k - a) := by
  let ψ := χ (h - a) + χ k - χ h - χ (k - a)
  let c := χ (h - a) a * star (χ (k - a) a)
  have hfactor (x : G) :
      star (χ h x) * χ (h - a) (x + a) * χ k x * star (χ (k - a) (x + a)) =
        c * ψ x := by
    simp only [ψ, c, AddChar.sub_apply, AddChar.add_apply, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_conj, Complex.star_def, map_mul]
    ring
  have hmean : (𝔼 x, star (χ h x) * χ (h - a) (x + a) * χ k x *
      star (χ (k - a) (x + a))) = c * (𝔼 x, ψ x) := by
    simp_rw [hfactor]
    exact (Finset.mul_expect _ _ _).symm
  have hψ : ψ = 0 := by
    by_contra hn
    have hz : (𝔼 x, ψ x) = 0 := AddChar.expect_eq_zero_iff_ne_zero.mpr hn
    change 0 < ‖𝔼 x, star (χ h x) * χ (h - a) (x + a) * χ k x *
      star (χ (k - a) (x + a))‖ at hpos
    rw [hmean, hz, mul_zero, norm_zero] at hpos
    exact (lt_irrefl 0) hpos
  apply sub_eq_zero.mp
  calc
    (χ (h - a) + χ k) - (χ h + χ (k - a)) = ψ := by dsimp [ψ]; abel
    _ = 0 := hψ

theorem exists_many_derivative_character_relations
    (f : G → ℂ) (H : Finset G) (χ : G → AddChar G ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (α * δ) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        χ (t.2.1 - t.1) + χ t.2.2 = χ t.2.1 + χ (t.2.2 - t.1) := by
  classical
  let g (h x : G) : ℂ := if h ∈ H then χ h x else 0
  have hg (h x : G) : ‖g h x‖ ≤ 1 := by
    dsimp [g]
    split_ifs
    · exact (AddChar.norm_apply _ _).le
    · simp
  have hzero (h : G) (hh : h ∉ H) (x : G) : g h x = 0 := by simp [g, hh]
  have hcorr' (h : G) (hh : h ∈ H) :
      δ ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    simpa only [g, ite_eq_left hh, finiteFourierCoeff] using hcorr h hh
  obtain ⟨Q, hQ, hcard, hrelations⟩ :=
    exists_many_correlated_additive_quadruples f g H hf hg hzero hα hδ hdense hcorr'
  refine ⟨Q, hQ, hcard, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hlarge⟩ := hrelations t ht
  refine ⟨h₁, h₂, h₃, h₄, character_relation_of_quadruple_pos χ t.1 t.2.1 t.2.2 ?_⟩
  have heq : additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 =
      additiveQuadrupleCorrelation (fun h x => χ h x) t.1 t.2.1 t.2.2 := by
    simp only [additiveQuadrupleCorrelation, g, ite_eq_left h₁, ite_eq_left h₂, ite_eq_left h₃, ite_eq_left h₄]
  rw [heq] at hlarge
  exact lt_of_lt_of_le (by positivity) hlarge

theorem derivative_character_graph_energy [DecidableEq G]
    (f : G → ℂ) (H : Finset G) (χ : G → AddChar G ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) :
    (α * δ) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
  classical
  obtain ⟨Q, _, hcard, hrelations⟩ :=
    exists_many_derivative_character_relations f H χ hf hα hδ hdense hcorr
  have henergy := graph_energy_of_few_quadruple_differences H Q χ {0}
    (fun t ht => let h := hrelations t ht; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (by
      intro t ht
      simp only [Finset.mem_singleton]
      rw [(hrelations t ht).2.2.2.2]
      abel)
  have henergy' : Q.card ≤ Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) := by
    simpa only [Finset.card_singleton, one_mul] using henergy
  exact hcard.trans (by exact_mod_cast henergy')

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_quadratic_frequency_graph {p : ℝ} (hp : 0 ≤ p)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-(128 * (p + 1))) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∃ χ : G → AddChar G ℂ,
        (∀ h ∈ H, Real.exp (-(128 * (p + 1))) ≤
          ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) ∧
        Real.exp (-(128 * (p + 1))) * (Fintype.card G : ℝ) ^ 3 ≤
          (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
  classical
  obtain ⟨H, hH, hdense, hderivative⟩ := exists_many_large_gowers_derivatives 1 f hf hp hG
  choose χ hχ using fun h =>
    exists_large_fourier_of_gowers_two (multiplicativeDerivative f h)
      (multiplicativeDerivative_norm_le_one f hf h)
  let d := derivativeInverseBudget 1 p
  have hd : d = 8 * p + 2 := by norm_num [d, derivativeInverseBudget]
  have hcorr (h : G) (hh : h ∈ H) : Real.exp (-(2 * d)) ≤
      ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖ := by
    calc
      _ = Real.exp (-d) ^ 2 := by rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ gowersNorm 2 (multiplicativeDerivative f h) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) (hderivative h hh) 2
      _ ≤ _ := hχ h
  have hdP : d ≤ 128 * (p + 1) := by rw [hd]; linarith
  have h2dP : 2 * d ≤ 128 * (p + 1) := by rw [hd]; linarith
  have henergy := derivative_character_graph_energy f H χ hf
    (Real.exp_pos (-d)) (Real.exp_pos (-(2 * d))) hdense hcorr
  have hthreshold : Real.exp (-(128 * (p + 1))) ≤
      (Real.exp (-d) * Real.exp (-(2 * d))) ^ 4 / 2 := by
    rw [derivative_quadruple_exp_threshold]
    calc
      _ ≤ Real.exp (-(12 * d) - 1) := Real.exp_le_exp.mpr (by rw [hd]; linarith)
      _ ≤ _ := exp_sub_one_le_half_exp _
  refine ⟨H, hH, ?_, χ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdP))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg h2dP)).trans (hcorr h hh)
  · exact (mul_le_mul_of_nonneg_right hthreshold (by positivity)).trans henergy

theorem exists_quadratic_frequency_small_difference {p : ℝ} (hp : 0 ≤ p)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-(1024 * (p + 1))) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∃ χ : G → AddChar G ℂ,
        (∀ h ∈ H, Real.exp (-(1024 * (p + 1))) ≤
          ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) ∧
        ((additiveGraph H χ - additiveGraph H χ).card : ℝ) ≤
          Real.exp (1024 * (p + 1)) * H.card := by
  classical
  obtain ⟨H, hH, hdense, χ, hcorr, henergy⟩ := exists_quadratic_frequency_graph hp f hf hG
  let q := 128 * (p + 1)
  let P := 1024 * (p + 1)
  have hqP : q ≤ P := by dsimp [q, P]; linarith
  have henergy' : (Real.exp q)⁻¹ * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
    rw [← Real.exp_neg]
    apply le_trans _ henergy
    gcongr
    exact_mod_cast Finset.card_le_univ H
  obtain ⟨J, hJH, hJ, hsize, hdiff⟩ :=
    exists_large_graph_subset_small_difference H hH χ (Real.exp_pos q) henergy'
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (2 : ℝ) ^ 4 ≤ Real.exp 4 := by
    calc
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hfourteen : (2 : ℝ) ^ 14 ≤ Real.exp 14 := by
    calc
      _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) htwo 14
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hnegfour : Real.exp (-4) ≤ ((2 : ℝ) ^ 4)⁻¹ := by
    simpa only [Real.exp_neg, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 4) hfour
  have hsize' : Real.exp (-P) * Fintype.card G ≤ (J.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(2 * q + 4)) * Fintype.card G :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by dsimp [q, P]; linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-4) * (Real.exp (-q) * (Real.exp (-q) * Fintype.card G)) := by
        rw [show -(2 * q + 4) = -4 + -q + -q by ring, Real.exp_add, Real.exp_add]
        ring
      _ ≤ ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (-q) * (Real.exp (-q) * Fintype.card G)) :=
        mul_le_mul_of_nonneg_right hnegfour (by positivity)
      _ ≤ ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (-q) * H.card) := by
        gcongr
      _ = ((2 : ℝ) ^ 4)⁻¹ * (Real.exp q)⁻¹ * H.card := by
        rw [Real.exp_neg]
        ring
      _ ≤ _ := hsize
  refine ⟨J, hJ, hsize', χ, ?_, ?_⟩
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqP)).trans (hcorr h (hJH hh))
  · apply hdiff.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      (2 : ℝ) ^ 14 * Real.exp q ^ 6 ≤ Real.exp 14 * Real.exp q ^ 6 := by gcongr
      _ = Real.exp (6 * q + 14) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp P := Real.exp_le_exp.mpr (by dsimp [q, P]; linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cyclic_interval_fourier_smoothing {N : ℕ} [NeZero N]
    (a : ZMod N) (L : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (v : ZMod N → ℂ) (c : AddChar (ZMod N) ℂ → ℂ),
      (∀ x, ‖v x‖ ≤ 1) ∧
      (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - v x‖) ≤ 2 * δ ∧
      (∑ χ, ‖c χ‖) ≤ 2 / δ ∧ ∀ x, v x = ∑ χ, c χ * χ x := by
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let I := cyclicInterval a L
  let B := cyclicInterval (0 : ZMod N) K
  have hB : B.Nonempty := cyclicInterval_nonempty 0 hK
  have hcard : B.card = K := cyclicInterval_card 0 hKN
  refine ⟨smoothedIndicator I B,
    (fun χ => finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ),
    smoothedIndicator_norm_le_one I hB, ?_, ?_, ?_⟩
  · apply mean_indicator_smoothing_error I hB
    intro h hh
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have hmean := cyclicInterval_nat_shift_error a L m
    have hhcast : (m : ZMod N) = h := by simpa using he
    rw [hhcast] at hmean
    apply hmean.trans
    apply (div_le_iff₀ (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N)).mpr
    nlinarith
  · have hmass := smoothedIndicator_fourier_mass hB I
    rw [ZMod.card, hcard] at hmass
    exact hmass.trans hratio
  · intro x
    rw [smoothedIndicator_eq_convolution]
    simpa only [finiteFourierCoeff_convolution] using
      (finiteFourier_inversion (finiteConvolution (averagingKernel B) (finiteIndicator I)) x).symm

end Erdos3

end

section

namespace Erdos3

open scoped Pointwise

theorem additiveGraph_difference_card_hom
    {G K L : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup L]
    [DecidableEq G] [DecidableEq K] [DecidableEq L]
    (H : Finset G) (b : G → K) (e : K →+ L) (he : Function.Injective e) :
    (additiveGraph H (fun h => e (b h)) - additiveGraph H (fun h => e (b h))).card =
      (additiveGraph H b - additiveGraph H b).card := by
  let F : G × K →+ G × L := {
    toFun := fun x => (x.1, e x.2)
    map_zero' := by simp
    map_add' := by intro x y; simp }
  have hF : Function.Injective F := by
    intro x y h
    exact Prod.ext (congrArg (fun z : G × L => z.1) h)
      (he (congrArg (fun z : G × L => z.2) h))
  have hgraph : additiveGraph H (fun h => e (b h)) = (additiveGraph H b).image F := by
    unfold additiveGraph
    rw [Finset.image_image]
    rfl
  rw [hgraph]
  apply FreimanModel.card_difference_image_of_freiman
  exact FreimanModel.isAddFreimanIso_of_injOn_iterated_sums F (additiveGraph H b) 2
    hF.injOn hF.injOn

theorem exists_quadratic_affine_frequency_coordinates
    {N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    let P := 1024 * (p + 1)
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-(P + properAffineRecoveryLogLoss P 1)) * N ≤ (H.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (η ξ : (Fin r → ℤ) →+ ZMod N) (h₀ ξ₀ : ZMod N),
        (r : ℝ) ≤ properAffineRankBound P 1 ∧
        Set.InjOn η (centeredIntegerBox R : Set _) ∧
        ∀ h ∈ H, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x ∧
          Real.exp (-P) ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h)
            (AddChar.zmodAddEquiv (ξ₀ + ξ x))‖ := by
  intro P
  classical
  obtain ⟨H, hH, hdense, χ, hcorr, hsmall⟩ := exists_quadratic_frequency_small_difference hp f hf hG
  let e₀ : AddChar (ZMod N) ℂ ≃+ ZMod N := (AddChar.zmodAddEquiv (n := N)).symm
  let e : AddChar (ZMod N) ℂ →+ (Unit → ZMod N) := {
    toFun := fun c _ => e₀ c
    map_zero' := by ext; simp
    map_add' := by intro c d; ext; simp }
  have he : Function.Injective e := by
    intro c d h
    exact e₀.injective (congrFun h ())
  let b (h : ZMod N) := e (χ h)
  have hsmall' : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp P * H.card := by
    rw [additiveGraph_difference_card_hom H χ e he]
    exact hsmall
  obtain ⟨J, hJH, hJ, hJdense, r, R, Φ, base, hrank, hproper, hrepr⟩ :=
    exists_small_difference_graph_affine_coordinates N (fun _ : Unit => N) H hH b
      (by dsimp [P]; positivity) hsmall'
  let reduce := FreimanModel.variableIntegerGraphReduction N (fun _ : Unit => N)
  let η := (AddMonoidHom.fst (ZMod N) (Unit → ZMod N)).comp (reduce.comp Φ)
  let ξ : (Fin r → ℤ) →+ ZMod N := {
    toFun := fun x => (reduce (Φ x)).2 ()
    map_zero' := by simp
    map_add' := by intro x y; simp }
  have hdense' : Real.exp (-P) * N ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using hdense
  have hJdense' : Real.exp (-properAffineRecoveryLogLoss P 1) * H.card ≤ (J.card : ℝ) := by
    simpa only [Fintype.card_unique] using hJdense
  refine ⟨J, hJ, ?_, r, R, η, ξ, (reduce base).1, (reduce base).2 (), ?_, hproper, ?_⟩
  · calc
      _ = Real.exp (-properAffineRecoveryLogLoss P 1) * (Real.exp (-P) * N) := by
        rw [neg_add, Real.exp_add]
        ring
      _ ≤ Real.exp (-properAffineRecoveryLogLoss P 1) * H.card :=
        mul_le_mul_of_nonneg_left hdense' (Real.exp_nonneg _)
      _ ≤ _ := hJdense'
  · simpa only [Fintype.card_unique] using hrank
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    have hred : (h, b h) = reduce base + reduce (Φ x) := by
      have h := congrArg reduce heq
      simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using h
    have hfreq : AddChar.zmodAddEquiv ((reduce base).2 () + ξ x) = χ h := by
      have hv : e₀ (χ h) = (reduce base).2 () + ξ x := congrArg (fun v => v.2 ()) hred
      rw [← hv]
      exact (AddChar.zmodAddEquiv (n := N)).apply_symm_apply _
    refine ⟨x, hx, congrArg Prod.fst hred, ?_⟩
    rw [hfreq]
    exact hcorr h (hJH hh)

theorem exists_quadratic_affine_frequency_coordinates_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ) (η ξ : (Fin r → ℤ) →+ ZMod N) (h₀ ξ₀ : ZMod N),
          (r : ℝ) ≤ (p + C) ^ C ∧ Set.InjOn η (centeredIntegerBox R : Set _) ∧
          ∀ h ∈ H, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x ∧
            Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h)
              (AddChar.zmodAddEquiv (ξ₀ + ξ x))‖ := by
  obtain ⟨C, hC, hbudget⟩ := exists_quadratic_affine_budget
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  obtain ⟨H, hH, hdense, r, R, η, ξ, h₀, ξ₀, hrank, hproper, hcorr⟩ :=
    exists_quadratic_affine_frequency_coordinates hp f hf hG
  obtain ⟨hcost, hrankCost, hcorrCost⟩ := hbudget p hp
  refine ⟨H, hH, ?_, r, R, η, ξ, h₀, ξ₀, hrank.trans hrankCost, hproper, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨x, hx, hshift, hlarge⟩ := hcorr h hh
    exact ⟨x, hx, hshift, (Real.exp_le_exp.mpr (neg_le_neg hcorrCost)).trans hlarge⟩

end Erdos3

end

end OAI
