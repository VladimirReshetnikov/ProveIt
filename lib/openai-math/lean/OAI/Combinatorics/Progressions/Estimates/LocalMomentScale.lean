import OAI.Combinatorics.Progressions.Estimates.LocalCorrelationBounds
import OAI.Combinatorics.Progressions.Estimates.LocalCorrelationEnergy
import OAI.Combinatorics.Progressions.Estimates.PeelingDecomposition
import OAI.Combinatorics.Progressions.Fourier.RelativeSpectrumDimension

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem abs_sum_mul_sub_le {ι : Type*} [Fintype ι] (u v f : ι → ℝ) {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) :
    |(∑ x, u x * f x) - ∑ x, v x * f x| ≤ M * ∑ x, |u x - v x| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |u x * f x - v x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |u x - v x| * |f x| := by simp only [← sub_mul, abs_mul]
    _ ≤ ∑ x, |u x - v x| * M :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _))
    _ = M * ∑ x, |u x - v x| := by rw [← Finset.sum_mul]; ring

namespace LocalConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem correlation_swap (L : Finset G) (f g : G → ℝ) (t : G) :
    correlation L f g t = correlation L g f (-t) := by
  unfold correlation
  congr 1
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro x
  simp [mul_comm]

theorem correlation_sub_self (L : Finset G) (f g : G → ℝ) (t : G) :
    correlation L (fun x => f x - g x) (fun x => f x - g x) t =
      correlation L f f t - correlation L f g t - correlation L g f t + correlation L g g t := by
  unfold correlation
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

variable [DecidableEq G]

omit [AddCommGroup G] [Fintype G] in
theorem indicator_div_card (L : Finset G) (x : G) :
    realFinsetIndicator L x / (L.card : ℝ) = realUniformMass L x := by
  by_cases hx : x ∈ L <;> simp [realFinsetIndicator, realUniformMass, hx, one_div]

omit [AddCommGroup G] in
theorem sum_uniformMass_mul_eq_one {L : Finset G} (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card) :
    ∑ x, realUniformMass L x * f x = 1 := by
  have hcard : (L.card : ℝ) ≠ 0 := by exact_mod_cast hL.card_pos.ne'
  have hpoint (x : G) : realUniformMass L x * f x = f x / L.card := by
    by_cases hx : x ∈ L
    · simp [realUniformMass, hx, div_eq_mul_inv, mul_comm]
    · simp [realUniformMass, hx, hsupport x hx]
  simp_rw [hpoint]
  rw [← Finset.sum_div, hsum, div_self hcard]

theorem correlation_indicator_left_eq (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L (realFinsetIndicator L) f t = ∑ x, realUniformMass L (x + t) * f x := by
  rw [correlation, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [← div_mul_eq_mul_div, indicator_div_card]

theorem correlation_indicator_right_eq (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L f (realFinsetIndicator L) t = ∑ x, realUniformMass L (x - t) * f x := by
  rw [correlation_swap, correlation_indicator_left_eq]
  simp only [sub_eq_add_neg]

theorem convolution_indicator_eq (L : Finset G)
    (hsymm : ∀ x, -x ∈ L ↔ x ∈ L) (f : G → ℝ) (t : G) :
    convolution L (realFinsetIndicator L) f t = ∑ x, realUniformMass L (x - t) * f x := by
  rw [convolution, Finset.sum_div]
  apply Fintype.sum_equiv (Equiv.subLeft t)
  intro x
  have hindex : (t - x) - t = -x := by abel
  have hneg : realUniformMass L (-x) = realUniformMass L x := by
    simp [realUniformMass, hsymm x]
  simp only [Equiv.subLeft_apply, hindex, hneg]
  rw [← div_mul_eq_mul_div, indicator_div_card]

theorem correlation_indicator_right_sub_one_le {L : Finset G} (hL : L.Nonempty)
    (f : G → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) (t : G) :
    |correlation L f (realFinsetIndicator L) t - 1| ≤
      M * ∑ x, |realUniformMass L (x - t) - realUniformMass L x| := by
  rw [correlation_indicator_right_eq, ← sum_uniformMass_mul_eq_one hL f hsupport hsum]
  exact abs_sum_mul_sub_le _ _ _ hf

theorem convolution_indicator_sub_one_le {L : Finset G} (hL : L.Nonempty)
    (hsymm : ∀ x, -x ∈ L ↔ x ∈ L) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) (t : G) :
    |convolution L (realFinsetIndicator L) f t - 1| ≤
      M * ∑ x, |realUniformMass L (x - t) - realUniformMass L x| := by
  rw [convolution_indicator_eq L hsymm, ← sum_uniformMass_mul_eq_one hL f hsupport hsum]
  exact abs_sum_mul_sub_le _ _ _ hf

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem convolution_sub_left (L : Finset G) (f h g : G → ℝ) (t : G) :
    convolution L (fun x => f x - h x) g t = convolution L f g t - convolution L h g t := by
  unfold convolution
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, sub_div]

variable [DecidableEq G]

noncomputable def balancedFunction (L : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  f x - realFinsetIndicator L x

omit [AddCommGroup G] in
theorem normalized_cap_ge_one {L : Finset G} (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) : 1 ≤ M := by
  calc
    1 = ∑ x, realUniformMass L x * f x := (sum_uniformMass_mul_eq_one hL f hsupport hsum).symm
    _ ≤ ∑ x, realUniformMass L x * M := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hf x)) (realUniformMass_nonneg L x)
    _ = M := by rw [← Finset.sum_mul, sum_realUniformMass hL, one_mul]

omit [DecidableEq G] in
theorem centered_convolution_error (L : Finset G) (f g : G → ℝ) (t : G) :
    (convolution L f g t - 1) - convolution L (balancedFunction L f) g t =
      convolution L (realFinsetIndicator L) g t - 1 := by
  unfold balancedFunction
  rw [convolution_sub_left]
  ring

omit [DecidableEq G] in
theorem centered_correlation_error_identity (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L f f t - (1 + correlation L (balancedFunction L f) (balancedFunction L f) t) =
      (correlation L f (realFinsetIndicator L) t - 1) +
      (correlation L (realFinsetIndicator L) f t - 1) -
      (correlation L (realFinsetIndicator L) (realFinsetIndicator L) t - 1) := by
  unfold balancedFunction
  rw [correlation_sub_self]
  ring

theorem centered_correlation_error_le {L : Finset G} (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M eta : ℝ} (hf : ∀ x, |f x| ≤ M) (heta : 0 ≤ eta) (t : G)
    (hTV : (∑ x, |realUniformMass L (x - t) - realUniformMass L x|) ≤ eta)
    (hTVneg : (∑ x, |realUniformMass L (x - (-t)) - realUniformMass L x|) ≤ eta) :
    |correlation L f f t - (1 + correlation L (balancedFunction L f) (balancedFunction L f) t)| ≤
      3 * M * eta := by
  have hM1 := normalized_cap_ge_one hL f hsupport hsum hf
  have hM : 0 ≤ M := by linarith
  have hright : |correlation L f (realFinsetIndicator L) t - 1| ≤ M * eta :=
    (correlation_indicator_right_sub_one_le hL f hsupport hsum hf t).trans
      (mul_le_mul_of_nonneg_left hTV hM)
  have hleft : |correlation L (realFinsetIndicator L) f t - 1| ≤ M * eta := by
    rw [correlation_swap]
    exact (correlation_indicator_right_sub_one_le hL f hsupport hsum hf (-t)).trans
      (mul_le_mul_of_nonneg_left hTVneg hM)
  have hIsupport : ∀ x, x ∉ L → realFinsetIndicator L x = 0 := by
    intro x hx
    simp [realFinsetIndicator, hx]
  have hIsum : ∑ x, realFinsetIndicator L x = L.card := by simp [realFinsetIndicator]
  have hIbound : ∀ x, |realFinsetIndicator L x| ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ L <;> simp [realFinsetIndicator, hx]
  have hind : |correlation L (realFinsetIndicator L) (realFinsetIndicator L) t - 1| ≤ eta := by
    have h := correlation_indicator_right_sub_one_le hL (realFinsetIndicator L) hIsupport hIsum hIbound t
    exact (h.trans (mul_le_mul_of_nonneg_left hTV (by norm_num))).trans_eq (one_mul eta)
  rw [centered_correlation_error_identity]
  calc
    _ ≤ |correlation L f (realFinsetIndicator L) t - 1| +
        |correlation L (realFinsetIndicator L) f t - 1| +
        |correlation L (realFinsetIndicator L) (realFinsetIndicator L) t - 1| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * eta + M * eta + eta := add_le_add (add_le_add hright hleft) hind
    _ ≤ 3 * M * eta := by nlinarith [mul_le_mul_of_nonneg_right hM1 heta]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem sum_uniformMass_mul_eq_expect (S : Finset G) (f : G → ℝ) :
    (∑ x, realUniformMass S x * f x) = 𝔼 x ∈ S, f x := by
  rw [Finset.expect_eq_sum_div_card]
  simp only [realUniformMass, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

variable [AddCommGroup G]

theorem expect_add_eq_shift_mass (S : Finset G) (f : G → ℝ) (t : G) :
    (𝔼 x ∈ S, f (x + t)) = ∑ x, realUniformMass S (x - t) * f x := by
  rw [← sum_uniformMass_mul_eq_expect]
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro x
  simp

theorem abs_expect_add_sub_le (S : Finset G) (f : G → ℝ) (t : G)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) :
    |(𝔼 x ∈ S, f (x + t)) - 𝔼 x ∈ S, f x| ≤
      M * ∑ x, |realUniformMass S (x - t) - realUniformMass S x| := by
  rw [expect_add_eq_shift_mass, ← sum_uniformMass_mul_eq_expect]
  exact abs_sum_mul_sub_le _ _ f hf

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def localMomentExponentFactor (delta : ℝ) : ℕ :=
  momentAmplificationFactor (delta ^ 2 / 8)

noncomputable def localMomentGain (delta : ℝ) : ℝ :=
  momentAmplificationGain (delta ^ 2 / 8) / 2

theorem localMomentExponentFactor_pos (delta : ℝ) : 0 < localMomentExponentFactor delta :=
  momentAmplificationFactor_pos _

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem local_alternatives_of_boundary
    (L S : Finset G) (hS : S.Nonempty) (f g : G → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {m : ℕ} (hm : 0 < m)
    (hconverror : ∀ s ∈ S, ∀ t ∈ S,
      |convolution L (realFinsetIndicator L) g (s + t) - 1| ≤ delta / 2)
    (hcorrerror : ∀ s ∈ S, ∀ t ∈ S,
      |correlation L f f (s - t) -
        (1 + correlation L (balancedFunction L f) (balancedFunction L f) (s - t))| ≤
          localMomentGain delta) :
    sumLp S (fun x => convolution L f g x - 1) (2 * m) ≤ delta ∨
      ∃ h : G → ℝ, (h = f ∨ h = g) ∧ ∃ m' : ℕ,
        0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
        1 + localMomentGain delta ≤ differenceLp S (correlation L h h) (2 * m') := by
  classical
  by_cases hflat : sumLp S (fun x => convolution L f g x - 1) (2 * m) ≤ delta
  · exact Or.inl hflat
  right
  have hflatgt := lt_of_not_ge hflat
  have hp : 0 < 2 * m := by omega
  have heven : Even (2 * m) := ⟨m, by omega⟩
  have hfactor := localMomentExponentFactor_pos delta
  have hgain := localMomentGain_pos delta
  have hgainhalf := localMomentGain_le_half delta
  let f₁ := balancedFunction L f
  have hcompare : sumLp S (fun x => convolution L f g x - 1) (2 * m) ≤
      sumLp S (convolution L f₁ g) (2 * m) + delta / 2 := by
    apply sumLp_le_of_uniform_error hS _ _ hp (by positivity)
    intro s hs t ht
    rw [centered_convolution_error]
    exact hconverror s hs t ht
  have hlargeConv : delta / 2 ≤ sumLp S (convolution L f₁ g) (2 * m) := by linarith
  by_cases hg : 2 ≤ differenceLp S (correlation L g g) (2 * m)
  · refine ⟨g, Or.inr rfl, m, hm, le_rfl, ?_, ?_⟩
    · nlinarith
    · exact (show 1 + localMomentGain delta ≤ 2 by linarith).trans hg
  have hCS := convolution_sumLp_sq_le L S f₁ g hm
  have hconvSq := pow_le_pow_left₀ (show 0 ≤ delta / 2 by positivity) hlargeConv 2
  have hprod := mul_le_mul_of_nonneg_left (le_of_not_ge hg)
    (differenceLp_nonneg S (correlation L f₁ f₁) (2 * m))
  have hlarge : delta ^ 2 / 8 ≤ differenceLp S (correlation L f₁ f₁) (2 * m) := by nlinarith
  have hbeta : 0 < delta ^ 2 / 8 := by positivity
  have hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ S ×ˢ S, correlation L f₁ f₁ (x.1 - x.2) ^ k := by
    intro k
    simpa only [Finset.expect_product, differenceMoment] using differenceMoment_self_nonneg L S f₁ k
  have hunbalance := finiteSetLp_unbalance (S ×ˢ S)
    (fun x => correlation L f₁ f₁ (x.1 - x.2)) hbeta hp heven hmom hlarge
  have hindex : momentAmplificationFactor (delta ^ 2 / 8) * (2 * m) =
      2 * (localMomentExponentFactor delta * m) := by
    unfold localMomentExponentFactor
    ring
  rw [hindex] at hunbalance
  change 1 + momentAmplificationGain (delta ^ 2 / 8) ≤
    differenceLp S (fun x => 1 + correlation L f₁ f₁ x) (2 * (localMomentExponentFactor delta * m)) at hunbalance
  have hm' : 0 < localMomentExponentFactor delta * m := Nat.mul_pos hfactor hm
  have htransfer := differenceLp_le_of_uniform_error hS
    (fun x => 1 + correlation L f₁ f₁ x) (correlation L f f)
    (show 0 < 2 * (localMomentExponentFactor delta * m) by omega) hgain.le
    (fun s hs t ht => by simpa only [f₁, abs_sub_comm] using hcorrerror s hs t ht)
  refine ⟨f, Or.inl rfl, localMomentExponentFactor delta * m, hm', ?_, le_rfl, ?_⟩
  · nlinarith
  unfold localMomentGain
  unfold localMomentGain at htransfer
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

theorem abs_unit_weighted_mul_le {u v b M : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hb : |b| ≤ M) :
    |u * v * b| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg b).trans hb
  rw [abs_mul, abs_of_nonneg (mul_nonneg hu.1 hv.1)]
  exact (mul_le_mul_of_nonneg_left hb (mul_nonneg hu.1 hv.1)).trans
    ((mul_le_mul_of_nonneg_right
      ((mul_le_mul hu.2 hv.2 hv.1 (by norm_num)).trans_eq (one_mul 1)) hM).trans_eq (one_mul M))

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem abs_expect_pair_add_sub_le (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (F : G → G → ℝ) (r s : G) {M etaA etaB : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x y, |F x y| ≤ M)
    (hAshift : (∑ x, |realUniformMass A (x - r) - realUniformMass A x|) ≤ etaA)
    (hBshift : (∑ y, |realUniformMass B (y - s) - realUniformMass B y|) ≤ etaB) :
    |(𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + s)) -
      𝔼 x ∈ A, 𝔼 y ∈ B, F x y| ≤ M * (etaA + etaB) := by
  have hfirst : |(𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + s)) -
      𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)| ≤ M * etaA := by
    exact (abs_expect_add_sub_le A (fun x => 𝔼 y ∈ B, F x (y + s)) r
      (fun x => abs_expect_le_of_bound B hB _ (fun y _ => hF x (y + s)))).trans
        (mul_le_mul_of_nonneg_left hAshift hM)
  have hsecond : |(𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)) -
      𝔼 x ∈ A, 𝔼 y ∈ B, F x y| ≤ M * etaB := by
    apply abs_expect_sub_expect_le A hA
    intro x _
    exact (abs_expect_add_sub_le B (F x) s (hF x)).trans
      (mul_le_mul_of_nonneg_left hBshift hM)
  calc
    _ ≤ |(𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + s)) -
          𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)| +
        |(𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)) -
          𝔼 x ∈ A, 𝔼 y ∈ B, F x y| := abs_sub_le _ _ _
    _ ≤ M * etaA + M * etaB := add_le_add hfirst hsecond
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem expect_neg_add_eq (L : Finset G) (hL : -L = L) (f : G → ℝ) (t : G) :
    (𝔼 x ∈ L, f (-x + t)) = 𝔼 x ∈ L, f (x + t) := by
  have h := Finset.expect_neg_index L (fun x => f (x + t))
  rw [hL] at h
  exact h.symm

theorem reflected_average_sub_le (L : Finset G) (hL : -L = L) (f : G → ℝ) (t : G)
    {M eta : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hTV : (∑ x, |realUniformMass L (x - t) - realUniformMass L x|) ≤ eta) :
    (𝔼 x ∈ L, f x) - M * eta ≤ 𝔼 x ∈ L, f (-x + t) := by
  rw [expect_neg_add_eq L hL f t]
  have h := (abs_expect_add_sub_le L f t hf).trans (mul_le_mul_of_nonneg_left hTV hM)
  have hlower := (abs_le.mp h).1
  linarith

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def replacementIntegral (D Q C : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 z ∈ Q, 𝔼 x ∈ D, 𝔼 t ∈ C, f x * g (z + t) * a (x + (z + t))

theorem replacementIntegral_weighted (D Q C : Finset G) (a f g : G → ℝ) :
    replacementIntegral D Q C a f g =
      𝔼 x ∈ D, f x * (𝔼 t ∈ C, 𝔼 z ∈ Q, g (z + t) * a (x + (z + t))) := by
  unfold replacementIntegral
  rw [Finset.expect_comm Q D]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm Q C]
  simp_rw [mul_assoc, ← Finset.mul_expect]

variable [DecidableEq G]

theorem replacementIntegral_eq_cells (D Q C : Finset G) (a f g : G → ℝ) :
    replacementIntegral D Q C a f g =
      𝔼 z ∈ Q, bilinearIntegral D (C.image (fun t => z + t)) a f g := by
  apply Finset.expect_congr rfl
  intro z _
  unfold bilinearIntegral
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]

variable [Fintype G]

theorem abs_replacementIntegral_sub_le (D Q C : Finset G) (hC : C.Nonempty)
    (a f g : G → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (hf : ∀ x ∈ D, 0 ≤ f x)
    (htest : ∀ x ∈ D, ∀ y, |g y * a (x + y)| ≤ M)
    (hTV : ∀ t ∈ C,
      (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    |replacementIntegral D Q C a f g - bilinearIntegral D Q a f g| ≤
      M * eta * (𝔼 x ∈ D, f x) := by
  have hpoint (x : G) (hx : x ∈ D) :
      |(𝔼 t ∈ C, 𝔼 z ∈ Q, g (z + t) * a (x + (z + t))) -
        𝔼 z ∈ Q, g z * a (x + z)| ≤ M * eta := by
    calc
      _ = |(𝔼 t ∈ C, 𝔼 z ∈ Q, g (z + t) * a (x + (z + t))) -
          𝔼 _t ∈ C, 𝔼 z ∈ Q, g z * a (x + z)| := by
        rw [Finset.expect_const hC]
      _ ≤ M * eta := by
        apply abs_expect_sub_expect_le C hC
        intro t ht
        exact (abs_expect_add_sub_le Q (fun y => g y * a (x + y)) t (htest x hx)).trans
          (mul_le_mul_of_nonneg_left (hTV t ht) hM)
  rw [replacementIntegral_weighted]
  unfold bilinearIntegral
  simp_rw [mul_assoc, ← Finset.mul_expect]
  simpa only [mul_assoc] using abs_weighted_expect_sub_le D f _ _ hf hpoint

theorem abs_replacementIntegral_sub_le_of_unit_weights
    (D Q C : Finset G) (hD : D.Nonempty) (hC : C.Nonempty)
    (a f g : G → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hTV : ∀ t ∈ C,
      (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    |replacementIntegral D Q C a f g - bilinearIntegral D Q a f g| ≤ M * eta := by
  have htest (x : G) (_hx : x ∈ D) (y : G) : |g y * a (x + y)| ≤ M := by
    rw [abs_mul, abs_of_nonneg (hg y).1]
    exact (mul_le_mul_of_nonneg_left (ha _) (hg y).1).trans
      ((mul_le_mul_of_nonneg_right (hg y).2 hM).trans_eq (one_mul M))
  have hmean : (𝔼 x ∈ D, f x) ≤ 1 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ D) => (hf x).2)).trans_eq
      (Finset.expect_const hD 1)
  exact (abs_replacementIntegral_sub_le D Q C hC a f g hM
    (fun x _ => (hf x).1) htest hTV).trans
      ((mul_le_mul_of_nonneg_left hmean (mul_nonneg hM heta)).trans_eq (mul_one _))

theorem abs_slice_sub_replacement_le
    (A Q D C : Finset G) (hD : D.Nonempty) (hC : C.Nonempty)
    (a f g : G → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hsupport : ∀ x, x ∉ A → f x = 0)
    (hTV : ∀ t ∈ C,
      (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    |bilinearIntegral A Q a (Peeling.slice D f) g -
      (D.card : ℝ) / A.card * replacementIntegral D Q C a f g| ≤
      (D.card : ℝ) / A.card * (M * eta) := by
  rw [bilinearIntegral_slice_scale A Q D a f g hsupport, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (D.card : ℝ) / A.card), abs_sub_comm]
  exact mul_le_mul_of_nonneg_left
    (abs_replacementIntegral_sub_le_of_unit_weights D Q C hD hC a f g hM heta ha hf hg hTV)
    (by positivity)

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem smoothed_correlation_le_square_mean
    (L R C : Finset G) (hL : L.Nonempty) (hR : R.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M eta : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hTV : ∀ c ∈ C, ∀ d ∈ C,
      (∑ x, |realUniformMass R (x - (c - d)) - realUniformMass R x|) ≤ eta)
    (z : G) :
    (𝔼 t ∈ R, correlation L f f (z + t)) ≤
      (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.card + M ^ 2 * eta := by
  have hbound (x : G) : |correlation L f f x| ≤ M ^ 2 := by
    simpa only [pow_one, Nat.mul_one] using abs_correlation_self_pow_le L hL f hsupport hf x 1
  have hshift (c : G) (hc : c ∈ C) (d : G) (hd : d ∈ C) :
      (𝔼 t ∈ R, correlation L f f (z + t)) - M ^ 2 * eta ≤
        𝔼 t ∈ R, correlation L f f (z + t + c - d) := by
    have h := (abs_expect_add_sub_le R (fun t => correlation L f f (z + t)) (c - d)
      (fun t => hbound (z + t))).trans (mul_le_mul_of_nonneg_left (hTV c hc d hd) (sq_nonneg M))
    have hlower := (abs_le.mp h).1
    have hindex (t : G) : z + (t + (c - d)) = z + t + c - d := by abel
    simp_rw [hindex] at hlower
    linarith
  have havg := Finset.expect_le_expect (fun c (hc : c ∈ C) =>
    Finset.expect_le_expect (fun d (hd : d ∈ C) => hshift c hc d hd))
  simp only [Finset.expect_const hC] at havg
  have hreorder :
      (𝔼 c ∈ C, 𝔼 d ∈ C, 𝔼 t ∈ R, correlation L f f (z + t + c - d)) =
        𝔼 t ∈ R, 𝔼 c ∈ C, 𝔼 d ∈ C, correlation L f f (z + t + c - d) := by
    calc
      _ = 𝔼 c ∈ C, 𝔼 t ∈ R, 𝔼 d ∈ C, correlation L f f (z + t + c - d) := by
        apply Finset.expect_congr rfl
        intro c _
        exact Finset.expect_comm C R _
      _ = _ := Finset.expect_comm C R _
  rw [hreorder] at havg
  have henergy := Finset.expect_le_expect (fun t (_ : t ∈ R) =>
    opposite_average_correlation_le_square_mean L C f (z + t))
  rw [Finset.expect_const hR] at henergy
  linarith

theorem triple_smoothed_correlation_le_square_mean
    (L A B R C : Finset G) (hL : L.Nonempty) (hA : A.Nonempty) (hB : B.Nonempty)
    (hR : R.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M eta : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hTV : ∀ c ∈ C, ∀ d ∈ C,
      (∑ x, |realUniformMass R (x - (c - d)) - realUniformMass R x|) ≤ eta) :
    (𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R, correlation L f f (a - b + t)) ≤
      (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.card + M ^ 2 * eta := by
  have h := Finset.expect_le_expect (fun a (_ : a ∈ A) =>
    Finset.expect_le_expect (fun b (_ : b ∈ B) =>
      smoothed_correlation_le_square_mean L R C hL hR hC f hsupport hf hTV (a - b)))
  simpa only [Finset.expect_const hA, Finset.expect_const hB] using h

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

theorem exists_localMomentScale (rank : ℕ) {M delta : ℝ}
    (hM : 0 < M) (hdelta : 0 < delta) :
    ∃ kappa : ℝ≥0, 0 < kappa ∧
      kappa + kappa ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      1200 * (max rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ) * M ≤
        min (delta / 2) (localMomentGain delta) := by
  let d : ℝ := (max rank 1 : ℕ)
  let c : ℝ := min (delta / 2) (localMomentGain delta)
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : 0 < c := lt_min (by positivity) (localMomentGain_pos delta)
  let r : ℝ := min (1 / (400 * d)) (c / (2400 * d * M))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  let kappa := r.toNNReal
  have hkappa : (kappa : ℝ) = r := Real.coe_toNNReal r hr.le
  have hr₁ : r * (400 * d) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hr₂ : r * (2400 * d * M) ≤ c :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨kappa, Real.toNNReal_pos.mpr hr, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    push_cast
    rw [hkappa]
    have hdcast : max (rank : ℝ) 1 = d := by simp [d]
    rw [hdcast]
    change r + r ≤ 1 / (100 * (2 * d))
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  · rw [NNReal.coe_add, hkappa]
    change 1200 * d * (r + r) * M ≤ c
    nlinarith

end Erdos3.LocalConvolution

end

end OAI
