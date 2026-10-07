import OAI.Combinatorics.Progressions.Polynomial.BinomialMomentAmplification

namespace OAI


namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

noncomputable def finiteSetLp (s : Finset ι) (f : ι → ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (𝔼 i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ))

theorem finiteSetLp_of_pos (s : Finset ι) (f : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s f p = (𝔼 i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ)) := by
  simp only [finiteSetLp, hp.ne', ite_false]

theorem finiteSetLp_nonneg (s : Finset ι) (f : ι → ℝ) (p : ℕ) :
    0 ≤ finiteSetLp s f p := by
  unfold finiteSetLp
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Finset.expect_nonneg (fun _ _ => by positivity)) _

theorem finiteSetLp_pow (s : Finset ι) (f : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s f p ^ p = 𝔼 i ∈ s, |f i| ^ p := by
  rw [finiteSetLp_of_pos s f hp, ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.expect_nonneg (fun _ _ => by positivity))]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [one_div_mul_cancel hpR, Real.rpow_one]

theorem finiteSetLp_eq_sum (s : Finset ι) (f : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s f p =
      (∑ i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ)) / (s.card : ℝ) ^ (1 / (p : ℝ)) := by
  rw [finiteSetLp_of_pos s f hp, Finset.expect_eq_sum_div_card,
    Real.div_rpow (Finset.sum_nonneg (fun _ _ => by positivity)) (Nat.cast_nonneg _)]

theorem finiteSetLp_const {s : Finset ι} (hs : s.Nonempty) (c : ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s (fun _ => c) p = |c| := by
  rw [finiteSetLp_of_pos s (fun _ => c) hp, Finset.expect_const hs]
  simpa only [one_div] using Real.pow_rpow_inv_natCast (abs_nonneg c) hp.ne'

theorem finiteSetLp_mono_abs (s : Finset ι) (f g : ι → ℝ) {p : ℕ} (hp : 0 < p)
    (hfg : ∀ i ∈ s, |f i| ≤ |g i|) :
    finiteSetLp s f p ≤ finiteSetLp s g p := by
  rw [finiteSetLp_of_pos s f hp, finiteSetLp_of_pos s g hp]
  apply Real.rpow_le_rpow (Finset.expect_nonneg (fun _ _ => by positivity))
  · exact Finset.expect_le_expect (fun i hi => pow_le_pow_left₀ (abs_nonneg _) (hfg i hi) p)
  · positivity

theorem finiteSetLp_le_of_bound {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) {p : ℕ} (hp : 0 < p) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ i ∈ s, |f i| ≤ M) : finiteSetLp s f p ≤ M := by
  have h := finiteSetLp_mono_abs s f (fun _ => M) hp
    (fun i hi => by simpa only [abs_of_nonneg hM] using hf i hi)
  simpa only [finiteSetLp_const hs M hp, abs_of_nonneg hM] using h

theorem finiteSetLp_add_le (s : Finset ι) (f g : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s (fun i => f i + g i) p ≤ finiteSetLp s f p + finiteSetLp s g p := by
  simp only [finiteSetLp_eq_sum s _ hp]
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h := Real.Lp_add_le s f g hpR
  simp only [Real.rpow_natCast] at h
  have hd : 0 ≤ (s.card : ℝ) ^ (1 / (p : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simpa only [add_div] using div_le_div_of_nonneg_right h hd

theorem finiteSetLp_le_of_uniform_error {s : Finset ι} (hs : s.Nonempty)
    (f g : ι → ℝ) {p : ℕ} (hp : 0 < p) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ i ∈ s, |f i - g i| ≤ epsilon) :
    finiteSetLp s f p ≤ finiteSetLp s g p + epsilon := by
  have h := finiteSetLp_add_le s g (fun i => f i - g i) hp
  have heq : (fun i => g i + (f i - g i)) = f := by funext i; ring
  rw [heq] at h
  exact h.trans (add_le_add le_rfl (finiteSetLp_le_of_bound hs _ hp hepsilon herror))

end Erdos3


namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def convolution (L : Finset G) (f g : G → ℝ) (t : G) : ℝ :=
  (∑ x, f x * g (t - x)) / L.card

noncomputable def correlation (L : Finset G) (f g : G → ℝ) (t : G) : ℝ :=
  (∑ x, f (x + t) * g x) / L.card

noncomputable def sumMoment (S : Finset G) (f : G → ℝ) (j : ℕ) : ℝ :=
  𝔼 s ∈ S, 𝔼 t ∈ S, f (s + t) ^ j

noncomputable def differenceMoment (S : Finset G) (f : G → ℝ) (j : ℕ) : ℝ :=
  𝔼 s ∈ S, 𝔼 t ∈ S, f (s - t) ^ j

noncomputable def momentVector (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) : ℝ :=
  𝔼 s ∈ S, ∏ i, f (s - v i)

noncomputable def plusMomentVector (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) : ℝ :=
  𝔼 s ∈ S, ∏ i, f (s + v i)

theorem convolution_add (L : Finset G) (f g : G → ℝ) (s t : G) :
    convolution L f g (s + t) = (∑ x, f (s - x) * g (t + x)) / L.card := by
  unfold convolution
  congr 1
  apply Fintype.sum_equiv (Equiv.subLeft s)
  intro x
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  congr 1
  congr 1
  abel

theorem correlation_sub (L : Finset G) (f g : G → ℝ) (s t : G) :
    correlation L f g (s - t) = (∑ x, f (s - x) * g (t - x)) / L.card := by
  unfold correlation
  congr 1
  apply Fintype.sum_equiv (Equiv.subLeft t)
  intro x
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  congr 1
  congr 1
  abel

omit [Fintype G] in
theorem plusMomentVector_eq_neg (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) :
    plusMomentVector S f j v = momentVector S f j (-v) := by
  simp only [plusMomentVector, momentVector, Pi.neg_apply, sub_neg_eq_add]

theorem sum_momentVector_mul (S : Finset G) (f g : G → ℝ) (j : ℕ) :
    (∑ v : Fin j → G, momentVector S f j v * momentVector S g j v) =
      𝔼 s ∈ S, 𝔼 t ∈ S, (∑ x : G, f (s - x) * g (t - x)) ^ j := by
  unfold momentVector
  simp_rw [Finset.expect_mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro s _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro t _
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

theorem sum_momentVector_mul_plus (S : Finset G) (f g : G → ℝ) (j : ℕ) :
    (∑ v : Fin j → G, momentVector S f j v * plusMomentVector S g j v) =
      𝔼 s ∈ S, 𝔼 t ∈ S, (∑ x : G, f (s - x) * g (t + x)) ^ j := by
  unfold momentVector plusMomentVector
  simp_rw [Finset.expect_mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro s _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro t _
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

theorem sum_sq_plusMomentVector (S : Finset G) (f : G → ℝ) (j : ℕ) :
    (∑ v : Fin j → G, plusMomentVector S f j v ^ 2) =
      ∑ v : Fin j → G, momentVector S f j v ^ 2 := by
  simp_rw [plusMomentVector_eq_neg]
  exact Fintype.sum_equiv (Equiv.neg (Fin j → G)) _ _ (fun _ => rfl)

theorem differenceMoment_correlation_eq (L S : Finset G) (f g : G → ℝ) (j : ℕ) :
    differenceMoment S (correlation L f g) j =
      (∑ v : Fin j → G, momentVector S f j v * momentVector S g j v) / (L.card : ℝ) ^ j := by
  unfold differenceMoment
  simp_rw [correlation_sub, div_pow, ← Finset.expect_div]
  rw [sum_momentVector_mul]

theorem sumMoment_convolution_eq (L S : Finset G) (f g : G → ℝ) (j : ℕ) :
    sumMoment S (convolution L f g) j =
      (∑ v : Fin j → G, momentVector S f j v * plusMomentVector S g j v) / (L.card : ℝ) ^ j := by
  unfold sumMoment
  simp_rw [convolution_add, div_pow, ← Finset.expect_div]
  rw [sum_momentVector_mul_plus]

theorem differenceMoment_self_nonneg (L S : Finset G) (f : G → ℝ) (j : ℕ) :
    0 ≤ differenceMoment S (correlation L f f) j := by
  rw [differenceMoment_correlation_eq]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) (by positivity)

theorem sumMoment_convolution_sq_le (L S : Finset G) (f g : G → ℝ) (j : ℕ) :
    sumMoment S (convolution L f g) j ^ 2 ≤
      differenceMoment S (correlation L f f) j * differenceMoment S (correlation L g g) j := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (momentVector S f j) (plusMomentVector S g j)
  rw [sum_sq_plusMomentVector] at hCS
  have h := div_le_div_of_nonneg_right hCS (sq_nonneg ((L.card : ℝ) ^ j))
  rw [sumMoment_convolution_eq, differenceMoment_correlation_eq, differenceMoment_correlation_eq]
  simpa only [div_pow, pow_two, div_mul_div_comm] using h

end Erdos3.LocalConvolution


namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

theorem expect_tail_mul_pow_le (S : Finset ι) (f : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (q : ℕ) :
    t ^ q * (𝔼 i ∈ S, if t < |f i| then (1 : ℝ) else 0) ≤ 𝔼 i ∈ S, |f i| ^ q := by
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro i _
  by_cases hi : t < |f i|
  · simpa only [hi, ite_true, mul_one] using pow_le_pow_left₀ ht hi.le q
  · simp only [hi, ite_false, mul_zero]
    positivity

theorem finiteSetLp_tail_le (S : Finset ι) (f : ι → ℝ) {q : ℕ} (hq : 0 < q)
    {delta t : ℝ} (ht : 0 < t) (hLp : finiteSetLp S f q ≤ delta) :
    (𝔼 i ∈ S, if t < |f i| then (1 : ℝ) else 0) ≤ (delta / t) ^ q := by
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos ht q)).mpr
  calc
    _ = t ^ q * (𝔼 i ∈ S, if t < |f i| then (1 : ℝ) else 0) := mul_comm _ _
    _ ≤ 𝔼 i ∈ S, |f i| ^ q := expect_tail_mul_pow_le S f ht.le q
    _ = finiteSetLp S f q ^ q := (finiteSetLp_pow S f hq).symm
    _ ≤ delta ^ q := pow_le_pow_left₀ (finiteSetLp_nonneg S f q) hLp q

theorem finiteSetLp_double_tail_le (S : Finset ι) (f : ι → ℝ) {q : ℕ} (hq : 0 < q)
    {delta : ℝ} (hdelta : 0 < delta) (hLp : finiteSetLp S f q ≤ delta) :
    (𝔼 i ∈ S, if 2 * delta < |f i| then (1 : ℝ) else 0) ≤ (1 / 2 : ℝ) ^ q := by
  have h := finiteSetLp_tail_le S f hq (show 0 < 2 * delta by positivity) hLp
  have heq : delta / (2 * delta) = (1 / 2 : ℝ) := by field_simp
  simpa only [heq] using h

end Erdos3


namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def momentAmplificationFactor (delta : ℝ) : ℕ := ⌈2 / delta⌉₊ + 1

noncomputable def momentAmplificationGain (delta : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 / (momentAmplificationFactor delta : ℝ)) - 1

theorem momentAmplificationFactor_pos (delta : ℝ) : 0 < momentAmplificationFactor delta := by
  unfold momentAmplificationFactor
  omega

theorem momentAmplificationGain_pos (delta : ℝ) : 0 < momentAmplificationGain delta := by
  have hR : (0 : ℝ) < momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / (momentAmplificationFactor delta : ℝ))
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_le_one (delta : ℝ) : momentAmplificationGain delta ≤ 1 := by
  have hR : (1 : ℝ) ≤ momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have hinv : 1 / (momentAmplificationFactor delta : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hR
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hinv
  rw [Real.rpow_one] at h
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_pow (delta : ℝ) :
    (1 + momentAmplificationGain delta) ^ momentAmplificationFactor delta = 2 := by
  unfold momentAmplificationGain
  rw [← add_sub_assoc, add_sub_cancel_left, one_div]
  exact Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 2) (momentAmplificationFactor_pos delta).ne'

theorem finiteSetLp_unbalance {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ s, f x ^ k)
    (hlarge : delta ≤ finiteSetLp s f n) :
    1 + momentAmplificationGain delta ≤
      finiteSetLp s (fun x => 1 + f x) (momentAmplificationFactor delta * n) := by
  let R : ℕ := ⌈2 / delta⌉₊
  have hR : 2 ≤ (R : ℝ) * delta :=
    (div_le_iff₀ hdelta).mp (Nat.le_ceil (2 / delta))
  have hmoment : delta ^ n ≤ 𝔼 x ∈ s, f x ^ n := by
    have h := pow_le_pow_left₀ hdelta.le hlarge n
    rw [finiteSetLp_pow s f hn] at h
    simpa only [heven.pow_abs] using h
  have hN : 0 < momentAmplificationFactor delta * n :=
    Nat.mul_pos (momentAmplificationFactor_pos delta) hn
  have hmomentLarge : (2 : ℝ) ^ n ≤
      𝔼 x ∈ s, (1 + f x) ^ (momentAmplificationFactor delta * n) := by
    calc
      (2 : ℝ) ^ n ≤ ((R : ℝ) * delta) ^ n := pow_le_pow_left₀ (by norm_num) hR n
      _ = (R : ℝ) ^ n * delta ^ n := mul_pow _ _ _
      _ ≤ (R : ℝ) ^ n * (𝔼 x ∈ s, f x ^ n) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ ≤ 𝔼 x ∈ s, (1 + f x) ^ (momentAmplificationFactor delta * n) :=
        expect_one_add_pow_block_lower s f hmom R n
  apply le_of_pow_le_pow_left₀ hN.ne' (finiteSetLp_nonneg _ _ _)
  calc
    (1 + momentAmplificationGain delta) ^ (momentAmplificationFactor delta * n) = (2 : ℝ) ^ n := by
      rw [pow_mul, momentAmplificationGain_pow]
    _ ≤ 𝔼 x ∈ s, (1 + f x) ^ (momentAmplificationFactor delta * n) := hmomentLarge
    _ ≤ 𝔼 x ∈ s, |1 + f x| ^ (momentAmplificationFactor delta * n) := by
      apply Finset.expect_le_expect
      intro x _
      simpa only [abs_pow] using le_abs_self ((1 + f x) ^ (momentAmplificationFactor delta * n))
    _ = finiteSetLp s (fun x => 1 + f x) (momentAmplificationFactor delta * n) ^
        (momentAmplificationFactor delta * n) := (finiteSetLp_pow _ _ hN).symm

end Erdos3.LocalConvolution


namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def sumLp (S : Finset G) (f : G → ℝ) (p : ℕ) : ℝ :=
  finiteSetLp (S ×ˢ S) (fun x => f (x.1 + x.2)) p

noncomputable def differenceLp (S : Finset G) (f : G → ℝ) (p : ℕ) : ℝ :=
  finiteSetLp (S ×ˢ S) (fun x => f (x.1 - x.2)) p

theorem sumLp_nonneg (S : Finset G) (f : G → ℝ) (p : ℕ) : 0 ≤ sumLp S f p :=
  finiteSetLp_nonneg _ _ _

theorem differenceLp_nonneg (S : Finset G) (f : G → ℝ) (p : ℕ) : 0 ≤ differenceLp S f p :=
  finiteSetLp_nonneg _ _ _

theorem sumLp_pow (S : Finset G) (f : G → ℝ) {p : ℕ} (hp : 0 < p) (heven : Even p) :
    sumLp S f p ^ p = sumMoment S f p := by
  rw [sumLp, finiteSetLp_pow _ _ hp, Finset.expect_product]
  simp only [heven.pow_abs, sumMoment]

theorem differenceLp_pow (S : Finset G) (f : G → ℝ) {p : ℕ} (hp : 0 < p) (heven : Even p) :
    differenceLp S f p ^ p = differenceMoment S f p := by
  rw [differenceLp, finiteSetLp_pow _ _ hp, Finset.expect_product]
  simp only [heven.pow_abs, differenceMoment]

theorem sumLp_le_of_uniform_error {S : Finset G} (hS : S.Nonempty) (f g : G → ℝ)
    {p : ℕ} (hp : 0 < p) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ s ∈ S, ∀ t ∈ S, |f (s + t) - g (s + t)| ≤ epsilon) :
    sumLp S f p ≤ sumLp S g p + epsilon := by
  apply finiteSetLp_le_of_uniform_error (hS.product hS) _ _ hp hepsilon
  intro x hx
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hx
  exact herror x.1 hs x.2 ht

theorem differenceLp_le_of_uniform_error {S : Finset G} (hS : S.Nonempty) (f g : G → ℝ)
    {p : ℕ} (hp : 0 < p) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ s ∈ S, ∀ t ∈ S, |f (s - t) - g (s - t)| ≤ epsilon) :
    differenceLp S f p ≤ differenceLp S g p + epsilon := by
  apply finiteSetLp_le_of_uniform_error (hS.product hS) _ _ hp hepsilon
  intro x hx
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hx
  exact herror x.1 hs x.2 ht

theorem convolution_sumLp_sq_le [Fintype G] (L S : Finset G) (f g : G → ℝ)
    {m : ℕ} (hm : 0 < m) :
    sumLp S (convolution L f g) (2 * m) ^ 2 ≤
      differenceLp S (correlation L f f) (2 * m) * differenceLp S (correlation L g g) (2 * m) := by
  have hp : 0 < 2 * m := by omega
  have heven : Even (2 * m) := ⟨m, by omega⟩
  have hCS := sumMoment_convolution_sq_le L S f g (2 * m)
  rw [← sumLp_pow S (convolution L f g) hp heven,
    ← differenceLp_pow S (correlation L f f) hp heven,
    ← differenceLp_pow S (correlation L g g) hp heven] at hCS
  apply le_of_pow_le_pow_left₀ hp.ne'
    (mul_nonneg (differenceLp_nonneg _ _ _) (differenceLp_nonneg _ _ _))
  calc
    (sumLp S (convolution L f g) (2 * m) ^ 2) ^ (2 * m) =
        (sumLp S (convolution L f g) (2 * m) ^ (2 * m)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ _ := hCS
    _ = _ := (mul_pow _ _ _).symm

end Erdos3.LocalConvolution


namespace Erdos3

open scoped BigOperators

theorem flat_weighted_pointwise_le {A B d epsilon delta W M : ℝ}
    (hA : 0 ≤ A ∧ A ≤ W) (hB : 0 ≤ B ∧ B ≤ W) (hd : 0 ≤ d ∧ d ≤ M)
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta)) :
    (A - (1 + epsilon) * B) * d ≤ (1 + 2 * delta) * (A - B) +
      W * (M + 2) * (if 2 * delta < |d - 1| then (1 : ℝ) else 0) := by
  by_cases hbad : 2 * delta < |d - 1|
  · simp only [hbad, ite_true, mul_one]
    have hW : 0 ≤ W := hA.1.trans hA.2
    have hAd : A * d ≤ W * M := mul_le_mul hA.2 hd.2 hd.1 hW
    have hBweight : (1 + 2 * delta) * B ≤ 2 * W :=
      mul_le_mul (by linarith) hB.2 hB.1 (by norm_num)
    have hAnonneg : 0 ≤ (1 + 2 * delta) * A := mul_nonneg (by linarith) hA.1
    have hnegative : 0 ≤ ((1 + epsilon) * B) * d :=
      mul_nonneg (mul_nonneg (by linarith) hB.1) hd.1
    nlinarith
  · simp only [hbad, ite_false, mul_zero, add_zero]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (le_of_not_gt hbad)
    have hAd : A * d ≤ A * (1 + 2 * delta) := mul_le_mul_of_nonneg_left (by linarith) hA.1
    have hBd : (1 + epsilon) * B * (1 - 2 * delta) ≤ (1 + epsilon) * B * d :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hB.1)
    have hBcoeff := mul_le_mul_of_nonneg_right hcoeff hB.1
    nlinarith

theorem flat_weighted_average_le {ι : Type*} (S : Finset ι) (A B d : ι → ℝ)
    {q : ℕ} (hq : 0 < q) {epsilon delta W M eta : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hA : ∀ i ∈ S, 0 ≤ A i ∧ A i ≤ W) (hB : ∀ i ∈ S, 0 ≤ B i ∧ B i ≤ W)
    (hd : ∀ i ∈ S, 0 ≤ d i ∧ d i ≤ M)
    (hLp : finiteSetLp S (fun i => d i - 1) q ≤ delta)
    (hmean : (𝔼 i ∈ S, (A i - B i)) ≤ eta) :
    (𝔼 i ∈ S, (A i - (1 + epsilon) * B i) * d i) ≤
      (1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q := by
  have htail := finiteSetLp_double_tail_le S (fun i => d i - 1) hq hdelta hLp
  calc
    _ ≤ 𝔼 i ∈ S, ((1 + 2 * delta) * (A i - B i) +
        W * (M + 2) * (if 2 * delta < |d i - 1| then (1 : ℝ) else 0)) := by
      apply Finset.expect_le_expect
      intro i hi
      exact flat_weighted_pointwise_le (hA i hi) (hB i hi) (hd i hi)
        hepsilon hdelta.le hdelta2 hcoeff
    _ = (1 + 2 * delta) * (𝔼 i ∈ S, (A i - B i)) +
        W * (M + 2) * (𝔼 i ∈ S, if 2 * delta < |d i - 1| then (1 : ℝ) else 0) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hmean (by positivity))
      (mul_le_mul_of_nonneg_left htail (by positivity))

end Erdos3

end OAI
