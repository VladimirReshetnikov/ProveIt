import OAI.Combinatorics.Progressions.Dynamics.AbsoluteIncrementBudgets
import OAI.Combinatorics.Progressions.Dynamics.RepresentativeWindowBudget
import OAI.Combinatorics.Progressions.Estimates.PositiveWeightContradiction
import OAI.Combinatorics.Progressions.Fourier.FourierWeightedCounting
import OAI.Combinatorics.Progressions.Probability.DensityNormalization
import OAI.Combinatorics.Progressions.Sampling.PositiveScoreComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem distinct_prime_moduli_coprime {J : Type*} (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N) :
    Pairwise (fun i j => Nat.Coprime (N i) (N j)) := by
  intro i j hij
  exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hinj h))

theorem prime_product_unit_of_lt {J : Type*} [Fintype J] (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) {a : ℕ} (ha : 0 < a) (hlt : ∀ j, a < N j) :
    IsUnit (a : ZMod (∏ j, N j)) := by
  apply (ZMod.isUnit_iff_coprime a _).mpr
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro j
  exact ((hprime j).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha (hlt j))).symm

theorem modulus_le_product {J : Type*} [Fintype J] (N : J → ℕ)
    (hpos : ∀ j, 0 < N j) (j : J) : N j ≤ ∏ i, N i :=
  Finset.single_le_prod (fun i _ => hpos i) (Finset.mem_univ j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_crt_counting_contradiction {J : Type*} [Fintype J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) {p : ℝ},
      2 ≤ p → Odd (∏ j, N j) → Real.exp ((p + 2) ^ C) ≤ (∏ j, N j) →
      (∀ j, 64 * k ≤ N j) →
      (∀ m : ℕ, 1 ≤ m → m < k → IsUnit (m : ZMod (∏ j, N j))) →
      ∀ f : ((j : J) → ZMod (N j)) → ℝ,
      (∀ u, 0 ≤ f u ∧ f u ≤ Real.exp p) →
      (𝔼 x : ZMod (∏ j, N j), f (ZMod.prodEquivPi N hN x)) = 1 →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      ¬ CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j) ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (fun x => f (ZMod.prodEquivPi N hN x)) (fun _ => 1 + xi) := by
  classical
  let beta : ℝ := min 1 (1 / (2 * (128 * (k : ℝ)) ^ (Fintype.card J * 2)))
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbeta : 0 < beta := lt_min (by norm_num) (by positivity)
  have hbeta1 : beta ≤ 1 := min_le_left _ _
  let eta := beta / 8
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨F, inst, frequency, c, happ⟩ := exists_crtProgressionWeight_fourier (J := J) k heta
  let _ := inst
  let L : ℝ := ∑ a, ‖c a‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  let epsilon := beta / (8 * (L + 1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hL1 : L + 1 ≠ 0 := by linarith
  have heq : (L + 1) * epsilon = beta / 8 := by dsimp [epsilon]; field_simp [hL1]
  have hepsilon1 : epsilon ≤ 1 := by nlinarith [mul_nonneg hL hepsilon.le]
  have hsmall : L * epsilon + eta * ((2 : ℝ) + 1) < beta := by dsimp [eta]; nlinarith
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_fourier_weighted_counting (k - 2) (by omega) hepsilon
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ _ hN p hp hodd hlarge hsize hunit f hf hmean hfree hcompare
  let mu : ZMod (∏ j, N j) → ℝ := fun x => f (ZMod.prodEquivPi N hN x)
  let slopes : Fin k → ZMod (∏ j, N j) := fun i => i.val
  have hsep (i j : Fin k) (hij : i ≠ j) : IsUnit (slopes i - slopes j) :=
    consecutive_slopes_unit hunit i j hij
  have hcard : (Finset.univ : Finset (Fin k)).card ≤ k - 2 + 2 := by simp; omega
  let G : (ZMod (∏ j, N j) × ZMod (∏ j, N j)) → ℝ :=
    fun z => ∏ i : Fin k, mu (z.1 + slopes i * z.2)
  have hG0 (z) : 0 ≤ G z := Finset.prod_nonneg (fun i _ => (hf _).1)
  have hconst := hcount hp hodd hlarge mu (fun x => hf _) hmean hcompare
    slopes hsep Finset.univ hcard (fun _ : Unit => (1 : ℂ)) (fun _ => 1)
  have hGclose : ‖(𝔼 z, (G z : ℂ)) - 1‖ ≤ epsilon := by
    simpa [configurationFourierWeight, expect_prod_split, G, Complex.ofReal_prod] using hconst
  have hGmean : (𝔼 z, G z) ≤ 2 :=
    (real_mean_le_of_complex_mean_close G hGclose).trans (by linarith)
  let Psi : F → AddChar (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ℂ :=
    fun a => crtConfigurationCharacter N hN (frequency a)
  let H := configurationFourierWeight c Psi
  have hH : ‖(𝔼 z, H z * (G z : ℂ)) - (𝔼 z, H z)‖ ≤ L * epsilon := by
    have h := hcount hp hodd hlarge mu (fun x => hf _) hmean hcompare
      slopes hsep Finset.univ hcard c Psi
    simpa only [expect_prod_split, G, Complex.ofReal_prod, H, L] using h
  apply positive_weight_counting_contradiction (crtProgressionWeight N hN k) G H hbeta
    ((min_le_right _ _).trans (crtProgressionWeight_mean N hN (by omega) hsize))
    hG0 hGmean _ heta.le (happ N hN) hH hsmall
  intro z
  exact crtProgressionWeight_mul_prod_eq_zero N hN (by omega) f hfree z.1 z.2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_score {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
      (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
      0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
      (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
      (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      let hN := distinct_prime_moduli_coprime N hprime hinj
      ∃ T : ZMod (∏ j, N j) → ℝ,
        PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
        Real.exp (-((p + 2) ^ Csc)) ≤
          (𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x) ∧
        ((∏ j, N j : ℕ) : ℝ)⁻¹ ≤
          (𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x) /
            (100 * (1 + xi)) := by
  classical
  obtain ⟨C0, hC0, xi, hxi, hcontra⟩ := exists_crt_counting_contradiction (J := J) k hk
  let Csc := C0 + 1
  obtain ⟨C, hC, hstrict, hbudget⟩ := exists_absolute_side_budget Csc k (by omega) hxi
  refine ⟨Csc, by dsimp [Csc]; omega, C, hC, hstrict, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  let hN := distinct_prime_moduli_coprime N hprime hinj
  let original : ZMod (∏ j, N j) → ℝ := fun x => f (ZMod.prodEquivPi N hN x)
  let normalized : ((j : J) → ZMod (N j)) → ℝ := fun u => f u / alpha
  have hlower := density_lower_bound_of_log_inverse halpha hlog
  have hnumb := absolute_normalization_budget C0 hp halpha hlower
  have hb := hbudget p hp
  have hside (j) : 64 * k ≤ N j := by exact_mod_cast hb.2.1.trans (hsize j)
  let j0 : J := Classical.choice inferInstance
  have hprod : (N j0 : ℝ) ≤ (∏ j, N j : ℕ) := by
    exact_mod_cast modulus_le_product N (fun j => (hprime j).pos) j0
  have hlarge : Real.exp ((p + 2) ^ C0) ≤ (∏ j, N j : ℕ) :=
    (Real.exp_le_exp.mpr (hnumb.1.trans hb.1)).trans ((hsize j0).trans hprod)
  have hunit (a : ℕ) (ha : 1 ≤ a) (hak : a < k) : IsUnit (a : ZMod (∏ j, N j)) := by
    apply prime_product_unit_of_lt N hprime ha
    intro j
    have hj := hside j
    omega
  have hodd : Odd (∏ j, N j) := Nat.coprime_two_left.mp
    ((ZMod.isUnit_iff_coprime 2 _).mp (hunit 2 (by omega) (by omega)))
  have horiginal : (𝔼 x, original x) = alpha := by
    calc
      _ = 𝔼 u, f u := Fintype.expect_equiv (ZMod.prodEquivPi N hN).toEquiv _ _ (fun _ => rfl)
      _ = alpha := hmean
  have hnormalized : (𝔼 x : ZMod (∏ j, N j), normalized (ZMod.prodEquivPi N hN x)) = 1 :=
    normalized_density_mean original halpha horiginal
  have hnormfree : IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support normalized) k := by
    dsimp only [normalized]
    rw [support_normalized_density f halpha.ne']
    exact hfree
  have hnot := hcontra N hN hp hodd hlarge hside hunit normalized
    (normalized_density_bounds f halpha hlower hf) hnormalized hnormfree
  have hnotScore : ¬ CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j)
      ((p + 2) ^ Csc) (Real.exp (-((p + 2) ^ Csc))) original (fun _ => (1 + xi) * alpha) := by
    intro hcomp
    have hn : CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j)
        ((p + 2) ^ Csc) (Real.exp (-((p + 2) ^ Csc)) / alpha)
        (fun x => original x / alpha) (fun _ => 1 + xi) :=
      CyclicNiltestUpperComparison.normalize hcomp halpha
    exact hnot (CyclicNiltestUpperComparison.mono_budget hn hnumb.1 hnumb.2)
  obtain ⟨T, hT, hscore⟩ := exists_positive_score_of_not_upperComparison hnotScore
  refine ⟨T, hT, hscore.le, ?_⟩
  have hbig : 100 * (1 + xi) * Real.exp ((p + 2) ^ Csc) ≤ (∏ j, N j : ℕ) :=
    hb.2.2.trans ((hsize j0).trans hprod)
  have hM : 0 < 100 * (1 + xi) := by positivity
  calc
    _ = 1 / ((∏ j, N j : ℕ) : ℝ) := (one_div _).symm
    _ ≤ 1 / (100 * (1 + xi) * Real.exp ((p + 2) ^ Csc)) :=
      one_div_le_one_div_of_le (mul_pos hM (Real.exp_pos _)) hbig
    _ = Real.exp (-((p + 2) ^ Csc)) / (100 * (1 + xi)) := by
      simp [Real.exp_neg, div_eq_mul_inv, mul_comm]
    _ ≤ _ := div_le_div_of_nonneg_right hscore.le hM.le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_increment {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
      (f : ((j : J) → ZMod (N j)) → ℝ) {alpha : ℝ},
      0 < alpha → (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      let p := max 2 (Real.log (1 / alpha))
      (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
      let hN := distinct_prime_moduli_coprime N hprime hinj
      ∃ T : ZMod (∏ j, N j) → ℝ,
        PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ C) T ∧
        (∀ x, 0 ≤ T x ∧ T x ≤ 1) ∧
        Real.exp (-((p + 2) ^ C)) ≤
          𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x := by
  obtain ⟨Csc, _, C, hC, hstrict, xi, hxi, hscore⟩ := exists_absolute_crt_score (J := J) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha halpha hf hmean hfree p hsize
  have hp : 2 ≤ p := le_max_left _ _
  have hlog : Real.log (1 / alpha) ≤ p := le_max_right _ _
  obtain ⟨T, hT, hs, _⟩ := hscore N hprime hinj f halpha hp hlog hsize hf hmean hfree
  have hcost : (p + 2) ^ Csc ≤ (p + 2) ^ C :=
    pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hstrict.le
  exact ⟨T, hT.mono le_rfl hcost, hT.unit_interval,
    (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hs⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem density_test_score_abs_le {f T alpha xi : ℝ}
    (hf : 0 ≤ f ∧ f ≤ 1) (hT : 0 ≤ T ∧ T ≤ 1)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1) (hxi : 0 ≤ xi) :
    |(f - (1 + xi) * alpha) * T| ≤ 1 + xi := by
  have hM : 0 ≤ 1 + xi := by positivity
  have hc0 := mul_nonneg hM halpha.1
  have hc1 : (1 + xi) * alpha ≤ 1 + xi :=
    mul_le_of_le_one_right hM halpha.2
  have hdiff : |f - (1 + xi) * alpha| ≤ 1 + xi := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg hT.1]
  exact (mul_le_mul_of_nonneg_right hdiff hT.1).trans (mul_le_of_le_one_right hM hT.2)

theorem exists_absolute_crt_window {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧
      ∃ Cwindow : ℕ, 2 ≤ Cwindow ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        let hN := distinct_prime_moduli_coprime N hprime hinj
        ∃ (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow),
          PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
          Real.log (2 + (w.lip : ℝ)) ≤ (p + 2) ^ Cwindow ∧
          Real.exp (-((p + 2) ^ Cwindow)) ≤
            𝔼 u : (j : J) → ZMod (N j),
              ((f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u)) *
                (w.crtPatch N hN (k - 2) (by omega)).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨Csc, hCsc, C, hC, hstrict, xi, hxi, habsolute⟩ :=
    exists_absolute_crt_score (J := J) k hk
  obtain ⟨D, hD, hwindow⟩ := exists_polynomial_scored_crt_representative_patch
  obtain ⟨a, ha⟩ := exists_nat_ge (Real.log (1 + xi))
  obtain ⟨Cwindow, hCwindow, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (((Polynomial.X + 2) ^ Csc + Polynomial.C a + 2) ^ D)
  refine ⟨Csc, hCsc, C, hC, hstrict, Cwindow, hCwindow, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  let hN := distinct_prime_moduli_coprime N hprime hinj
  obtain ⟨T, hT, hscore, hmod⟩ := habsolute N hprime hinj f halpha hp hlog hsize hf hmean hfree
  let F : ZMod (∏ j, N j) → ℝ :=
    fun x => (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x
  let sigma : ℝ := 𝔼 x, F x
  let q : ℝ := (p + 2) ^ Csc + a
  have hp0 : 0 ≤ p := by linarith
  have hpow0 : 0 ≤ (p + 2) ^ Csc := by positivity
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hq : 0 ≤ q := add_nonneg hpow0 ha0
  have hM : 0 < 1 + xi := by positivity
  have hMexp : 1 + xi ≤ Real.exp q := by
    apply (Real.log_le_iff_le_exp hM).mp
    exact ha.trans (by dsimp only [q]; linarith)
  have hsig : Real.exp (-q) ≤ sigma :=
    (Real.exp_le_exp.mpr (show -q ≤ -((p + 2) ^ Csc) by dsimp only [q]; linarith)).trans hscore
  have halpha1 : alpha ≤ 1 := by
    rw [← hmean]
    exact (Finset.expect_le_expect (fun u _ => (hf u).2)).trans_eq (Fintype.expect_const 1)
  have hcap (x : ZMod (∏ j, N j)) : |F x| ≤ 1 + xi :=
    density_test_score_abs_le (hf _) (hT.unit_interval x) ⟨halpha.le, halpha1⟩ hxi.le
  obtain ⟨w, hw, hws⟩ := hwindow N hN (k - 2) (by omega) F hq hM hMexp hsig
    hcap le_rfl (by simpa only [one_div] using hmod)
  have hb : (q + 2) ^ D ≤ (p + 2) ^ Cwindow := by
    simpa [Polynomial.eval₂_pow, q] using hbudget p hp0
  refine ⟨T, w, hT, hw.trans hb, ?_⟩
  have hs := (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hws
  have he (u : (j : J) → ZMod (N j)) :
      F ((ZMod.prodEquivPi N hN).symm u) =
        (f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u) := by
    dsimp only [F]
    rw [RingEquiv.apply_symm_apply]
  simpa only [he] using hs

end Erdos3

end

end OAI
