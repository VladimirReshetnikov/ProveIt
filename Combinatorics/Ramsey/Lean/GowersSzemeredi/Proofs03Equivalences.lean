import GowersSzemeredi.Proofs03Basic

/-!
# Equivalent formulations of higher Gowers uniformity

This module proves the higher-difference preservation and normalization facts
used in Gowers's Lemma 3.1.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma difference_discValued {N : Nat} {g : ZMod N → Complex}
    (hg : DiscValued g) (r : ZMod N) : DiscValued (difference g r) := by
  intro s
  rw [difference, norm_mul, norm_star]
  exact (mul_le_mul (hg s) (hg (s - r)) (norm_nonneg _) zero_le_one).trans
    (mul_one 1).le

lemma iteratedDifference_discValued {N : Nat} {g : ZMod N → Complex}
    (hg : DiscValued g) (a : List (ZMod N)) : DiscValued (iteratedDifference g a) := by
  induction a with
  | nil => simpa only [iteratedDifference]
  | cons r a ih =>
      simpa only [iteratedDifference] using difference_discValued ih r

lemma cubeDifference_discValued {N d : Nat} {g : ZMod N → Complex}
    (hg : DiscValued g) (a : Point N d) : DiscValued (cubeDifference g a) :=
  iteratedDifference_discValued hg (List.ofFn a)

lemma discValued_uniform_one {N d : Nat} [NeZero N] {g : ZMod N → Complex}
    (hg : DiscValued g) : UniformOfDegree g 1 d := by
  have hterm (a : Point N d) :
      ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 ≤ (N : Real) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    calc
      ‖∑ s : ZMod N, cubeDifference g a s‖ ≤
          ∑ s : ZMod N, ‖cubeDifference g a s‖ := by
        simpa using norm_sum_le (Finset.univ : Finset (ZMod N)) (cubeDifference g a)
      _ ≤ ∑ _s : ZMod N, (1 : Real) := by
        apply Finset.sum_le_sum
        intro s _
        exact cubeDifference_discValued hg a s
      _ = (N : Real) := by simp [ZMod.card]
  calc
    ∑ a : Point N d, ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 ≤
        ∑ _a : Point N d, (N : Real) ^ 2 :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = 1 * (N : Real) ^ (d + 2) := by
      simp [Point, ZMod.card, pow_add]

lemma difference_comm {N : Nat} (g : ZMod N → Complex) (a b : ZMod N) :
    difference (difference g a) b = difference (difference g b) a := by
  funext s
  simp only [difference, star_mul, star_star]
  have harg : s - b - a = s - a - b := by abel
  rw [harg]
  ring

lemma iteratedDifference_difference {N : Nat} (g : ZMod N → Complex)
    (r : ZMod N) (a : List (ZMod N)) :
    iteratedDifference (difference g r) a = difference (iteratedDifference g a) r := by
  induction a with
  | nil => rfl
  | cons b a ih =>
      simp only [iteratedDifference]
      rw [ih, difference_comm]

lemma cubeDifference_difference {N d : Nat} (g : ZMod N → Complex)
    (r : ZMod N) (a : Point N d) :
    cubeDifference (difference g r) a = difference (cubeDifference g a) r := by
  exact iteratedDifference_difference g r (List.ofFn a)

lemma uniformOfDegree_mono_parameter {N d : Nat} [NeZero N]
    {g : ZMod N → Complex} {alpha beta : Real} (h : alpha ≤ beta)
    (hg : UniformOfDegree g alpha d) : UniformOfDegree g beta d := by
  exact hg.trans (mul_le_mul_of_nonneg_right h (pow_nonneg (by positivity) _))

private lemma cubeDifference_one {N : Nat} (g : ZMod N → Complex)
    (a : Point N 1) : cubeDifference g a = difference g (a 0) := rfl

private lemma degreeOneEnergy_eq_correlation {N : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 =
      ∑ r : ZMod N, ‖∑ s : ZMod N, difference g r s‖ ^ 2 := by
  let e := Equiv.funUnique (Fin 1) (ZMod N)
  have h := e.sum_comp fun r : ZMod N =>
    ‖∑ s : ZMod N, difference g r s‖ ^ 2
  simpa [e, cubeDifference_one] using h

lemma fourthMoment_eq_degreeOneEnergy {N : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ r : ZMod N, ‖fourier g r‖ ^ 4 =
      (N : Real) * ∑ a : Point N 1,
        ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 := by
  have h := lemma_2_1_holds N g g
  rw [degreeOneEnergy_eq_correlation]
  simpa only [difference, ← pow_add] using h

lemma degreeOne_uniform_iff_condition2i {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (c : Real) :
    UniformOfDegree g c 1 ↔ uniformCondition2i g c := by
  unfold UniformOfDegree uniformCondition2i
  rw [degreeOneEnergy_eq_correlation]
  norm_num [difference]

private lemma sum_localDegreeOneEnergy_eq_uniformEnergy {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ a : Point N n, ∑ b : Point N 1,
        ‖∑ s : ZMod N, cubeDifference (cubeDifference g a) b s‖ ^ 2 =
      ∑ c : Point N (n + 1), ‖∑ s : ZMod N, cubeDifference g c s‖ ^ 2 := by
  rw [sum_point_succ, Finset.sum_comm (s := (Finset.univ : Finset (ZMod N)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [degreeOneEnergy_eq_correlation]
  simp only [cubeDifference_cons]

private lemma higher_condition_i_iff_ii {N d : Nat} [NeZero N]
    (g : ZMod N → Complex) (c : Real) :
    UniformOfDegree g c d ↔ higherUniformConditionii g c d := by
  have h := congrArg Complex.re (sum_cube_succ_eq_sum_norm_sq (n := d) g)
  have hreal :
      (∑ b : Point N (d + 1), ∑ s : ZMod N, cubeDifference g b s).re =
        ∑ a : Point N d, ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 := by
    simpa only [map_sum, Complex.ofReal_re] using h
  unfold UniformOfDegree higherUniformConditionii
  rw [hreal]

/-- Local energies `0 ≤ e x ≤ D` have total at most `B * D` exactly when they are bounded by
`alpha x * D` for weights `alpha x ∈ [0, 1]` of total at most `B`. -/
private lemma sum_le_iff_exists_weights {X : Type*} [Fintype X] (e : X → Real) {B D : Real}
    (hD : 0 < D) (he : ∀ x, 0 ≤ e x ∧ e x ≤ D) :
    ∑ x, e x ≤ B * D ↔ ∃ alpha : X → Real, (∀ x, 0 ≤ alpha x ∧ alpha x ≤ 1) ∧
      ∑ x, alpha x ≤ B ∧ ∀ x, e x ≤ alpha x * D := by
  refine ⟨fun h => ⟨fun x => e x / D, fun x => ⟨div_nonneg (he x).1 hD.le,
    (div_le_one hD).2 (he x).2⟩, ?_, fun x => (div_mul_cancel₀ _ hD.ne').ge⟩, ?_⟩
  · rwa [← sum_div, div_le_iff₀ hD]
  · rintro ⟨alpha, -, hsum, hle⟩
    calc ∑ x, e x ≤ ∑ x, alpha x * D := sum_le_sum fun x _ => hle x
      _ ≤ B * D := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hsum hD.le

private lemma higher_condition_i_iff_iii_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c : Real) :
    UniformOfDegree g c (n + 1) ↔ higherUniformConditioniii g c (n + 1) := by
  have hN := NeZero.pos N
  -- split the energy over the first `n` differences; each local energy is at most `N ^ 3`
  rw [UniformOfDegree, ← sum_localDegreeOneEnergy_eq_uniformEnergy, higherUniformConditioniii,
    Nat.add_sub_cancel, show c * (N : Real) ^ (n + 1 + 2) = c * N ^ n * N ^ 3 by ring]
  exact sum_le_iff_exists_weights _ (by positivity) fun a =>
    ⟨sum_nonneg fun _ _ => sq_nonneg _, by
      simpa [UniformOfDegree] using
        discValued_uniform_one (d := 1) (cubeDifference_discValued hg a)⟩

private lemma higher_condition_i_iff_v_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (c : Real) :
    UniformOfDegree g c (n + 1) ↔ higherUniformConditionv g c (n + 1) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- the fourth moment is `N` times the uniformity energy
  rw [UniformOfDegree, higherUniformConditionv, Nat.add_sub_cancel,
    show c * (N : Real) ^ (n + 1 + 3) = N * (c * N ^ (n + 1 + 2)) by ring]
  simp_rw [fourthMoment_eq_degreeOneEnergy, ← mul_sum, sum_localDegreeOneEnergy_eq_uniformEnergy]
  exact (mul_le_mul_iff_right₀ hN).symm

private lemma sum_differenceUniformEnergy_eq_uniformEnergy {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ r : ZMod N, ∑ a : Point N n,
        ‖∑ s : ZMod N, cubeDifference (difference g r) a s‖ ^ 2 =
      ∑ b : Point N (n + 1), ‖∑ s : ZMod N, cubeDifference g b s‖ ^ 2 := by
  calc
    ∑ r : ZMod N, ∑ a : Point N n,
        ‖∑ s : ZMod N, cubeDifference (difference g r) a s‖ ^ 2 =
        ∑ a : Point N n, ∑ r : ZMod N,
          ‖∑ s : ZMod N, difference (cubeDifference g a) r s‖ ^ 2 := by
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      rw [cubeDifference_difference]
    _ = ∑ a : Point N n, ∑ b : Point N 1,
          ‖∑ s : ZMod N, cubeDifference (cubeDifference g a) b s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact (degreeOneEnergy_eq_correlation _).symm
    _ = ∑ b : Point N (n + 1),
          ‖∑ s : ZMod N, cubeDifference g b s‖ ^ 2 :=
      sum_localDegreeOneEnergy_eq_uniformEnergy g

private lemma exists_bounded_extension_sum {N : Nat} [NeZero N]
    (beta : ZMod N → Real) (hbeta : ∀ r, 0 ≤ beta r ∧ beta r ≤ 1)
    (c : Real) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsum : (∑ r, beta r) ≤ c * (N : Real)) :
    ∃ alpha : ZMod N → Real,
      (∀ r, 0 ≤ alpha r ∧ alpha r ≤ 1) ∧
      (∑ r, alpha r) = c * (N : Real) ∧
      ∀ r, beta r ≤ alpha r := by
  have hN1 : ∑ _r : ZMod N, (1 : Real) = N := by simp [ZMod.card]
  have hSN : ∑ r, beta r ≤ N := (sum_le_sum fun r _ => (hbeta r).2).trans_eq hN1
  have hcN : c * N ≤ N := mul_le_of_le_one_left (Nat.cast_nonneg N) hc1
  have hgap : ∀ r, 0 ≤ 1 - beta r := fun r => sub_nonneg.2 (hbeta r).2
  -- raise every weight by the same fraction `t` of its gap to `1` (`t = 0` if `∑ beta = N`)
  let t := (c * N - ∑ r, beta r) / (N - ∑ r, beta r)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
  have ht1 : t ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have htS : t * (N - ∑ r, beta r) = c * N - ∑ r, beta r :=
    div_mul_cancel_of_imp fun h => by linarith
  refine ⟨fun r => beta r + t * (1 - beta r), fun r => ⟨add_nonneg (hbeta r).1
    (mul_nonneg ht0 (hgap r)), le_sub_iff_add_le'.1 (mul_le_of_le_one_left (hgap r) ht1)⟩, ?_,
    fun r => le_add_of_nonneg_right (mul_nonneg ht0 (hgap r))⟩
  rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, hN1]
  linear_combination htS

private lemma higher_condition_i_iff_iv_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c : Real)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    UniformOfDegree g c (n + 1) ↔ higherUniformConditioniv g c (n + 1) := by
  have hD : (0 : Real) < (N : Real) ^ (n + 2) := by have := NeZero.pos N; positivity
  -- split the energy over the first difference; each local energy is at most `N ^ (n + 2)`
  rw [UniformOfDegree, ← sum_differenceUniformEnergy_eq_uniformEnergy, higherUniformConditioniv,
    Nat.add_sub_cancel, show c * (N : Real) ^ (n + 1 + 2) = c * N * N ^ (n + 2) by ring,
    sum_le_iff_exists_weights _ hD]
  · -- weights of total at most `c * N` extend to weights of total exactly `c * N`
    refine ⟨fun ⟨beta, hbeta, hsum, hle⟩ => ?_, fun ⟨alpha, halpha, hsum, hle⟩ =>
      ⟨alpha, halpha, hsum.le, hle⟩⟩
    obtain ⟨alpha, halpha, hsum', hba⟩ := exists_bounded_extension_sum beta hbeta c hc0 hc1 hsum
    exact ⟨alpha, halpha, hsum', fun r =>
      (hle r).trans (mul_le_mul_of_nonneg_right (hba r) hD.le)⟩
  · exact fun r => ⟨sum_nonneg fun _ _ => sq_nonneg _, by
      simpa [UniformOfDegree] using
        discValued_uniform_one (d := n) (difference_discValued hg r)⟩

private lemma higher_condition_iii_imp_vi_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (c1 c2 : Real) (hc2 : 0 ≤ c2)
    (hc : c1 ≤ c2 ^ 2) (hiii : higherUniformConditioniii g c1 (n + 1)) :
    higherUniformConditionvi g c2 (n + 1) := by
  classical
  rw [higherUniformConditioniii, Nat.add_sub_cancel] at hiii
  obtain ⟨alpha, halpha, hsum, hlocal⟩ := hiii
  rw [higherUniformConditionvi, Nat.add_sub_cancel, countWhere, Finset.filter_congr_decidable]
  set B := (Finset.univ : Finset (Point N n)).filter
    fun a => ¬UniformOfDegree (cubeDifference g a) c2 1
  -- a bad `a` has weight `alpha a > c2`, so `c2 * |B| < ∑ alpha ≤ c2 ^ 2 * N ^ n` unless `B = ∅`
  rcases B.eq_empty_or_nonempty with hB | hB
  · rw [hB, Finset.card_empty, Nat.cast_zero]
    positivity
  have hbad : ∀ a ∈ B, c2 < alpha a := fun a ha => lt_of_not_ge fun h =>
    (Finset.mem_filter.1 ha).2 (uniformOfDegree_mono_parameter h (hlocal a))
  have h := (Finset.sum_lt_sum_of_nonempty hB hbad).trans_le
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun a _ _ => (halpha a).1).trans hsum)
  rw [sum_const, nsmul_eq_mul] at h
  refine (lt_of_mul_lt_mul_left ?_ hc2).le
  nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (Nat.cast_nonneg N) n)]

private lemma higher_condition_vi_imp_iii_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c1 c2 : Real)
    (hc20 : 0 ≤ c2) (hc21 : c2 ≤ 1) (hc : 2 * c2 ≤ c1)
    (hvi : higherUniformConditionvi g c2 (n + 1)) :
    higherUniformConditioniii g c1 (n + 1) := by
  classical
  rw [higherUniformConditionvi, Nat.add_sub_cancel, countWhere_eq_sum_ite] at hvi
  push_cast at hvi
  rw [higherUniformConditioniii, Nat.add_sub_cancel]
  -- weight `c2` on the uniform `a` and `1` on the others
  refine ⟨fun a => if UniformOfDegree (cubeDifference g a) c2 1 then c2 else 1, fun a => ?_, ?_,
    fun a => ?_⟩
  · beta_reduce
    split_ifs <;> constructor <;> linarith
  · have hcard : ∑ _a : Point N n, c2 = c2 * (N : Real) ^ n := by simp [ZMod.card, mul_comm]
    calc ∑ a, (if UniformOfDegree (cubeDifference g a) c2 1 then c2 else 1)
        ≤ ∑ a, (c2 + if ¬UniformOfDegree (cubeDifference g a) c2 1 then 1 else 0) :=
          sum_le_sum fun a _ => by split_ifs <;> linarith
      _ ≤ c1 * (N : Real) ^ n := by
          rw [sum_add_distrib, hcard]
          linarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (Nat.cast_nonneg N) n)]
  · beta_reduce
    split_ifs with h
    exacts [h, discValued_uniform_one (cubeDifference_discValued hg a)]

private lemma higher_condition_vi_imp_vii_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c2 c3 : Real)
    (hc20 : 0 ≤ c2) (hc21 : c2 ≤ 1)
    (hroot : c2 ^ ((1 : Real) / 4) < c3)
    (hvi : higherUniformConditionvi g c2 (n + 1)) :
    higherUniformConditionvii g c3 (n + 1) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- a degree-one `c2`-uniform difference has all Fourier coefficients at most `c2 ^ (1/4) * N`
  -- (Lemma 2.2, (i) ⇒ (iii) ⇒ (iv)), so a coefficient `≥ c3 * N` makes it non-uniform
  have hPQ : ∀ a : Point N n, (∃ r, c3 * N ≤ ‖fourier (cubeDifference g a) r‖) →
      ¬UniformOfDegree (cubeDifference g a) c2 1 := by
    rintro a ⟨r, hr⟩ hU
    obtain ⟨-, hi_iii, hiii_iv, -⟩ :=
      lemma_2_2_holds N _ (cubeDifference_discValued hg a) c2 (c2 ^ ((1 : Real) / 4)) 0
    exact (hr.trans (hiii_iv le_rfl (hi_iii.1 ((degreeOne_uniform_iff_condition2i _ _).1 hU))
      r)).not_gt (mul_lt_mul_of_pos_right hroot hN)
  rw [higherUniformConditionvi, Nat.add_sub_cancel] at hvi
  rw [higherUniformConditionvii, Nat.add_sub_cancel]
  exact (Nat.cast_le.2 (countWhere_mono hPQ)).trans (hvi.trans (mul_le_mul_of_nonneg_right
    ((Real.self_le_rpow_of_le_one hc20 hc21 (by norm_num)).trans hroot.le) (by positivity)))

private lemma higher_condition_vii_imp_vi_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c2 c3 : Real)
    (hc30 : 0 ≤ c3) (hc31 : c3 ≤ 1)
    (hc32 : c3 ≤ c2)
    (hvii : higherUniformConditionvii g c3 (n + 1)) :
    higherUniformConditionvi g c2 (n + 1) := by
  -- Fourier coefficients all below `c3 * N` give degree-one `c2`-uniformity, as `c3 ^ 2 ≤ c2`
  -- (Lemma 2.2, (iv) ⇒ (iii) ⇒ (i))
  have hPQ : ∀ a : Point N n, ¬UniformOfDegree (cubeDifference g a) c2 1 →
      ∃ r, c3 * N ≤ ‖fourier (cubeDifference g a) r‖ := fun a ha => by
    by_contra hnot
    simp only [not_exists, not_le] at hnot
    obtain ⟨-, hi_iii, -, hiv_iii, -⟩ :=
      lemma_2_2_holds N _ (cubeDifference_discValued hg a) c2 c3 0
    exact ha ((degreeOne_uniform_iff_condition2i _ _).2 (hi_iii.2 (hiv_iii
      (by nlinarith [mul_nonneg hc30 (sub_nonneg.2 hc31)]) fun r => (hnot r).le)))
  rw [higherUniformConditionvii, Nat.add_sub_cancel] at hvii
  rw [higherUniformConditionvi, Nat.add_sub_cancel]
  exact (Nat.cast_le.2 (countWhere_mono hPQ)).trans
    (hvii.trans (mul_le_mul_of_nonneg_right hc32 (by positivity)))

/-- **Gowers, Lemma 3.1.** The seven higher-uniformity formulations are
equivalent up to the quantitative parameter losses stated in the paper. -/
theorem lemma_3_1_holds : lemma_3_1 := by
  intro N d _ g hd hg c1 c2 c3 hc10 hc11 hc20 hc21 hc30 hc31
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hi_ii : UniformOfDegree g c1 (n + 1) ↔
      higherUniformConditionii g c1 (n + 1) :=
    higher_condition_i_iff_ii g c1
  have hi_iii : UniformOfDegree g c1 (n + 1) ↔
      higherUniformConditioniii g c1 (n + 1) :=
    higher_condition_i_iff_iii_succ g hg c1
  have hi_iv : UniformOfDegree g c1 (n + 1) ↔
      higherUniformConditioniv g c1 (n + 1) :=
    higher_condition_i_iff_iv_succ g hg c1 hc10 hc11
  refine ⟨hi_ii, hi_ii.symm.trans hi_iii, hi_ii.symm.trans hi_iv,
    higher_condition_i_iff_v_succ g c1, ?_, ?_, ?_, ?_⟩
  · exact fun h hiii ↦
      higher_condition_iii_imp_vi_succ g c1 c2 hc20 h hiii
  · exact fun h hvi ↦
      higher_condition_vi_imp_iii_succ g hg c1 c2 hc20 hc21 h hvi
  · exact fun h hvi ↦
      higher_condition_vi_imp_vii_succ g hg c2 c3 hc20 hc21 h hvi
  · exact fun h hvii ↦
      higher_condition_vii_imp_vi_succ g hg c2 c3 hc30 hc31 h hvii

end LeanProofs.GowersSzemeredi
