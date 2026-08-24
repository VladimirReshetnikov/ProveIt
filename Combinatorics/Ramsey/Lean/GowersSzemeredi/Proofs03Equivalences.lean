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
  have hN : (0 : Real) ≤ N := by positivity
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
    (a : Point N 1) : cubeDifference g a = difference g (a 0) := by
  funext s
  simp only [cubeDifference, List.ofFn_succ, List.ofFn_zero, iteratedDifference]

private lemma degreeOneEnergy_eq_correlation {N : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 =
      ∑ r : ZMod N, ‖∑ s : ZMod N, difference g r s‖ ^ 2 := by
  let e := Equiv.funUnique (Fin 1) (ZMod N)
  have h := e.sum_comp fun r : ZMod N =>
    ‖∑ s : ZMod N, difference g r s‖ ^ 2
  simpa [e, cubeDifference_one] using h

private lemma fourthMoment_eq_degreeOneEnergy {N : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ r : ZMod N, ‖fourier g r‖ ^ 4 =
      (N : Real) * ∑ a : Point N 1,
        ‖∑ s : ZMod N, cubeDifference g a s‖ ^ 2 := by
  have h := lemma_2_1_holds N g g
  rw [degreeOneEnergy_eq_correlation]
  simpa only [difference, ← pow_add] using h

private lemma degreeOne_uniform_iff_condition2i {N : Nat} [NeZero N]
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
  calc
    ∑ a : Point N n, ∑ b : Point N 1,
        ‖∑ s : ZMod N, cubeDifference (cubeDifference g a) b s‖ ^ 2 =
        ∑ a : Point N n, ∑ r : ZMod N,
          ‖∑ s : ZMod N, difference (cubeDifference g a) r s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact degreeOneEnergy_eq_correlation _
    _ = ∑ r : ZMod N, ∑ a : Point N n,
          ‖∑ s : ZMod N, cubeDifference g (Fin.cons r a) s‖ ^ 2 := by
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro a _
      rw [cubeDifference_cons]
    _ = ∑ c : Point N (n + 1),
          ‖∑ s : ZMod N, cubeDifference g c s‖ ^ 2 :=
      (sum_point_succ (N := N) (n := n) (M := Real)
        (fun c => ‖∑ s : ZMod N, cubeDifference g c s‖ ^ 2)).symm

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

private lemma higher_condition_i_iff_iii_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c : Real) :
    UniformOfDegree g c (n + 1) ↔ higherUniformConditioniii g c (n + 1) := by
  let e : Point N n → Real := fun a =>
    ∑ b : Point N 1,
      ‖∑ s : ZMod N, cubeDifference (cubeDifference g a) b s‖ ^ 2
  have henergy : ∑ a : Point N n, e a =
      ∑ b : Point N (n + 1), ‖∑ s : ZMod N, cubeDifference g b s‖ ^ 2 :=
    sum_localDegreeOneEnergy_eq_uniformEnergy g
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  constructor
  · intro hUniform
    let alpha : Point N n → Real := fun a => e a / (N : Real) ^ 3
    refine ⟨alpha, ?_, ?_, ?_⟩
    · intro a
      have he_nonneg : 0 ≤ e a := Finset.sum_nonneg fun b _ => sq_nonneg _
      have hlocal := discValued_uniform_one (d := 1)
        (cubeDifference_discValued hg a)
      change e a ≤ 1 * (N : Real) ^ 3 at hlocal
      exact ⟨div_nonneg he_nonneg (pow_nonneg hN.le _),
        (div_le_one (pow_pos hN 3)).mpr (by simpa using hlocal)⟩
    · change (∑ a : Point N n, alpha a) ≤ c * (N : Real) ^ n
      calc
        ∑ a : Point N n, alpha a =
            (∑ a : Point N n, e a) / (N : Real) ^ 3 := by
          simp only [alpha, sum_div]
        _ = (∑ b : Point N (n + 1),
              ‖∑ s : ZMod N, cubeDifference g b s‖ ^ 2) /
                (N : Real) ^ 3 := by rw [henergy]
        _ ≤ (c * (N : Real) ^ (n + 3)) / (N : Real) ^ 3 :=
          div_le_div_of_nonneg_right hUniform (pow_nonneg hN.le _)
        _ = c * (N : Real) ^ n := by
          rw [pow_add]
          field_simp
    · intro a
      unfold UniformOfDegree
      change e a ≤ alpha a * (N : Real) ^ 3
      simp only [alpha]
      rw [div_mul_cancel₀]
      exact pow_ne_zero _ hN.ne'
  · rintro ⟨alpha, _halpha, hsum, hlocal⟩
    unfold UniformOfDegree at hlocal ⊢
    rw [← henergy]
    calc
      ∑ a : Point N n, e a ≤
          ∑ a : Point N n, alpha a * (N : Real) ^ 3 := by
        apply Finset.sum_le_sum
        intro a _
        exact hlocal a
      _ = (∑ a : Point N n, alpha a) * (N : Real) ^ 3 := by
        rw [sum_mul]
      _ ≤ (c * (N : Real) ^ n) * (N : Real) ^ 3 :=
        mul_le_mul_of_nonneg_right hsum (pow_nonneg hN.le _)
      _ = c * (N : Real) ^ (n + 3) := by rw [pow_add]; ring

private lemma higher_condition_i_iff_v_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (c : Real) :
    UniformOfDegree g c (n + 1) ↔ higherUniformConditionv g c (n + 1) := by
  let U := ∑ b : Point N (n + 1),
    ‖∑ s : ZMod N, cubeDifference g b s‖ ^ 2
  let F := ∑ a : Point N n, ∑ r : ZMod N,
    ‖fourier (cubeDifference g a) r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmoment : F = (N : Real) * U := by
    calc
      F = ∑ a : Point N n, (N : Real) *
          ∑ b : Point N 1,
            ‖∑ s : ZMod N, cubeDifference (cubeDifference g a) b s‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        exact fourthMoment_eq_degreeOneEnergy _
      _ = (N : Real) * ∑ a : Point N n, ∑ b : Point N 1,
          ‖∑ s : ZMod N, cubeDifference (cubeDifference g a) b s‖ ^ 2 := by
        rw [mul_sum]
      _ = (N : Real) * U := by
        rw [sum_localDegreeOneEnergy_eq_uniformEnergy]
  change U ≤ c * (N : Real) ^ (n + 3) ↔ F ≤ c * (N : Real) ^ (n + 4)
  constructor
  · intro h
    calc
      F = (N : Real) * U := hmoment
      _ ≤ (N : Real) * (c * (N : Real) ^ (n + 3)) :=
        mul_le_mul_of_nonneg_left h hN.le
      _ = c * (N : Real) ^ (n + 4) := by
        rw [show n + 4 = 1 + (n + 3) by omega, pow_add]
        ring
  · intro h
    refine le_of_mul_le_mul_left ?_ hN
    calc
      (N : Real) * U = F := hmoment.symm
      _ ≤ c * (N : Real) ^ (n + 4) := h
      _ = (N : Real) * (c * (N : Real) ^ (n + 3)) := by
        rw [show n + 4 = 1 + (n + 3) by omega, pow_add]
        ring

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
  let S := ∑ r, beta r
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => (hbeta r).1
  have hSN : S ≤ (N : Real) := by
    calc
      S ≤ ∑ _r : ZMod N, (1 : Real) :=
        Finset.sum_le_sum fun r _ => (hbeta r).2
      _ = (N : Real) := by simp [ZMod.card]
  by_cases heq : S = (N : Real)
  · refine ⟨beta, hbeta, ?_, fun r => le_rfl⟩
    apply le_antisymm
    · exact hsum
    · calc
        c * (N : Real) ≤ 1 * (N : Real) :=
          mul_le_mul_of_nonneg_right hc1 hN.le
        _ = S := by rw [heq]; ring
  · have hSlt : S < (N : Real) := lt_of_le_of_ne hSN heq
    have hden : 0 < (N : Real) - S := sub_pos.mpr hSlt
    let t := (c * (N : Real) - S) / ((N : Real) - S)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hsum) hden.le
    have ht1 : t ≤ 1 := by
      apply (div_le_one hden).mpr
      nlinarith [mul_le_mul_of_nonneg_right hc1 hN.le]
    let alpha : ZMod N → Real := fun r => beta r + t * (1 - beta r)
    refine ⟨alpha, ?_, ?_, ?_⟩
    · intro r
      have hgap : 0 ≤ 1 - beta r := sub_nonneg.mpr (hbeta r).2
      have hinc : 0 ≤ t * (1 - beta r) := mul_nonneg ht0 hgap
      have hremain : 0 ≤ (1 - t) * (1 - beta r) :=
        mul_nonneg (sub_nonneg.mpr ht1) hgap
      constructor
      · exact add_nonneg (hbeta r).1 hinc
      · dsimp [alpha]
        nlinarith
    · calc
        ∑ r, alpha r = S + t * ((N : Real) - S) := by
          simp only [alpha, sum_add_distrib]
          rw [← mul_sum]
          simp only [sum_sub_distrib, sum_const, card_univ, ZMod.card,
            nsmul_eq_mul]
          ring
        _ = c * (N : Real) := by
          dsimp [t]
          field_simp [ne_of_gt hden]
          ring
    · intro r
      dsimp [alpha]
      exact le_add_of_nonneg_right
        (mul_nonneg ht0 (sub_nonneg.mpr (hbeta r).2))

private lemma higher_condition_i_iff_iv_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c : Real)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    UniformOfDegree g c (n + 1) ↔ higherUniformConditioniv g c (n + 1) := by
  let e : ZMod N → Real := fun r =>
    ∑ a : Point N n,
      ‖∑ s : ZMod N, cubeDifference (difference g r) a s‖ ^ 2
  let U := ∑ b : Point N (n + 1),
    ‖∑ s : ZMod N, cubeDifference g b s‖ ^ 2
  have henergy : ∑ r, e r = U :=
    sum_differenceUniformEnergy_eq_uniformEnergy g
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  constructor
  · intro hUniform
    let beta : ZMod N → Real := fun r => e r / (N : Real) ^ (n + 2)
    have hbeta : ∀ r, 0 ≤ beta r ∧ beta r ≤ 1 := by
      intro r
      have he0 : 0 ≤ e r := Finset.sum_nonneg fun a _ => sq_nonneg _
      have hone := discValued_uniform_one (d := n) (difference_discValued hg r)
      change e r ≤ 1 * (N : Real) ^ (n + 2) at hone
      exact ⟨div_nonneg he0 (pow_nonneg hN.le _),
        (div_le_one (pow_pos hN _)).mpr (by simpa using hone)⟩
    have hbetaSum : (∑ r, beta r) ≤ c * (N : Real) := by
      calc
        ∑ r, beta r = (∑ r, e r) / (N : Real) ^ (n + 2) := by
          simp only [beta, sum_div]
        _ = U / (N : Real) ^ (n + 2) := by rw [henergy]
        _ ≤ (c * (N : Real) ^ (n + 3)) / (N : Real) ^ (n + 2) :=
          div_le_div_of_nonneg_right hUniform (pow_nonneg hN.le _)
        _ = c * (N : Real) := by
          rw [show n + 3 = (n + 2) + 1 by omega, pow_add]
          field_simp
    obtain ⟨alpha, halpha, halphaSum, hbetaAlpha⟩ :=
      exists_bounded_extension_sum beta hbeta c hc0 hc1 hbetaSum
    refine ⟨alpha, halpha, halphaSum, ?_⟩
    intro r
    apply uniformOfDegree_mono_parameter (hbetaAlpha r)
    unfold UniformOfDegree
    change e r ≤ beta r * (N : Real) ^ (n + 2)
    simp only [beta]
    rw [div_mul_cancel₀]
    exact pow_ne_zero _ hN.ne'
  · rintro ⟨alpha, _halpha, halphaSum, hlocal⟩
    unfold UniformOfDegree at hlocal ⊢
    change U ≤ c * (N : Real) ^ (n + 3)
    rw [← henergy]
    calc
      ∑ r, e r ≤ ∑ r, alpha r * (N : Real) ^ (n + 2) := by
        apply Finset.sum_le_sum
        intro r _
        exact hlocal r
      _ = (∑ r, alpha r) * (N : Real) ^ (n + 2) := by rw [sum_mul]
      _ = (c * (N : Real)) * (N : Real) ^ (n + 2) := by rw [halphaSum]
      _ = c * (N : Real) ^ (n + 3) := by
        rw [show n + 3 = 1 + (n + 2) by omega, pow_add]
        ring

private lemma higher_condition_iii_imp_vi_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (c1 c2 : Real) (hc2 : 0 ≤ c2)
    (hc : c1 ≤ c2 ^ 2) (hiii : higherUniformConditioniii g c1 (n + 1)) :
    higherUniformConditionvi g c2 (n + 1) := by
  classical
  obtain ⟨alpha, halpha, hsum, hlocal⟩ := hiii
  unfold higherUniformConditionvi countWhere
  simp only [Nat.add_sub_cancel]
  rw [Finset.filter_congr_decidable]
  set B := (Finset.univ : Finset (Point N n)).filter (fun a =>
    ¬ UniformOfDegree (cubeDifference g a) c2 1) with hB
  change (B.card : Real) ≤ c2 * (N : Real) ^ n
  by_cases hc20 : c2 = 0
  · have hsum0 : (∑ a, alpha a) = 0 := by
      apply le_antisymm
      · calc
          ∑ a, alpha a ≤ c1 * (N : Real) ^ n := hsum
          _ ≤ 0 * (N : Real) ^ n :=
            mul_le_mul_of_nonneg_right (by simpa [hc20] using hc) (by positivity)
          _ = 0 := by ring
      · exact Finset.sum_nonneg fun a _ => (halpha a).1
    have halpha0 (a : Point N n) : alpha a = 0 := by
      apply le_antisymm
      · calc
          alpha a ≤ ∑ x : Point N n, alpha x := by
            simpa using (Finset.single_le_sum
              (s := (Finset.univ : Finset (Point N n)))
              (f := alpha) (fun x _ => (halpha x).1) (Finset.mem_univ a))
          _ = 0 := hsum0
      · exact (halpha a).1
    have hB : B = ∅ := by
      ext a
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hnot
      exact hnot (by simpa [hc20, halpha0 a] using hlocal a)
    simp [hB, hc20]
  · have hc2pos : 0 < c2 := lt_of_le_of_ne hc2 (Ne.symm hc20)
    have hbad (a : Point N n) (ha : a ∈ B) : c2 ≤ alpha a := by
      by_contra hnot
      have hle : alpha a ≤ c2 := le_of_not_ge hnot
      exact (Finset.mem_filter.mp ha).2
        (uniformOfDegree_mono_parameter hle (hlocal a))
    have hweighted : c2 * (B.card : Real) ≤ c1 * (N : Real) ^ n := by
      calc
        c2 * (B.card : Real) = ∑ _a ∈ B, c2 := by simp [mul_comm]
        _ ≤ ∑ a ∈ B, alpha a := Finset.sum_le_sum hbad
        _ ≤ ∑ a : Point N n, alpha a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun a _ _ => (halpha a).1)
        _ ≤ c1 * (N : Real) ^ n := hsum
    refine le_of_mul_le_mul_left ?_ hc2pos
    calc
      c2 * (B.card : Real) ≤ c1 * (N : Real) ^ n := hweighted
      _ ≤ c2 ^ 2 * (N : Real) ^ n :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = c2 * (c2 * (N : Real) ^ n) := by ring

private lemma higher_condition_vi_imp_iii_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c1 c2 : Real)
    (hc20 : 0 ≤ c2) (hc21 : c2 ≤ 1) (hc : 2 * c2 ≤ c1)
    (hvi : higherUniformConditionvi g c2 (n + 1)) :
    higherUniformConditioniii g c1 (n + 1) := by
  classical
  unfold higherUniformConditionvi countWhere at hvi
  simp only [Nat.add_sub_cancel] at hvi
  rw [Finset.filter_congr_decidable] at hvi
  set B := (Finset.univ : Finset (Point N n)).filter (fun a ↦
    ¬ UniformOfDegree (cubeDifference g a) c2 1) with hB
  change (B.card : Real) ≤ c2 * (N : Real) ^ n at hvi
  unfold higherUniformConditioniii
  rw [show n + 1 - 1 = n by omega]
  let alpha : Point N n → Real := fun a ↦
    if UniformOfDegree (cubeDifference g a) c2 1 then c2 else 1
  refine ⟨alpha, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : UniformOfDegree (cubeDifference g a) c2 1
    · simp [alpha, ha, hc20, hc21]
    · simp [alpha, ha]
  · have halphaBound (a : Point N n) :
        alpha a ≤ c2 + if a ∈ B then 1 else 0 := by
      by_cases ha : UniformOfDegree (cubeDifference g a) c2 1
      · simp [alpha, ha, B]
      · simp only [alpha, ha, if_false, B, Finset.mem_filter,
          Finset.mem_univ, true_and, not_false_eq_true, if_true]
        linarith
    have hpointCard : Fintype.card (Point N n) = N ^ n := by
      simp [Point, ZMod.card]
    have hconst : ∑ _a : Point N n, c2 = c2 * (N : Real) ^ n := by
      simp only [sum_const, card_univ, nsmul_eq_mul, hpointCard, Nat.cast_pow]
      ring
    have hindicator :
        ∑ a : Point N n, (if a ∈ B then (1 : Real) else 0) =
          (B.card : Real) := by
      have hnat : B.card =
          ∑ a : Point N n, if a ∈ B then (1 : Nat) else 0 :=
        Finset.card_eq_sum_ite (Finset.subset_univ B)
      exact_mod_cast hnat.symm
    calc
      ∑ a : Point N n, alpha a ≤
          ∑ a : Point N n, (c2 + if a ∈ B then 1 else 0) :=
        Finset.sum_le_sum fun a _ ↦ halphaBound a
      _ = c2 * (N : Real) ^ n + (B.card : Real) := by
        rw [sum_add_distrib, hconst, hindicator]
      _ ≤ c2 * (N : Real) ^ n + c2 * (N : Real) ^ n :=
        add_le_add le_rfl hvi
      _ = 2 * c2 * (N : Real) ^ n := by ring
      _ ≤ c1 * (N : Real) ^ n :=
        mul_le_mul_of_nonneg_right hc (by positivity)
  · intro a
    by_cases ha : UniformOfDegree (cubeDifference g a) c2 1
    · simpa [alpha, ha] using ha
    · simpa [alpha, ha] using
        (discValued_uniform_one (d := 1) (cubeDifference_discValued hg a))

private lemma higher_condition_vi_imp_vii_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c2 c3 : Real)
    (hc20 : 0 ≤ c2) (hc21 : c2 ≤ 1)
    (hroot : c2 ^ ((1 : Real) / 4) < c3)
    (hvi : higherUniformConditionvi g c2 (n + 1)) :
    higherUniformConditionvii g c3 (n + 1) := by
  classical
  have hc2root : c2 ≤ c2 ^ ((1 : Real) / 4) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' hc20 hc21
      (by norm_num : (0 : Real) ≤ 1 / 4) (by norm_num : (1 : Real) / 4 ≤ 1)
    simpa only [Real.rpow_one] using h
  have hc23 : c2 ≤ c3 := hc2root.trans hroot.le
  let P : Point N n → Prop := fun a ↦
    ∃ r : ZMod N, c3 * N ≤ ‖fourier (cubeDifference g a) r‖
  let Q : Point N n → Prop := fun a ↦
    ¬ UniformOfDegree (cubeDifference g a) c2 1
  have hPQ : ∀ a, P a → Q a := by
    intro a ha hUniform
    obtain ⟨r, hr⟩ := ha
    have hdisc := cubeDifference_discValued hg a
    have hi : uniformCondition2i (cubeDifference g a) c2 :=
      (degreeOne_uniform_iff_condition2i _ _).mp hUniform
    rcases lemma_2_2_holds N (cubeDifference g a) hdisc c2
        (c2 ^ ((1 : Real) / 4)) 0 with ⟨_, hi_iii, hiii_iv, _, _, _⟩
    have hiv : uniformCondition2iv (cubeDifference g a)
        (c2 ^ ((1 : Real) / 4)) := hiii_iv le_rfl (hi_iii.mp hi)
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hstrict : c2 ^ ((1 : Real) / 4) * (N : Real) < c3 * N :=
      mul_lt_mul_of_pos_right hroot hN
    exact (not_lt_of_ge hr) ((hiv r).trans_lt hstrict)
  unfold higherUniformConditionvi at hvi
  unfold higherUniformConditionvii
  simp only [Nat.add_sub_cancel]
  calc
    (countWhere P : Real) ≤ (countWhere Q : Nat) := by
      exact_mod_cast countWhere_mono hPQ
    _ ≤ c2 * (N : Real) ^ n := hvi
    _ ≤ c3 * (N : Real) ^ n :=
      mul_le_mul_of_nonneg_right hc23 (by positivity)

private lemma higher_condition_vii_imp_vi_succ {N n : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (c2 c3 : Real)
    (hc30 : 0 ≤ c3) (hc31 : c3 ≤ 1)
    (hc32 : c3 ≤ c2)
    (hvii : higherUniformConditionvii g c3 (n + 1)) :
    higherUniformConditionvi g c2 (n + 1) := by
  classical
  have hc3self : c3 ^ 2 ≤ c3 := by
    nlinarith [mul_nonneg hc30 (sub_nonneg.mpr hc31)]
  have hc3sq : c3 ^ 2 ≤ c2 := hc3self.trans hc32
  let P : Point N n → Prop := fun a ↦
    ¬ UniformOfDegree (cubeDifference g a) c2 1
  let Q : Point N n → Prop := fun a ↦
    ∃ r : ZMod N, c3 * N ≤ ‖fourier (cubeDifference g a) r‖
  have hPQ : ∀ a, P a → Q a := by
    intro a ha
    by_contra hnot
    have hsmall : ∀ r : ZMod N,
        ‖fourier (cubeDifference g a) r‖ < c3 * N := by
      intro r
      exact lt_of_not_ge (fun hr ↦ hnot ⟨r, hr⟩)
    have hdisc := cubeDifference_discValued hg a
    rcases lemma_2_2_holds N (cubeDifference g a) hdisc c2 c3 0 with
      ⟨_, hi_iii, _, hiv_iii, _, _⟩
    have hiv : uniformCondition2iv (cubeDifference g a) c3 :=
      fun r ↦ (hsmall r).le
    have hi : uniformCondition2i (cubeDifference g a) c2 :=
      hi_iii.mpr (hiv_iii hc3sq hiv)
    exact ha ((degreeOne_uniform_iff_condition2i _ _).mpr hi)
  unfold higherUniformConditionvii at hvii
  unfold higherUniformConditionvi
  simp only [Nat.add_sub_cancel]
  calc
    (countWhere P : Real) ≤ (countWhere Q : Nat) := by
      exact_mod_cast countWhere_mono hPQ
    _ ≤ c3 * (N : Real) ^ n := hvii
    _ ≤ c2 * (N : Real) ^ n :=
      mul_le_mul_of_nonneg_right hc32 (by positivity)

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
