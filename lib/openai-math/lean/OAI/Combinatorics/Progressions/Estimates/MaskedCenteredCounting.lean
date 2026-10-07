import OAI.Combinatorics.Progressions.Dynamics.MaskedComparisonBudget
import OAI.Combinatorics.Progressions.Linear.FiniteKernelCounting
import OAI.Combinatorics.Progressions.Linear.ProgressionKernelBound

namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

def maskedNormalized {X : Type*} (mu phi : X → ℝ) (x : X) : ℝ :=
  1 + phi x * (mu x - 1)

theorem maskedNormalized_bounds {X : Type*} (mu phi : X → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hmu : ∀ x, 0 ≤ mu x ∧ mu x ≤ B) (hphi : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1) (x : X) :
    0 ≤ maskedNormalized mu phi x ∧ maskedNormalized mu phi x ≤ B := by
  have h1 := mul_nonneg (hphi x).1 (hmu x).1
  have h2 := mul_nonneg (hphi x).1 (sub_nonneg.mpr (hmu x).2)
  have h3 := mul_nonneg (sub_nonneg.mpr (hphi x).2) (sub_nonneg.mpr hB)
  dsimp [maskedNormalized]
  constructor <;> nlinarith [(hphi x).2]

theorem maskedNormalized_score_le {X : Type*} (mu phi : X → ℝ) {xi xi' : ℝ}
    (hxi : 0 ≤ xi) (hxi' : xi ≤ xi') (hphi : ∀ x, phi x ≤ 1) (x : X) :
    maskedNormalized mu phi x - (1 + xi') ≤ mu x * phi x - (1 + xi) * phi x := by
  have h := mul_le_mul_of_nonneg_left (hphi x) hxi
  dsimp [maskedNormalized]
  nlinarith

theorem maskedNormalized_mean {X : Type*} [Fintype X] [Nonempty X]
    (mu phi : X → ℝ) {xi error : ℝ} (hxi : 0 ≤ xi)
    (hmean : (𝔼 x, mu x) = 1) (hphi : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hupper : (𝔼 x, (mu x - (1 + xi)) * phi x) ≤ error)
    (hlower : (𝔼 x, (mu x - (1 + xi)) * (1 - phi x)) ≤ error) :
    |(𝔼 x, maskedNormalized mu phi x) - 1| ≤ xi + error := by
  have hphimean : 0 ≤ (𝔼 x, phi x) ∧ (𝔼 x, phi x) ≤ 1 := by
    constructor
    · exact Finset.expect_nonneg (fun x _ => (hphi x).1)
    · exact (Finset.expect_le_expect (fun x _ => (hphi x).2)).trans_eq (Fintype.expect_const 1)
  have he (x : X) : maskedNormalized mu phi x = 1 + (mu x - (1 + xi)) * phi x + xi * phi x := by
    dsimp [maskedNormalized]
    ring
  have hcomp (x : X) : (mu x - (1 + xi)) * (1 - phi x) =
      mu x - (1 + xi) - (mu x - (1 + xi)) * phi x := by ring
  simp only [hcomp, Finset.expect_sub_distrib, Fintype.expect_const, hmean] at hlower
  simp only [he, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hxi hphimean.1,
    mul_le_mul_of_nonneg_left hphimean.2 hxi]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem CyclicNiltestUpperComparison.masked {degree N : ℕ} [NeZero N]
    {P R error xi xi' : ℝ} {mu phi : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error mu (fun _ => 1 + xi))
    (hphi : PositiveCyclicNiltest.{u} degree N R phi) (hR : 0 ≤ R)
    (hbudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    (hxi : 0 ≤ xi) (hxi' : xi ≤ xi') :
    CyclicNiltestUpperComparison.{u} degree N R error
      (maskedNormalized mu phi) (fun _ => 1 + xi') := by
  have h : CyclicNiltestUpperComparison.{u} degree N R error
      (fun x => mu x * phi x) (fun x => (1 + xi) * phi x) :=
    hphi.mul_upperComparison (low := degree) (@hcompare) le_rfl hR hbudget
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  apply le_trans _ (h D hs T hT hTc)
  apply Finset.expect_le_expect
  intro x _
  exact mul_le_mul_of_nonneg_right
    (maskedNormalized_score_le mu phi hxi hxi' (fun y => (hphi.unit_interval y).2) x)
    (T.unit_interval_evalCyclic hT N (fun _ => x)).2.1

theorem CyclicNiltestUpperComparison.masked_mean {degree N : ℕ} [NeZero N]
    {P R error xi : ℝ} {mu phi : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error mu (fun _ => 1 + xi))
    (hphi : PositiveCyclicNiltest.{u} degree N R phi) (hRP : R + 1 ≤ P)
    (hxi : 0 ≤ xi) (hmean : (𝔼 x, mu x) = 1) :
    |(𝔼 x, maskedNormalized mu phi x) - 1| ≤ xi + error :=
  maskedNormalized_mean mu phi hxi hmean hphi.unit_interval
    (hcompare.test_positive hphi (by linarith))
    (hcompare.test_positive hphi.complement hRP)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_progression_counting (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, |(𝔼 x, mu i x) - 1| ≤ 2 * xi) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, mu i (x + slopes i * d)) - 1| ≤ tau := by
  let delta := tau / (18 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi1, hxi1, hkernel⟩ := exists_progression_kernel_bound s
    (show 0 < delta / 16 by positivity)
  refine ⟨C, hC, min xi1 (delta / 2), lt_min hxi1 (by positivity), ?_⟩
  intro N _ p xi hp hxi hxib hodd hN I _ slopes mu hsep hmu hmean hcompare T hT
  have hxi1b : xi ≤ xi1 := hxib.trans (min_le_left _ _)
  have hxid : 2 * xi ≤ delta := by
    have h := hxib.trans (min_le_right xi1 (delta / 2))
    linarith
  let F : I → (ZMod N × ZMod N) → ℝ := fun i z => mu i (z.1 + slopes i * z.2)
  have hmeanF (i : I) : |(𝔼 z, F i z) - 1| ≤ delta := by
    dsimp only [F]
    rw [expect_prod_split, expect_single_slope]
    exact (hmean i).trans hxid
  have hkernelF (S : Finset I) (hS : S.card ≤ s) (i j : I)
      (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) (b : ℝ) (hb : b = 1 ∨ b = 1 / 4) :
      countingKernelAverage b (fun z => ∏ k ∈ S, F k z) (F i) (F j) ≤ 1 + delta / 16 := by
    have hb0 : 0 ≤ b := by rcases hb with rfl | rfl <;> norm_num
    have hb1 : b ≤ 1 := by rcases hb with rfl | rfl <;> norm_num
    have h := hkernel hp hxi hxi1b hodd hN slopes mu (slopes i) (slopes j) b (mu i) (mu j)
      hb0 hb1 hmu hcompare (hmu i) (@hcompare i) (hmu j) (@hcompare j) S hS
      (hsep j i (Ne.symm hij))
      (fun k hk => ⟨hsep i k (by rintro rfl; exact hi hk),
        hsep j k (by rintro rfl; exact hj hk)⟩)
      (fun k _ l _ hkl => hsep k l hkl)
    unfold countingKernelAverage
    rw [expect_prod_split]
    exact (le_abs_self _).trans (le_of_lt h)
  have h := finite_products_near_one_of_kernel_bound s hdelta F hmeanF hkernelF T hT
  dsimp only [F] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    (18 : ℝ) ^ T.card * delta ≤ (18 : ℝ) ^ (s + 2) * delta :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hT) (le_of_lt hdelta)
    _ = tau := by dsimp [delta]; field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_masked_positive_counting (s a : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (phi : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i, PositiveCyclicNiltest.{0} s N ((p + 2) ^ a) (phi i)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, maskedNormalized mu (phi i) (x + slopes i * d)) - 1| ≤ tau := by
  obtain ⟨B, _, xi, hxi, hcount⟩ := exists_positive_progression_counting s htau
  obtain ⟨C, hC, hbudget⟩ := exists_masked_comparison_budget a B hxi
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes phi hsep hphi T hT
  obtain ⟨haR, hBR, hRP, hproduct, herror⟩ := hbudget p hp
  let R := (p + 2) ^ (max a B)
  have hR : 0 ≤ R := pow_nonneg (by linarith) _
  have hBP : (p + 2) ^ B ≤ (p + 2) ^ C := by linarith
  have hphiR (i : I) : PositiveCyclicNiltest.{0} s N R (phi i) :=
    (hphi i).mono le_rfl haR
  apply hcount (N := N) (p := p) (xi := xi) hp hxi le_rfl hodd
    ((Real.exp_le_exp.mpr hBP).trans hN) slopes (fun i => maskedNormalized mu (phi i)) hsep
    (fun i x => maskedNormalized_bounds mu (phi i) (Real.one_le_exp (by linarith))
      hmu (hphiR i).unit_interval x) ?_ ?_ T hT
  · intro i
    have h := CyclicNiltestUpperComparison.masked_mean hcompare (hphiR i) hRP hxi.le hmean
    exact h.trans (by linarith)
  · intro i
    exact CyclicNiltestUpperComparison.mono_budget
      (CyclicNiltestUpperComparison.masked hcompare (hphiR i) hR hproduct hxi.le le_rfl)
      hBR (Real.exp_le_exp.mpr (neg_le_neg hBP))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem consecutive_slopes_unit {N k : ℕ}
    (hunit : ∀ m : ℕ, 1 ≤ m → m < k → IsUnit (m : ZMod N))
    (i j : Fin k) (hij : i ≠ j) : IsUnit ((i.val : ZMod N) - (j.val : ZMod N)) := by
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij' with hlt | hgt
  · have h := (hunit (j.val - i.val) (by omega) (by omega)).neg
    simpa only [Nat.cast_sub (Nat.le_of_lt hlt), neg_sub] using h
  · simpa only [Nat.cast_sub (Nat.le_of_lt hgt)] using
      hunit (i.val - j.val) (by omega) (by omega)

theorem exists_positive_counting (k : ℕ) (hk : 3 ≤ k) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      (∀ m : ℕ, 1 ≤ m → m < k → IsUnit (m : ZMod N)) →
      Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : Fin k → ZMod N → ℝ,
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, |(𝔼 x, mu i x) - 1| ≤ 2 * xi) →
      (∀ i, CyclicNiltestUpperComparison.{0} (k - 2) N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      ∀ (c : ZMod N) (T : Finset (Fin k)),
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, mu i (x + ((i.val : ZMod N) + c) * d)) - 1| ≤ tau := by
  obtain ⟨C, hC, xi0, hxi0, hcount⟩ := exists_positive_progression_counting (k - 2) htau
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hunit hN mu hmu hmean hcompare c T
  have hodd : Odd N := Nat.coprime_two_left.mp
    ((ZMod.isUnit_iff_coprime 2 N).mp (hunit 2 (by omega) (by omega)))
  have hcard : T.card ≤ k - 2 + 2 := by
    have h := Finset.card_le_univ T
    simp only [Fintype.card_fin] at h
    omega
  have hsep : ∀ i j : Fin k, i ≠ j →
      IsUnit (((i.val : ZMod N) + c) - ((j.val : ZMod N) + c)) := by
    intro i j hij
    simpa only [add_sub_add_right_eq_sub] using consecutive_slopes_unit hunit i j hij
  exact hcount (N := N) (p := p) (xi := xi) hp hxi hxib hodd hN
    (I := Fin k) (fun (i : Fin k) => (i.val : ZMod N) + c) mu
    hsep hmu hmean hcompare T hcard

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_masked_centered_counting (s a : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (phi : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i, PositiveCyclicNiltest.{0} s N ((p + 2) ^ a) (phi i)) →
      ∀ T : Finset I, T.Nonempty → T.card ≤ s + 2 →
        |𝔼 x, 𝔼 d, ∏ i ∈ T, phi i (x + slopes i * d) * (mu (x + slopes i * d) - 1)| ≤
          epsilon := by
  let tau := epsilon / (2 : ℝ) ^ (s + 2)
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_masked_positive_counting s a htau
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes phi hsep hphi T hT hcard
  let F : I → (ZMod N × ZMod N) → ℝ :=
    fun i z => maskedNormalized mu (phi i) (z.1 + slopes i * z.2)
  have hsub (U : Finset I) (hU : U ⊆ T) : |(𝔼 z, ∏ i ∈ U, F i z) - 1| ≤ tau := by
    dsimp only [F]
    rw [expect_prod_split]
    exact hcount hp hodd hN mu hmu hmean hcompare slopes phi hsep hphi U
      ((Finset.card_le_card hU).trans hcard)
  have h := centered_product_mean_abs_le T hT F hsub
  have heq (i : I) (z : ZMod N × ZMod N) :
      F i z - 1 = phi i (z.1 + slopes i * z.2) * (mu (z.1 + slopes i * z.2) - 1) := by
    dsimp [F, maskedNormalized]
    ring
  simp only [heq] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    (2 : ℝ) ^ T.card * tau ≤ (2 : ℝ) ^ (s + 2) * tau :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) htau.le
    _ = epsilon := by dsimp [tau]; field_simp

end Erdos3

end

end OAI
