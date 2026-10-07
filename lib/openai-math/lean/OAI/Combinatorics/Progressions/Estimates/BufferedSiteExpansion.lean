-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Compat.Star
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_star_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * star (g x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : f x * star (g x) - f y * star (g y) =
      f x * star (g x - g y) + (f x - f y) * star (g y) := by
    rw [star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖f x * star (g x - g y)‖ + ‖(f x - f y) * star (g y)‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ Bf * (Kg * dist x y) + (Kf * dist x y) * Bg := by
      apply add_le_add
      · exact mul_le_mul (hBf x) (by simpa only [dist_eq_norm] using hg.dist_le_mul x y)
          (norm_nonneg _) Bf.coe_nonneg
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hf.dist_le_mul x y) (hBg y)
          (norm_nonneg _) (mul_nonneg Kf.coe_nonneg dist_nonneg)
    _ = _ := by push_cast; ring

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

theorem lipschitz_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hstar : LipschitzWith Kg (fun x => star (g x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hg.dist_le_mul x y
  simpa only [star_star] using lipschitz_mul_star_of_bounds f (fun x => star (g x)) hf hstar
    hBf (fun x => by simpa only [norm_star] using hBg x)

theorem bounded_lipschitz_finset_prod {ι X : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i ∈ s, LipschitzWith K (f i)) (hn : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i ∈ s, f i x‖ ≤ (B : ℝ) ^ s.card) ∧
      LipschitzWith (s.card * K * B ^ s.card) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro x
      simp
    · simpa only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, zero_mul] using
        (LipschitzWith.const (α := X) (1 : ℂ))
  | @insert a s ha ih =>
    obtain ⟨hns, hls⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hn i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    constructor
    · intro x
      rw [norm_mul, pow_succ']
      exact mul_le_mul (hn a (Finset.mem_insert_self _ _) x) (hns x) (norm_nonneg _) B.coe_nonneg
    · have hm := lipschitz_mul_of_bounds (f a) (fun x => ∏ i ∈ s, f i x)
        (hf a (Finset.mem_insert_self _ _)) hls (hn a (Finset.mem_insert_self _ _))
        (Bg := B ^ s.card) (fun x => by simpa only [NNReal.coe_pow] using hns x)
      apply hm.weaken
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * B ^ s.card from zero_le)
      nlinarith

theorem bounded_lipschitz_fintype_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i, f i x‖ ≤ (B : ℝ) ^ Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B ^ Fintype.card ι) (fun x => ∏ i, f i x) := by
  simpa only [Finset.card_univ] using
    bounded_lipschitz_finset_prod Finset.univ f hB (fun i _ => hf i) (fun i _ => hn i)

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem ambient_nsmul_lipschitz {J : Type*} [Fintype J] (a : ℕ) :
    LipschitzWith (a : ℝ≥0) (fun z : J → UnitAddCircle => a • z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, dist_eq_norm]
  exact norm_nsmul_le

theorem ambient_pair_lipschitz {J : Type*} [Fintype J]
    (a b : ℕ) (f g : (J → UnitAddCircle) → ℂ) {Lf Lg : ℝ≥0}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfb : ∀ z, ‖f z‖ ≤ 1) (hgb : ∀ z, ‖g z‖ ≤ 1) :
    LipschitzWith (Lf * a + Lg * b) (fun z => f (a • z) * star (g (b • z))) ∧
      ∀ z, ‖f (a • z) * star (g (b • z))‖ ≤ 1 := by
  have hf' := hf.comp (ambient_nsmul_lipschitz (J := J) a)
  have hg' : LipschitzWith (Lg * b) (fun z => star (g (b • z))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_star_star, Function.comp_apply] using (hg.comp (ambient_nsmul_lipschitz (J := J) b)).dist_le_mul x y
  constructor
  · simpa only [one_mul, mul_one, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds (fun z => f (a • z)) (fun z => star (g (b • z)))
        hf' hg' (Bf := 1) (Bg := 1) (fun z => hfb _) (fun z => by simpa only [norm_star, NNReal.coe_one] using hgb (b • z))
  · intro z
    rw [norm_mul, norm_star]
    exact (mul_le_mul (hfb _) (hgb _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

theorem finite_lipschitz_linear_combination {T X : Type*} [Fintype T] [PseudoMetricSpace X]
    (c : T → ℂ) (f : T → X → ℂ) {L B : ℝ≥0}
    (hf : ∀ t, LipschitzWith L (f t)) (hb : ∀ t x, ‖f t x‖ ≤ B) :
    (∀ x, ‖∑ t, c t * f t x‖ ≤ ((∑ t, ‖c t‖₊) * B : ℝ≥0)) ∧
      LipschitzWith ((∑ t, ‖c t‖₊) * L) (fun x => ∑ t, c t * f t x) := by
  constructor
  · intro x
    calc
      _ ≤ ∑ t, ‖c t * f t x‖ := norm_sum_le _ _
      _ ≤ ∑ t, ‖c t‖ * B := Finset.sum_le_sum (fun t _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb t x) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ ∑ t, dist (c t * f t x) (c t * f t y) := dist_sum_sum_le _ _ _
      _ = ∑ t, ‖c t‖ * dist (f t x) (f t y) := by
        simp only [dist_eq_norm, ← mul_sub, norm_mul]
      _ ≤ ∑ t, ‖c t‖ * ((L : ℝ) * dist x y) := Finset.sum_le_sum (fun t _ =>
        mul_le_mul_of_nonneg_left ((hf t).dist_le_mul _ _) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul, mul_assoc]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

theorem finiteSiteExpansion_product {A B S : Type*} [Fintype A] [Fintype B] [Fintype S]
    (a : A → ℂ) (b : B → ℂ) (f : A → S → ℂ) (g : B → S → ℂ) :
    (∑ i, a i * ∏ s, f i s) * (∑ j, b j * ∏ s, g j s) =
      ∑ i, ∑ j, (a i * b j) * ∏ s, f i s * g j s := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteSiteExpansion_product_mass {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℂ) (b : B → ℂ) :
    (∑ i, ∑ j, ‖a i * b j‖) = (∑ i, ‖a i‖) * (∑ j, ‖b j‖) := by
  simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]

theorem finiteSiteExpansion_product_factor {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℂ) (g : Y → ℂ) {L K : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ y, ‖g y‖ ≤ 1) :
    LipschitzWith (L + K) (fun z : X × Y => f z.1 * g z.2) ∧
      ∀ z : X × Y, ‖f z.1 * g z.2‖ ≤ 1 := by
  constructor
  · simpa only [one_mul, mul_one, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds (fun z : X × Y => f z.1) (fun z : X × Y => g z.2)
        (hf.comp LipschitzWith.prod_fst) (hg.comp LipschitzWith.prod_snd)
        (Bf := 1) (Bg := 1) (fun z => hfb z.1) (fun z => hgb z.2)
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hfb _) (hgb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem finiteNestedSiteExpansion_transport {A B C S : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype S]
    (a : A → B → ℂ) (b : C → ℂ) (f : A → B → S → ℂ) (g : C → S → ℂ)
    {z y : ℂ} (hz : z = ∑ i, ∑ j, a i j * ∏ s, f i j s)
    (hy : z * y = z * ∑ k, b k * ∏ s, g k s) :
    z * y = ∑ i, ∑ j, ∑ k, (a i j * b k) * ∏ s, f i j s * g k s := by
  rw [hy, hz, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => finiteSiteExpansion_product _ _ _ _)

theorem siteBudget_of_rowBudget {a b t E : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) (ht : 0 ≤ t)
    (h : (a + 1) * (b * t) ≤ E) : t ≤ E := by
  have hbt : t ≤ b * t := (one_mul t).symm.le.trans (mul_le_mul_of_nonneg_right hb ht)
  exact hbt.trans ((le_mul_of_one_le_left (mul_nonneg (by linarith) ht) (by linarith)).trans h)

theorem finiteNestedSiteExpansion_mass {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (c : ℂ) (a : A → B → ℂ) (b : C → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖(c * a i j) * b k‖) =
      ‖c‖ * (∑ i, ∑ j, ‖a i j‖) * (∑ k, ‖b k‖) := by
  simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]

theorem finiteNestedSiteExpansion_product_functions {A B C S X Y : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype S]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : A → B → S → X → ℂ) (g : C → S → Y → ℂ)
    {L : ℝ≥0} {K : C → ℝ≥0}
    (hf : ∀ i j s, LipschitzWith L (f i j s)) (hg : ∀ k s, LipschitzWith (K k) (g k s))
    (hfb : ∀ i j s x, ‖f i j s x‖ ≤ 1) (hgb : ∀ k s y, ‖g k s y‖ ≤ 1) :
    ∃ h : A → B → C → S → X × Y → ℂ,
      (∀ i j k s, LipschitzWith (L + K k) (h i j k s)) ∧
      (∀ i j k s z, ‖h i j k s z‖ ≤ 1) ∧
      ∀ (a : A → B → ℂ) (b : C → ℂ) (x : S → X) (y : C → S → Y) (z w : ℂ),
        z = ∑ i, ∑ j, a i j * ∏ s, f i j s (x s) →
        z * w = z * ∑ k, b k * ∏ s, g k s (y k s) →
        z * w = ∑ i, ∑ j, ∑ k, (a i j * b k) * ∏ s, h i j k s (x s, y k s) := by
  refine ⟨fun i j k s z => f i j s z.1 * g k s z.2, ?_, ?_, ?_⟩
  · intro i j k s
    exact (finiteSiteExpansion_product_factor _ _ (hf i j s) (hg k s) (hfb i j s) (hgb k s)).1
  · intro i j k s z
    exact (finiteSiteExpansion_product_factor _ _ (hf i j s) (hg k s) (hfb i j s) (hgb k s)).2 z
  · intro a b x y z w hz hw
    exact finiteNestedSiteExpansion_transport a b (fun i j s => f i j s (x s))
      (fun k s => g k s (y k s)) hz hw

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem lipschitz_real_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hfc : LipschitzWith Kf (fun x => (f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hf.dist_le_mul x y
  have hgc : LipschitzWith Kg (fun x => (g x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hg.dist_le_mul x y
  have h := lipschitz_mul_of_bounds _ _ hfc hgc
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hBf x)
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hBg x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [← Complex.ofReal_mul, Complex.isometry_ofReal.dist_eq] using h.dist_le_mul x y

theorem bounded_lipschitz_real_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℝ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, |f i x| ≤ B) :
    (∀ x, |∏ i, f i x| ≤ (B : ℝ)^Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B^Fintype.card ι) (fun x => ∏ i, f i x) := by
  have hfc (i : ι) : LipschitzWith K (fun x => (f i x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact (hf i).dist_le_mul x y
  obtain ⟨hb, hl⟩ := bounded_lipschitz_fintype_prod (fun i x => (f i x : ℂ)) hB hfc
    (fun i x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hn i x)
  constructor
  · intro x
    simpa only [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs] using hb x
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [← Complex.ofReal_prod, Complex.isometry_ofReal.dist_eq] using hl.dist_le_mul x y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem siteFactorTensor_identity {D S U : Type*} [Fintype D] [DecidableEq D] [Fintype S]
    {T : D → Type*} [∀ d, Fintype (T d)]
    (c : ∀ d, T d → ℂ) (f : ∀ d, T d → S → U → ℂ) (v : S → D → U) :
    (∏ d, ∑ t, c d t * ∏ s, f d t s (v s d)) =
      ∑ t : ∀ d, T d, (∏ d, c d (t d)) * ∏ s, ∏ d, f d (t d) s (v s d) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_comm]

theorem siteFactorTensor_coefficient_sum {D : Type*} [Fintype D] [DecidableEq D]
    {T : D → Type*} [∀ d, Fintype (T d)] (c : ∀ d, T d → ℂ) :
    (∑ t : ∀ d, T d, ‖∏ d, c d (t d)‖) = ∏ d, ∑ t, ‖c d t‖ := by
  simp_rw [norm_prod]
  exact (Fintype.prod_sum (fun d t => ‖c d t‖)).symm

theorem siteFactorTensor_coefficient_bound {D : Type*} [Fintype D] [DecidableEq D]
    {T : D → Type*} [∀ d, Fintype (T d)] (c : ∀ d, T d → ℂ) (C : D → ℝ)
    (hc : ∀ d, (∑ t, ‖c d t‖) ≤ C d) :
    (∑ t : ∀ d, T d, ‖∏ d, c d (t d)‖) ≤ ∏ d, C d := by
  rw [siteFactorTensor_coefficient_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun d _ => hc d)

theorem siteFactorTensor_factor_bound {D U : Type*} [Fintype D] (f : D → U → ℂ)
    (hf : ∀ d x, ‖f d x‖ ≤ 1) (x : D → U) : ‖∏ d, f d (x d)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun d _ => hf d (x d))

theorem siteFactorTensor_factor_lipschitz {D U : Type*} [Fintype D] [PseudoMetricSpace U]
    (f : D → U → ℂ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (hn : ∀ d x, ‖f d x‖ ≤ 1) :
    LipschitzWith (Fintype.card D * K) (fun x : D → U => ∏ d, f d (x d)) := by
  have hcoord (d : D) : LipschitzWith K (fun x : D → U => f d (x d)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hf d).dist_le_mul _ _ |>.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y d) K.coe_nonneg)
  simpa only [one_pow, mul_one] using
    (bounded_lipschitz_fintype_prod (fun d (x : D → U) => f d (x d))
      (B := 1) le_rfl hcoord (fun d x => hn d (x d))).2

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem finiteSiteExpansion_test_expect {Ω I S : Type*}
    [Fintype Ω] [Fintype I] [Fintype S]
    (c : I → ℂ) (g : I → S → Ω → ℂ) (model : Ω → ℂ)
    (hmodel : ∀ ω, model ω = ∑ i, c i * ∏ s, g i s ω)
    (test : S → Ω → ℂ) :
    (𝔼 ω, model ω * ∏ s, test s ω) =
      ∑ i, c i * (𝔼 ω, ∏ s, test s ω * g i s ω) := by
  have hpoint (ω) : model ω * ∏ s, test s ω =
      ∑ i, c i * ∏ s, test s ω * g i s ω := by
    rw [hmodel, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hpoint, Finset.expect_sum_comm, ← Finset.mul_expect]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

def bufferedSiteFactor (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (f : T → S → (D → ℝ) → ℂ) (k : T) (s : S) (u : U) : ℂ :=
  χ s u*f k s (y s u)

theorem bufferedSiteExpansion_identity (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (c : T → ℂ) (f : T → S → (D → ℝ) → ℂ) (u : S → U) :
    (∑ k, c k*∏ s, bufferedSiteFactor y χ f k s (u s)) =
      (∏ s, χ s (u s))*(∑ k, c k*∏ s, f k s (y s (u s))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bufferedSiteFactor, Finset.prod_mul_distrib]
  ring

omit [Fintype S] [Fintype T] in
theorem bufferedSiteFactor_bound (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (f : T → S → (D → ℝ) → ℂ) (hχ : ∀ s u, ‖χ s u‖ ≤ 1)
    (hf : ∀ k s x, ‖f k s x‖ ≤ 1) (k : T) (s : S) (u : U) :
    ‖bufferedSiteFactor y χ f k s u‖ ≤ 1 := by
  unfold bufferedSiteFactor
  rw [norm_mul]
  exact (mul_le_mul (hχ s u) (hf k s _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [Fintype S] [Fintype T] in
theorem bufferedSiteFactor_lipschitz [Fintype D] [PseudoMetricSpace U]
    (y : S → U → D → ℝ) (χ : S → U → ℂ) (f : T → S → (D → ℝ) → ℂ)
    {K L C : ℝ≥0} (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hf : ∀ k s, LipschitzWith K (f k s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hf1 : ∀ k s x, ‖f k s x‖ ≤ 1) (k : T) (s : S) :
    LipschitzWith (K*L+C) (bufferedSiteFactor y χ f k s) := by
  unfold bufferedSiteFactor
  simpa only [one_mul, Function.comp_def] using
    lipschitz_mul_of_bounds (χ s) (f k s ∘ y s) (hχ s) ((hf k s).comp (hy s))
      (Bf := 1) (Bg := 1) (hχ1 s) (fun u => hf1 k s (y s u))

theorem bufferedSiteExpansion_error (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (F : (S → D → ℝ) → ℂ) (c : T → ℂ) (f : T → S → (D → ℝ) → ℂ)
    {R ε : ℝ} (hε : 0 ≤ ε) (hχ : ∀ s u, ‖χ s u‖ ≤ 1)
    (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R)
    (herr : ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ R) →
      ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε) (u : S → U) :
    ‖(∏ s, χ s (u s))*F (fun s => y s (u s))-
      ∑ k, c k*∏ s, bufferedSiteFactor y χ f k s (u s)‖ ≤ ε := by
  classical
  rw [bufferedSiteExpansion_identity, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s (u s) = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hbox : ∀ s d, |y s (u s) d| ≤ R := fun s => hsupport s (u s) (fun hs => hz ⟨s, hs⟩)
    have hp : ‖∏ s, χ s (u s)‖ ≤ 1 := siteFactorTensor_factor_bound χ hχ u
    exact (mul_le_mul hp (herr _ hbox) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

end Erdos3

end

end OAI
