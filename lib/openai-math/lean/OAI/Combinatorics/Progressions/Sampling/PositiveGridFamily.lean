/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Group.Units.Equiv
import OAI.Combinatorics.Progressions.Estimates.CyclicComparisonMean
import OAI.Combinatorics.Progressions.Estimates.FiniteExceptionalMean
import OAI.Combinatorics.Progressions.Estimates.SimultaneousAxisCompression
import OAI.Combinatorics.Progressions.FixedDensity.Energy

namespace OAI

section

namespace Erdos3

theorem positiveGrid_normalization_bound {g b : ℝ} (hg : 0 ≤ g) (hb : 1 ≤ b)
    (s V W : ℕ) (hWV : W ≤ V) :
    (b * g) ^ V * (b ^ (s + 1)) ^ W ≤ (g * b ^ (s + 2)) ^ V := by
  calc
    _ ≤ (b * g) ^ V * (b ^ (s + 1)) ^ V :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_pow₀ hb) hWV)
        (pow_nonneg (mul_nonneg (by linarith) hg) _)
    _ = _ := by
      rw [← mul_pow]
      congr 1
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring

theorem positiveGrid_compression_errors {q L B R T c : ℝ} (V W : ℕ)
    (hq : 1 ≤ q) (hV : (V : ℝ) * q ≤ B) (hWV : W ≤ V)
    (hc : 0 ≤ c) (hcb : c ≤ Real.exp (2 * q))
    (hR : L + 2 * B + 2 ≤ R) (hRT : R ≤ T) :
    c ^ V * Real.exp (-R) + Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T) ≤
      Real.exp (-L) := by
  have hcpow : c ^ V ≤ Real.exp (2 * B) := by
    calc
      _ ≤ (Real.exp (2 * q)) ^ V := pow_le_pow_left₀ hc hcb V
      _ = Real.exp (2 * ((V : ℝ) * q)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hWB : (W : ℝ) ≤ B := by
    have hcast : (W : ℝ) ≤ V := by exact_mod_cast hWV
    have hvq : (V : ℝ) ≤ (V : ℝ) * q := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg V)
    exact hcast.trans (hvq.trans hV)
  have hWexp : (W : ℝ) ≤ Real.exp B := hWB.trans (by linarith [Real.add_one_le_exp B])
  have hfirst : c ^ V * Real.exp (-R) ≤ Real.exp (2 * B - R) := by
    calc
      _ ≤ Real.exp (2 * B) * Real.exp (-R) :=
        mul_le_mul_of_nonneg_right hcpow (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  have hsecond : Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T) ≤
      Real.exp (2 * B - R) := by
    calc
      _ ≤ (Real.exp B * Real.exp B) * Real.exp (-T) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (Real.exp_le_exp.mpr hV) hWexp (Nat.cast_nonneg W) (Real.exp_nonneg B)
      _ = Real.exp (2 * B - T) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 2 * Real.exp (2 * B - R) := by linarith
    _ ≤ Real.exp 2 * Real.exp (2 * B - R) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (2 + 2 * B - R) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exists_positiveGrid_base_budget {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 2 ≤ p → Real.exp (-((p + 2) ^ C)) ≤ epsilon := by
  obtain ⟨a, ha⟩ := exists_nat_ge (-Real.log epsilon)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (Polynomial.C a)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have haP : (a : ℝ) ≤ (p + 2) ^ C := by simpa using hbudget p (by linarith)
  calc
    _ ≤ Real.exp (-(a : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg haP)
    _ ≤ Real.exp (Real.log epsilon) := Real.exp_le_exp.mpr (by linarith)
    _ = epsilon := Real.exp_log hepsilon

end Erdos3

end

section

namespace Erdos3

open Filter Topology

theorem exists_positiveGrid_slack (s : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
      (1 + epsilon) ^ (s + 2) ≤ 1 + delta / 2 := by
  have hcontinuous : ContinuousAt (fun x : ℝ => (1 + x) ^ (s + 2)) 0 := by fun_prop
  have htend : Tendsto (fun x : ℝ => (1 + x) ^ (s + 2)) (𝓝 0) (𝓝 1) := by
    simpa using hcontinuous.tendsto
  have heventually : ∀ᶠ x : ℝ in 𝓝 0, (1 + x) ^ (s + 2) < 1 + delta / 2 :=
    htend.eventually_lt_const (by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp heventually
  let epsilon := min r 1 / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hepsilon1 : epsilon < 1 := by
    dsimp [epsilon]
    have h := min_le_right r (1 : ℝ)
    linarith
  have hepsilonr : epsilon < r := by
    dsimp [epsilon]
    have h := min_le_left r (1 : ℝ)
    linarith
  refine ⟨epsilon, hepsilon, hepsilon1, le_of_lt (hball epsilon ?_)⟩
  simpa [Real.dist_eq, abs_of_pos hepsilon] using hepsilonr

theorem positiveGrid_power_gap {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {V : ℕ} (hV : 1 ≤ V) : a ^ V + (b - a) ≤ b ^ V := by
  cases V with
  | zero => omega
  | succ n =>
    rw [pow_succ, pow_succ]
    have hgap : b - a ≤ a ^ n * (b - a) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ ha) (sub_nonneg.mpr hab)
    calc
      _ ≤ a ^ n * a + a ^ n * (b - a) := add_le_add le_rfl hgap
      _ = a ^ n * b := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hab n) (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev PositiveGridVertex {j : ℕ} (a : Fin j → ℕ) := ∀ i, Fin (a i)

abbrev PositiveGridShifts {j : ℕ} (a : Fin j → ℕ) (G : Type*) := ∀ i, Fin (a i) → G

def positiveGridVolume {j : ℕ} (a : Fin j → ℕ) : ℕ := ∏ i, a i

noncomputable def positiveGridProduct {j : ℕ} (a : Fin j → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (t : PositiveGridShifts a G) : ℝ :=
  ∏ b, f b (∑ i, t i (b i))

noncomputable def positiveGridMean {j : ℕ} (a : Fin j → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) : ℝ :=
  𝔼 t, positiveGridProduct a f t

theorem positiveGridVertex_card {j : ℕ} (a : Fin j → ℕ) :
    Fintype.card (PositiveGridVertex a) = positiveGridVolume a := by
  simp [PositiveGridVertex, positiveGridVolume, Fintype.card_pi]

theorem positiveGridVolume_succ {j : ℕ} (a : Fin (j + 1) → ℕ) :
    positiveGridVolume a = a 0 * positiveGridVolume (fun i => a i.succ) := by
  exact Fin.prod_univ_succ a

theorem positiveGridVolume_pos {j : ℕ} (a : Fin j → ℕ) (ha : ∀ i, 0 < a i) :
    0 < positiveGridVolume a := Finset.prod_pos (fun i _ => ha i)

theorem positiveGridVolume_le {j : ℕ} (a : Fin j → ℕ) {p : ℝ}
    (ha : ∀ i, (a i : ℝ) ≤ p) : (positiveGridVolume a : ℝ) ≤ p ^ j := by
  calc
    _ = ∏ i, (a i : ℝ) := by simp [positiveGridVolume]
    _ ≤ ∏ _i : Fin j, p := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => ha i)
    _ = _ := by simp

theorem positiveGridProduct_nonneg {j : ℕ} (a : Fin j → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (hf : ∀ b x, 0 ≤ f b x) (t) :
    0 ≤ positiveGridProduct a f t := Finset.prod_nonneg (fun b _ => hf b _)

theorem positiveGridProduct_le_exp {j : ℕ} (a : Fin j → ℕ) {G : Type*} [AddCommMonoid G]
    {p : ℝ} (f : PositiveGridVertex a → G → ℝ)
    (hf : ∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) (t) :
    positiveGridProduct a f t ≤ Real.exp ((positiveGridVolume a : ℝ) * p) := by
  calc
    _ ≤ ∏ _b : PositiveGridVertex a, Real.exp p :=
      Finset.prod_le_prod₀ (fun b _ => (hf b _).1) (fun b _ => (hf b _).2)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, positiveGridVertex_card, Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem prod_dependent_fin_cons {j : ℕ} {X : Fin (j + 1) → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [CommMonoid M] (F : (∀ i, X i) → M) :
    (∏ x, F x) = ∏ y : ∀ i : Fin j, X i.succ, ∏ a : X 0, F (Fin.cons a y) := by
  calc
    _ = ∏ p : X 0 × (∀ i : Fin j, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by rw [Fintype.prod_prod_type, Finset.prod_comm]

noncomputable def positiveGridFiber {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*} [Add G]
    (f : PositiveGridVertex a → G → ℝ) (t : Fin (a 0) → G) (c : ℝ)
    (b : PositiveGridVertex (fun i => a i.succ)) : G → ℝ :=
  normalizedAxisProduct (fun i => f (Fin.cons i b)) t c

theorem positiveGridProduct_cons {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] (f : PositiveGridVertex a → G → ℝ) (t : Fin (a 0) → G)
    (u : PositiveGridShifts (fun i => a i.succ) G) {c : ℝ} (hc : c ≠ 0) :
    positiveGridProduct a f (Fin.cons t u) = c ^ positiveGridVolume a *
      positiveGridProduct (fun i => a i.succ) (positiveGridFiber a f t c) u := by
  have heq (b : PositiveGridVertex (fun i => a i.succ)) :
      (∏ i : Fin (a 0), f (Fin.cons i b) (∑ k, (Fin.cons t u : PositiveGridShifts a G) k ((Fin.cons i b : PositiveGridVertex a) k))) =
        c ^ a 0 * positiveGridFiber a f t c b (∑ k, u k (b k)) := by
    simp only [positiveGridFiber, normalizedAxisProduct, axisProduct, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hc)]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (f (Fin.cons i b)) (add_comm _ _)
  unfold positiveGridProduct
  rw [prod_dependent_fin_cons]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, positiveGridVertex_card]
  rw [← pow_mul, positiveGridVolume_succ]

theorem positiveGridMean_first_axis {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) :
    positiveGridMean a f = 𝔼 t : Fin (a 0) → G,
      𝔼 u : PositiveGridShifts (fun i => a i.succ) G,
        positiveGridProduct a f (Fin.cons t u) := by
  exact expect_dependent_fin_cons (fun t => positiveGridProduct a f t)

theorem positiveGridMean_fiber {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ)
    (t : Fin (a 0) → G) {c : ℝ} (hc : c ≠ 0) :
    (𝔼 u : PositiveGridShifts (fun i => a i.succ) G, positiveGridProduct a f (Fin.cons t u)) =
      c ^ positiveGridVolume a * positiveGridMean (fun i => a i.succ) (positiveGridFiber a f t c) := by
  simp only [positiveGridProduct_cons a f t _ hc, positiveGridMean, Finset.mul_expect]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rootGrid_product {R : Type*} [AddCommMonoid R] (r q l : ℕ)
    (F : Fin r → (Fin l → Fin q) → R → ℝ) (root : Fin r → R) (z : Fin l → Fin q → R) :
    positiveGridProduct (Fin.cons r (fun _ : Fin l => q))
      (fun beta => F (beta 0) (fun i => beta i.succ)) (Fin.cons root z) =
      ∏ beta : Fin l → Fin q, ∏ j : Fin r, F j beta (root j + ∑ a, z a (beta a)) := by
  simp only [positiveGridProduct, prod_dependent_fin_cons, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rfl

theorem rootGrid_mean {R : Type*} [AddCommMonoid R] [Fintype R] (r q l : ℕ)
    (F : Fin r → (Fin l → Fin q) → R → ℝ) :
    positiveGridMean (Fin.cons r (fun _ : Fin l => q))
      (fun beta => F (beta 0) (fun i => beta i.succ)) =
      𝔼 z : Fin l → Fin q → R, 𝔼 root : Fin r → R,
        ∏ beta : Fin l → Fin q, ∏ j : Fin r, F j beta (root j + ∑ a, z a (beta a)) := by
  rw [positiveGridMean_first_axis, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro z _
  apply Finset.expect_congr rfl
  intro root _
  exact rootGrid_product r q l F root z

theorem scaledRootGrid_mean {R : Type*} [CommRing R] [Fintype R] (r q l : ℕ)
    (coeff : Fin l → R) (hcoeff : ∀ i, IsUnit (coeff i))
    (F : Fin r → (Fin l → Fin q) → R → ℝ) :
    (𝔼 z : Fin l → Fin q → R, 𝔼 root : Fin r → R,
      ∏ beta : Fin l → Fin q, ∏ j : Fin r, F j beta (root j + ∑ a, coeff a * z a (beta a))) =
      positiveGridMean (Fin.cons r (fun _ : Fin l => q))
        (fun beta => F (beta 0) (fun i => beta i.succ)) := by
  classical
  choose u hu using hcoeff
  let e : (Fin l → Fin q → R) ≃ (Fin l → Fin q → R) :=
    Equiv.piCongrRight (fun a => Equiv.piCongrRight (fun _ : Fin q => (u a).mulLeft))
  have he (z : Fin l → Fin q → R) (a : Fin l) (b : Fin q) : e z a b = coeff a * z a b := by
    change (u a : R) * z a b = coeff a * z a b
    rw [hu]
  rw [rootGrid_mean]
  apply Fintype.expect_equiv e
  intro z
  simp only [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positiveGridProduct_zero (a : Fin 0 → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (t : PositiveGridShifts a G) :
    positiveGridProduct a f t = f (fun i => Fin.elim0 i) 0 := by
  unfold positiveGridProduct
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp

theorem positiveGridProduct_one_axis (a : Fin 1 → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (t : PositiveGridShifts a G) :
    positiveGridProduct a f t =
      ∏ i : Fin (a 0), f (Fin.cons i (fun j => Fin.elim0 j)) (t 0 i) := by
  unfold positiveGridProduct
  rw [prod_dependent_fin_cons, Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.sum_univ_zero, add_zero]

theorem positiveGridMean_one_axis (a : Fin 1 → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) :
    positiveGridMean a f =
      ∏ i : Fin (a 0), (𝔼 x, f (Fin.cons i (fun j => Fin.elim0 j)) x) := by
  rw [positiveGridMean_first_axis]
  simp only [positiveGridProduct_one_axis, Fin.cons_zero, Fintype.expect_const]
  exact (FixedDensity.prod_mean (fun i x => f (Fin.cons i (fun j => Fin.elim0 j)) x)).symm

theorem positiveGridMean_one_axis_le (a : Fin 1 → ℕ) {N s : ℕ} [NeZero N]
    {P error g : ℝ} (hP : 2 ≤ P) (f : PositiveGridVertex a → ZMod N → ℝ)
    (hf : ∀ b x, 0 ≤ f b x)
    (hcompare : ∀ b, CyclicNiltestUpperComparison.{0} s N P error (f b) (fun _ => g)) :
    positiveGridMean a f ≤ (g + error) ^ positiveGridVolume a := by
  rw [positiveGridMean_one_axis]
  calc
    _ ≤ ∏ _i : Fin (a 0), (g + error) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.expect_nonneg (fun x _ => hf _ x)
      · intro i _
        exact CyclicNiltestUpperComparison.mean_le_const (hcompare _) hP
    _ = _ := by simp [positiveGridVolume]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def PositiveGridEstimate (s : ℕ) (epsilon : ℝ) (C : ℕ) : Prop :=
  ∀ {N j : ℕ} [NeZero N] {p L g : ℝ}, 2 ≤ p → 2 ≤ L → 1 ≤ g → g ≤ Real.exp p →
    Odd N → Real.exp ((p + L + 2) ^ C) ≤ N → 1 ≤ j → j ≤ s + 1 →
    ∀ a : Fin j → ℕ, (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ p) →
    ∀ f : PositiveGridVertex a → ZMod N → ℝ,
    (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
    (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
      (Real.exp (-((p + L + 2) ^ C))) (f b) (fun _ => g)) →
    positiveGridMean a f ≤ (g * (1 + epsilon) ^ (s + 1)) ^ positiveGridVolume a + Real.exp (-L)

theorem positiveGridMean_one_axis_slack (a : Fin 1 → ℕ) {N s : ℕ} [NeZero N]
    {P error epsilon g : ℝ} (hP : 2 ≤ P) (hepsilon : 0 ≤ epsilon) (hg : 1 ≤ g)
    (herror0 : 0 ≤ error) (herror : error ≤ epsilon) (f : PositiveGridVertex a → ZMod N → ℝ)
    (hf : ∀ b x, 0 ≤ f b x)
    (hcompare : ∀ b, CyclicNiltestUpperComparison.{0} s N P error (f b) (fun _ => g)) :
    positiveGridMean a f ≤ (g * (1 + epsilon)) ^ positiveGridVolume a := by
  have hmean := positiveGridMean_one_axis_le a hP f hf hcompare
  apply hmean.trans
  apply pow_le_pow_left₀ (by linarith : 0 ≤ g + error)
  nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hg)]

theorem exists_positiveGridEstimate_zero {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ PositiveGridEstimate 0 epsilon C := by
  obtain ⟨C, hC, hbase⟩ := exists_positiveGrid_base_budget hepsilon
  refine ⟨C, hC, ?_⟩
  intro N j _ p L g hp hL hg _ _ _ hj hj1 a _ f hf hcompare
  have hjeq : j = 1 := by omega
  subst j
  have hP : 2 ≤ (p + L + 2) ^ C :=
    (by linarith : 2 ≤ p + L).trans (le_power_budget (by linarith) (by omega))
  have h := positiveGridMean_one_axis_slack a hP hepsilon.le hg (Real.exp_nonneg _) (hbase (by linarith)) f
    (fun b x => (hf b x).1) hcompare
  simpa only [zero_add, pow_one] using h.trans (le_add_of_nonneg_right (Real.exp_nonneg (-L)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGrid_compression_bound (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {j N : ℕ} [NeZero N] {p L g A : ℝ},
      2 ≤ p → 2 ≤ L → 1 ≤ g → g ≤ Real.exp p → 0 ≤ A → Odd N →
      Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ (a : Fin (j + 1) → ℕ), (a 0 : ℝ) ≤ p →
      ∀ f : PositiveGridVertex a → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f b) (fun _ => g)) →
      (∀ h : PositiveGridVertex (fun i => a i.succ) → ZMod N → ℝ,
        (∀ b x, 0 ≤ h b x ∧ h b x ≤ Real.exp (p ^ 2)) →
        (∀ b, CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L)) (h b) (fun _ => 1)) →
        positiveGridMean (fun i => a i.succ) h ≤ A) →
      positiveGridMean a f ≤ ((1 + epsilon) * g) ^ positiveGridVolume a * A +
        Real.exp ((positiveGridVolume a : ℝ) * p) *
          (positiveGridVolume (fun i => a i.succ) : ℝ) * Real.exp (-L) := by
  classical
  obtain ⟨C, hC, hcompress⟩ := exists_simultaneous_axis_compression s hs hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro j N _ p L g A hp hL hg hgb hA hodd hN a ha f hf hcompare htail
  let c := (1 + epsilon) * g
  have hc : 0 < c := mul_pos (by linarith) (by linarith)
  obtain ⟨S, hS, hcap, hgood⟩ := hcompress hp hL ha hg hgb hodd hN
    (fun b i => f (Fin.cons i b)) (fun b i => hf (Fin.cons i b))
    (fun b i => hcompare (Fin.cons i b))
  have hSc : (S.card : ℝ) ≤
      ((positiveGridVolume (fun i => a i.succ) : ℝ) * Real.exp (-L)) *
        Fintype.card (Fin (a 0) → ZMod N) := by
    simpa only [positiveGridVertex_card, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      Nat.cast_pow] using hS
  let F : (Fin (a 0) → ZMod N) → ℝ := fun t =>
    𝔼 u : PositiveGridShifts (fun i => a i.succ) (ZMod N), positiveGridProduct a f (Fin.cons t u)
  have hbound (t) : F t ≤ Real.exp ((positiveGridVolume a : ℝ) * p) := by
    exact (Finset.expect_le_expect (fun u _ => positiveGridProduct_le_exp a f hf _)).trans_eq
      (Fintype.expect_const _)
  have hgoodF (t) (ht : t ∉ S) : F t ≤ c ^ positiveGridVolume a * A := by
    dsimp only [F]
    rw [positiveGridMean_fiber a f t hc.ne']
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc.le _)
    apply htail
    · exact fun b x => hcap b t x
    · exact hgood t ht
  rw [positiveGridMean_first_axis]
  have hresult := expect_le_of_exceptional_set S F (mul_nonneg (pow_nonneg hc.le _) hA)
    (Real.exp_nonneg _) hSc hbound hgoodF
  simpa only [F, c, mul_assoc] using hresult

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGridEstimate_step (s cPrevious : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hprevious : PositiveGridEstimate s epsilon cPrevious) :
    ∃ C : ℕ, 2 ≤ C ∧ PositiveGridEstimate (s + 1) epsilon C := by
  obtain ⟨cBase, _, hsmall⟩ := exists_positiveGrid_base_budget hepsilon
  obtain ⟨cCompression, _, hcompression⟩ :=
    exists_positiveGrid_compression_bound (s + 1) (by omega) hepsilon hepsilon1
  let X : Polynomial ℕ := Polynomial.X
  let RP := X + 4 * X ^ (s + 3) + 4
  let QP := (X ^ 2 + RP + 2) ^ cPrevious
  let TP := QP + RP
  let PP := (X + TP + 2) ^ cCompression
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget (PP + QP + (X + 2) ^ cBase + 2)
  refine ⟨C, hC, ?_⟩
  intro N j _ p L g hp hL hg hgb hodd hN hjpos hj a ha f hf hcompare
  let q := p + L
  let B := q ^ (s + 3)
  let R := q + 4 * B + 4
  let Q := (q ^ 2 + R + 2) ^ cPrevious
  let T := Q + R
  let P := (q + T + 2) ^ cCompression
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hLq : L ≤ q := by dsimp [q]; linarith
  have hB : 0 ≤ B := pow_nonneg hq0 _
  have hR : 2 ≤ R := by dsimp [R]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hT : 2 ≤ T := by dsimp [T]; linarith
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hcBase : 0 ≤ (q + 2) ^ cBase := pow_nonneg (by linarith) _
  have hcost : P + Q + (q + 2) ^ cBase + 2 ≤ (q + 2) ^ C := by
    simpa [X, RP, QP, TP, PP, P, T, Q, R, B, Polynomial.eval₂_pow] using hbudget q hq0
  have hcostP : P ≤ (q + 2) ^ C := by linarith
  have hcostQ : Q ≤ (q + 2) ^ C := by linarith
  have hcostBase : (q + 2) ^ cBase ≤ (q + 2) ^ C := by linarith
  have hQT : Q ≤ T := by dsimp [T]; linarith
  have hRT : R ≤ T := by dsimp [T]; linarith
  have hinput : 2 ≤ (q + 2) ^ C := hq.trans (le_power_budget hq0 (by omega))
  have hsmallC : Real.exp (-((q + 2) ^ C)) ≤ epsilon :=
    (Real.exp_le_exp.mpr (neg_le_neg hcostBase)).trans (hsmall hq)
  have hg0 : 0 ≤ g := by linarith
  have hb : 1 ≤ 1 + epsilon := by linarith
  have hb0 : 0 ≤ 1 + epsilon := by linarith
  by_cases hjone : j = 1
  · subst j
    have hmean := positiveGridMean_one_axis_slack a hinput hepsilon.le hg
      (Real.exp_nonneg _) hsmallC f (fun b x => (hf b x).1) hcompare
    have hbase : g * (1 + epsilon) ≤ g * (1 + epsilon) ^ (s + 2) := by
      apply mul_le_mul_of_nonneg_left _ hg0
      simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ s + 2 by omega)
    calc
      _ ≤ (g * (1 + epsilon)) ^ positiveGridVolume a := hmean
      _ ≤ (g * (1 + epsilon) ^ (s + 2)) ^ positiveGridVolume a :=
        pow_le_pow_left₀ (mul_nonneg hg0 hb0) hbase _
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_nonneg (-L))
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    let V := positiveGridVolume a
    let W := positiveGridVolume (fun i => a i.succ)
    let c := (1 + epsilon) * g
    let A := ((1 + epsilon) ^ (s + 1)) ^ W + Real.exp (-R)
    have hA : 0 ≤ A := add_nonneg (pow_nonneg (pow_nonneg hb0 _) _) (Real.exp_nonneg _)
    have hqSquare : q ≤ q ^ 2 := by nlinarith
    have hqSquare2 : 2 ≤ q ^ 2 := hq.trans hqSquare
    have htail : ∀ h : PositiveGridVertex (fun i => a i.succ) → ZMod N → ℝ,
        (∀ b x, 0 ≤ h b x ∧ h b x ≤ Real.exp (q ^ 2)) →
        (∀ b, CyclicNiltestUpperComparison.{0} ((s + 1) - 1) N T (Real.exp (-T)) (h b) (fun _ => 1)) →
        positiveGridMean (fun i => a i.succ) h ≤ A := by
      intro h hcap htest
      have hh := hprevious hqSquare2 hR (le_refl (1 : ℝ))
        (Real.one_le_exp (by positivity : 0 ≤ q ^ 2)) hodd
        ((Real.exp_le_exp.mpr hcostQ).trans hN) (show 1 ≤ k + 1 by omega)
        (show k + 1 ≤ s + 1 by omega) (fun i => a i.succ)
        (fun i => ⟨(ha i.succ).1, (ha i.succ).2.trans (hpq.trans hqSquare)⟩) h hcap
        (fun b => CyclicNiltestUpperComparison.mono_budget (htest b) hQT
          (Real.exp_le_exp.mpr (neg_le_neg hQT)))
      simpa only [one_mul] using hh
    have hgrid := hcompression hq hT hg (hgb.trans (Real.exp_le_exp.mpr hpq)) hA hodd
      ((Real.exp_le_exp.mpr hcostP).trans hN) a ((ha 0).2.trans hpq) f
      (fun b x => ⟨(hf b x).1, (hf b x).2.trans (Real.exp_le_exp.mpr hpq)⟩)
      (fun b => CyclicNiltestUpperComparison.mono_budget (hcompare b) hcostP
        (Real.exp_le_exp.mpr (neg_le_neg hcostP))) htail
    have hWV : W ≤ V := by
      calc
        W = 1 * W := by omega
        _ ≤ a 0 * W := Nat.mul_le_mul_right W (ha 0).1
        _ = V := (positiveGridVolume_succ a).symm
    have hV : (V : ℝ) * q ≤ B := by
      have hvolume : (V : ℝ) ≤ q ^ (s + 2) :=
        (positiveGridVolume_le a (fun i => (ha i).2.trans hpq)).trans
          (pow_le_pow_right₀ hq1 hj)
      calc
        _ ≤ q ^ (s + 2) * q := mul_le_mul_of_nonneg_right hvolume hq0
        _ = B := (pow_succ q (s + 2)).symm
    have hc0 : 0 ≤ c := mul_nonneg hb0 hg0
    have hcb : c ≤ Real.exp (2 * q) := by
      calc
        c ≤ 2 * Real.exp q := mul_le_mul (by linarith) (hgb.trans (Real.exp_le_exp.mpr hpq)) hg0 (by norm_num)
        _ ≤ Real.exp q * Real.exp q :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp q]) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have herr := positiveGrid_compression_errors V W hq1 hV hWV hc0 hcb
      (show L + 2 * B + 2 ≤ R by dsimp [R]; linarith) hRT
    have hmain := positiveGrid_normalization_bound hg0 hb s V W hWV
    calc
      positiveGridMean a f ≤ c ^ V * A + Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T) := hgrid
      _ = c ^ V * ((1 + epsilon) ^ (s + 1)) ^ W +
          (c ^ V * Real.exp (-R) + Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T)) := by
        dsimp [A]
        ring
      _ ≤ (g * (1 + epsilon) ^ (s + 2)) ^ V + Real.exp (-L) := add_le_add hmain herr

theorem exists_positiveGridEstimate (s : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ PositiveGridEstimate s epsilon C := by
  induction s with
  | zero => exact exists_positiveGridEstimate_zero hepsilon
  | succ s ih =>
    obtain ⟨cPrevious, _, hprevious⟩ := ih
    exact exists_positiveGridEstimate_step s cPrevious hepsilon hepsilon1 hprevious

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGrid_counting (s : ℕ) {delta C0 : ℝ}
    (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧ ∀ {N j : ℕ} [NeZero N] {p xi : ℝ},
      2 ≤ p → 0 < xi → xi ≤ xi0 → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      1 ≤ j → j ≤ s + 1 → ∀ a : Fin j → ℕ,
      (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ C0 * p) →
      ∀ f : PositiveGridVertex a → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (f b) (fun _ => 1 + xi)) →
      positiveGridMean a f ≤ (1 + delta) ^ positiveGridVolume a := by
  obtain ⟨epsilon, hepsilon, hepsilon1, hslack⟩ := exists_positiveGrid_slack s hdelta
  obtain ⟨c, _, hgrid⟩ := exists_positiveGridEstimate s hepsilon hepsilon1
  obtain ⟨A, hA⟩ := exists_nat_ge C0
  obtain ⟨ell, hell⟩ := exists_nat_ge (max 2 (-Real.log (delta / 2)))
  have hell2 : (2 : ℝ) ≤ ell := (le_max_left _ _).trans hell
  have hlog : -Real.log (delta / 2) ≤ ell := (le_max_right _ _).trans hell
  have herror : Real.exp (-(ell : ℝ)) ≤ delta / 2 := by
    calc
      _ ≤ Real.exp (Real.log (delta / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by linarith)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.C A * (X + 1) + Polynomial.C ell + 2) ^ c)
  refine ⟨C, hC, epsilon, hepsilon, ?_⟩
  intro N j _ p xi hp hxi hxiepsilon hodd hN hj hjbound a ha f hf hcompare
  let q : ℝ := A * (p + 1)
  have hA1 : (1 : ℝ) ≤ A := hC0.trans hA
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hp0 : 0 ≤ p := by linarith
  have hpq : p ≤ q := by
    dsimp [q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (show 0 ≤ p + 1 by linarith)]
  have hq : 2 ≤ q := hp.trans hpq
  have hcost : (q + ell + 2) ^ c ≤ (p + 2) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hgb : 1 + xi ≤ Real.exp q := by
    have h := Real.add_one_le_exp q
    linarith
  have hbound (i) : (a i : ℝ) ≤ q := by
    calc
      _ ≤ C0 * p := (ha i).2
      _ ≤ (A : ℝ) * p := mul_le_mul_of_nonneg_right hA hp0
      _ ≤ q := mul_le_mul_of_nonneg_left (by linarith : p ≤ p + 1) hA0
  have h := hgrid hq hell2 (by linarith : 1 ≤ 1 + xi) hgb hodd
    ((Real.exp_le_exp.mpr hcost).trans hN) hj hjbound a
    (fun i => ⟨(ha i).1, hbound i⟩) f
    (fun b x => ⟨(hf b x).1, (hf b x).2.trans (Real.exp_le_exp.mpr hpq)⟩)
    (fun b => CyclicNiltestUpperComparison.mono_budget (hcompare b) hcost
      (Real.exp_le_exp.mpr (neg_le_neg hcost)))
  have hb0 : 0 ≤ 1 + epsilon := by linarith
  have hmain : (1 + xi) * (1 + epsilon) ^ (s + 1) ≤ 1 + delta / 2 := by
    calc
      _ ≤ (1 + epsilon) * (1 + epsilon) ^ (s + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hb0 _)
      _ = (1 + epsilon) ^ (s + 2) := (pow_succ' _ _).symm
      _ ≤ _ := hslack
  have hvolume : 1 ≤ positiveGridVolume a :=
    positiveGridVolume_pos a (fun i => (ha i).1)
  have hgap := positiveGrid_power_gap (by linarith : 1 ≤ 1 + delta / 2)
    (by linarith : 1 + delta / 2 ≤ 1 + delta) hvolume
  calc
    _ ≤ ((1 + xi) * (1 + epsilon) ^ (s + 1)) ^ positiveGridVolume a + Real.exp (-(ell : ℝ)) := h
    _ ≤ (1 + delta / 2) ^ positiveGridVolume a + delta / 2 :=
      add_le_add (pow_le_pow_left₀ (mul_nonneg (by linarith) (pow_nonneg hb0 _)) hmain _) herror
    _ ≤ _ := by convert hgap using 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem CyclicNiltestUpperComparison.of_pointwise.{universeLevel} {s N : ℕ} [NeZero N]
    {P error : ℝ} {f g : ZMod N → ℝ} (hfg : ∀ x, f x ≤ g x) (herror : 0 ≤ error) :
    CyclicNiltestUpperComparison.{universeLevel} s N P error f g := by
  intro L _ _ degree dim _ _ _ _ D _ T hT _
  apply le_trans _ herror
  refine (Finset.expect_le_expect (fun x _ => ?_)).trans_eq (Fintype.expect_const (0 : ℝ))
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hfg x))
    (T.unit_interval_evalCyclic hT N (fun _ => x)).2.1

theorem exists_positiveGrid_family_counting (s : ℕ) {delta C0 : ℝ}
    (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {I : Type*} {N j : ℕ} [NeZero N] {p xi : ℝ},
      2 ≤ p → 0 < xi → xi ≤ xi0 → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      1 ≤ j → j ≤ s + 1 → ∀ a : Fin j → ℕ,
      (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ C0 * p) → ∀ f : I → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (f b) (fun _ => 1 + xi)) →
      ∀ choice : PositiveGridVertex a → Option I,
      positiveGridMean a (fun b x => (choice b).elim 1 (fun i => f i x)) ≤
        (1 + delta) ^ positiveGridVolume a := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_positiveGrid_counting s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro I N j _ p xi hp hxi hxib hodd hN hj hjb a ha f hf hcompare choice
  apply hgrid hp hxi hxib hodd hN hj hjb a ha
  · intro b x
    cases hc : choice b with
    | none => simpa only [hc, Option.elim_none] using
        (show (0 : ℝ) ≤ 1 ∧ 1 ≤ Real.exp p from ⟨zero_le_one, Real.one_le_exp (by linarith)⟩)
    | some i => simpa only [hc, Option.elim_some] using hf i x
  · intro b
    cases hc : choice b with
    | none =>
      change CyclicNiltestUpperComparison s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (fun _ => 1) (fun _ => 1 + xi)
      exact CyclicNiltestUpperComparison.of_pointwise (fun _ => by linarith) (Real.exp_nonneg _)
    | some i =>
      change CyclicNiltestUpperComparison s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (f i) (fun _ => 1 + xi)
      exact @hcompare i

end Erdos3

end

end OAI
