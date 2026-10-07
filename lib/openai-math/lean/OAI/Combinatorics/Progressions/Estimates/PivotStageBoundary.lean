/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Linear.CountingKernelOuter
import OAI.Combinatorics.Progressions.Sampling.PositiveGridFamily

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_independent_product {G : Type*} [Fintype G] [Nonempty G]
    (q : ℕ) (f : G → ℝ) :
    (𝔼 t : Fin q → G, ∏ i, f (t i)) = (𝔼 x, f x) ^ q := by
  simpa [FixedDensity.mean] using (FixedDensity.prod_mean (fun _i : Fin q => f)).symm

theorem expect_common_shift_product {G : Type*} [AddGroup G] [Fintype G]
    (q : ℕ) (d : G) (f : G → ℝ) :
    (𝔼 t : Fin q → G, ∏ i, f (d + t i)) = (𝔼 x, f x) ^ q := by
  rw [expect_independent_product q (fun x => f (d + x))]
  congr 1
  apply Fintype.expect_equiv (Equiv.addLeft d)
  intro x
  rfl

theorem expect_pivot_change {R : Type*} [Ring R] [Fintype R]
    (p : R) (F : R → R → ℝ) :
    (𝔼 x, 𝔼 d, F x d) = 𝔼 w, 𝔼 d, F (w - p * d) d := by
  rw [Finset.expect_comm, Finset.expect_comm (Finset.univ : Finset R) (Finset.univ : Finset R)
    (fun w d => F (w - p * d) d)]
  apply Finset.expect_congr rfl
  intro d _
  symm
  apply Fintype.expect_equiv (Equiv.addRight (-(p * d)))
  intro w
  change F (w - p * d) d = F (w + -(p * d)) d
  rw [sub_eq_add_neg]

theorem pivot_even_moment {R : Type*} [CommRing R] [Fintype R]
    (q : ℕ) (hq : Even q) (p : R) (H : R → R → ℝ) :
    (𝔼 x, 𝔼 d, 𝔼 t : Fin q → R, ∏ i, H (x - p * t i) (d + t i)) =
      𝔼 w, |𝔼 d, H (w - p * d) d| ^ q := by
  rw [expect_pivot_change p]
  apply Finset.expect_congr rfl
  intro w _
  have hpoint (d : R) :
      (𝔼 t : Fin q → R, ∏ i, H ((w - p * d) - p * t i) (d + t i)) =
        (𝔼 a, H (w - p * a) a) ^ q := by
    have heq (t : Fin q → R) (i : Fin q) :
        H ((w - p * d) - p * t i) (d + t i) = H (w - p * (d + t i)) (d + t i) := by
      congr 1
      ring
    simp_rw [heq]
    exact expect_common_shift_product q d (fun a => H (w - p * a) a)
  simp only [hpoint, Fintype.expect_const, hq.pow_abs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem twoSlopeMap_bijective {R : Type*} [CommRing R] (a b : R) (hab : IsUnit (b - a)) :
    Function.Bijective (fun z : R × R => (z.1 + a * z.2, z.1 + b * z.2)) := by
  obtain ⟨u, hu⟩ := hab
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hd : (u : R) * x.2 = (u : R) * y.2 := by
      rw [hu]
      dsimp at h1 h2
      linear_combination h2 - h1
    have hxy : x.2 = y.2 := u.isUnit.mul_left_cancel hd
    apply Prod.ext
    · dsimp at h1
      rw [hxy] at h1
      exact add_right_cancel h1
    · exact hxy
  · rintro ⟨y, z⟩
    let d := (↑(u⁻¹) : R) * (z - y)
    refine ⟨(y - a * d, d), ?_⟩
    apply Prod.ext
    · dsimp
      ring
    · change y - a * d + b * d = z
      have hd : (b - a) * d = z - y := by
        rw [← hu]
        dsimp [d]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      linear_combination hd

theorem expect_two_slopes {R : Type*} [CommRing R] [Fintype R]
    (a b : R) (hab : IsUnit (b - a)) (F : R → R → ℝ) :
    (𝔼 x, 𝔼 d, F (x + a * d) (x + b * d)) = 𝔼 y, 𝔼 z, F y z := by
  let e := Equiv.ofBijective _ (twoSlopeMap_bijective a b hab)
  have h : (𝔼 q : R × R, F (q.1 + a * q.2) (q.1 + b * q.2)) =
      𝔼 q : R × R, F q.1 q.2 := by
    apply Fintype.expect_equiv e
    intro q
    rfl
  simpa only [expect_prod_split] using h

theorem expect_two_slope_product {R : Type*} [CommRing R] [Fintype R]
    (a b : R) (hab : IsUnit (b - a)) (f g : R → ℝ) :
    (𝔼 x, 𝔼 d, f (x + a * d) * g (x + b * d)) = (𝔼 x, f x) * (𝔼 x, g x) := by
  rw [expect_two_slopes a b hab (fun x y => f x * g y)]
  simp only [← Finset.mul_expect, ← Finset.expect_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.mean_pow_two_pow_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (n : ℕ) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    p.mean f ^ (2 ^ n) ≤ p.mean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (p.mean f ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (p.mean (fun x => f x ^ (2 ^ n))) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (p.mean_nonneg hf) _) ih 2
      _ ≤ p.mean (fun x => (f x ^ (2 ^ n)) ^ 2) := p.mean_square_le _
      _ = _ := by simp only [pow_succ, pow_mul]

theorem weighted_dyadic_holder {X : Type*} [Fintype X] [Nonempty X]
    (n : ℕ) (D F : X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ x, 0 ≤ D x) (hcap : ∀ x, D x ≤ B) :
    |𝔼 x, D x * F x| ^ (2 ^ n) ≤
      (𝔼 x, D x) ^ (2 ^ n - 1) * B * (𝔼 x, |F x| ^ (2 ^ n)) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hmean : 0 ≤ 𝔼 x, D x := Finset.expect_nonneg (fun x _ => hD x)
  by_cases hm : (𝔼 x, D x) = 0
  · have hsum : ∑ x, D x = 0 := by
      have h := Fintype.card_mul_expect D
      rw [hm, mul_zero] at h
      exact h.symm
    have hzero : ∀ x, D x = 0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hD y)).mp hsum x (Finset.mem_univ x)
    simp only [hzero, zero_mul, Fintype.expect_const, abs_zero, zero_pow hq0]
    positivity
  · have hmpos : 0 < 𝔼 x, D x := lt_of_le_of_ne hmean (Ne.symm hm)
    let p := FiniteProbabilityWeights.uniform X
    have hpm : 0 < p.mean D := by simpa only [p, FiniteProbabilityWeights.uniform_mean] using hmpos
    let w := p.reweightPositive D hD hpm
    have hnorm := w.mean_pow_two_pow_le n (fun x => |F x|) (fun x => abs_nonneg _)
    have hnorm' : ((𝔼 x, D x * |F x|) / (𝔼 x, D x)) ^ (2 ^ n) ≤
        (𝔼 x, D x * |F x| ^ (2 ^ n)) / (𝔼 x, D x) := by
      simpa only [w, FiniteProbabilityWeights.reweightPositive_mean, p,
        FiniteProbabilityWeights.uniform_mean] using hnorm
    rw [div_pow] at hnorm'
    have hweighted := (div_le_iff₀ (pow_pos hmpos (2 ^ n))).mp hnorm'
    have hfactor : (𝔼 x, D x) ^ (2 ^ n) = (𝔼 x, D x) ^ (2 ^ n - 1) * (𝔼 x, D x) := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    have hpoint (x : X) : |D x * F x| = D x * |F x| := by rw [abs_mul, abs_of_nonneg (hD x)]
    have habs : |𝔼 x, D x * F x| ≤ 𝔼 x, D x * |F x| := by
      simpa only [Real.norm_eq_abs, hpoint] using
        (RCLike.norm_expect_le (K := ℝ) (f := fun x => D x * F x))
    have hmoment : (𝔼 x, D x * |F x| ^ (2 ^ n)) ≤ B * (𝔼 x, |F x| ^ (2 ^ n)) := by
      calc
        _ ≤ 𝔼 x, B * |F x| ^ (2 ^ n) :=
          Finset.expect_le_expect (fun x _ => mul_le_mul_of_nonneg_right (hcap x) (pow_nonneg (abs_nonneg _) _))
        _ = _ := (Finset.mul_expect _ _ _).symm
    calc
      _ ≤ (𝔼 x, D x * |F x|) ^ (2 ^ n) := pow_le_pow_left₀ (abs_nonneg _) habs _
      _ ≤ ((𝔼 x, D x * |F x| ^ (2 ^ n)) / (𝔼 x, D x)) * (𝔼 x, D x) ^ (2 ^ n) := hweighted
      _ = (𝔼 x, D x) ^ (2 ^ n - 1) * (𝔼 x, D x * |F x| ^ (2 ^ n)) := by
        rw [hfactor]
        field_simp [hm]
      _ ≤ (𝔼 x, D x) ^ (2 ^ n - 1) * (B * (𝔼 x, |F x| ^ (2 ^ n))) :=
        mul_le_mul_of_nonneg_left hmoment (pow_nonneg hmean _)
      _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_single_slope {R : Type*} [Ring R] [Fintype R] (a : R) (f : R → ℝ) :
    (𝔼 x, 𝔼 d, f (x + a * d)) = 𝔼 x, f x := by
  rw [Finset.expect_comm]
  have h (d : R) : (𝔼 x, f (x + a * d)) = 𝔼 x, f x := by
    apply Fintype.expect_equiv (Equiv.addRight (a * d))
    intro x
    rfl
  simp only [h, Fintype.expect_const]

theorem product_near_one {a b delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (ha : |a - 1| ≤ delta) (hb : |b - 1| ≤ delta) : |a * b - 1| ≤ 3 * delta := by
  have ha' : |a| ≤ 1 + delta := by
    have h := abs_add_le (a - 1) (1 : ℝ)
    norm_num at h
    linarith
  calc
    |a * b - 1| = |a * (b - 1) + (a - 1)| := by congr 1; ring
    _ ≤ |a * (b - 1)| + |a - 1| := abs_add_le _ _
    _ = |a| * |b - 1| + |a - 1| := by rw [abs_mul]
    _ ≤ (1 + delta) * delta + delta :=
      add_le_add (mul_le_mul ha' hb (abs_nonneg _) (by linarith)) ha
    _ ≤ 3 * delta := by nlinarith

theorem twoSlope_average_near_one {R : Type*} [CommRing R] [Fintype R]
    (a b : R) (hab : IsUnit (b - a)) (f g : R → ℝ)
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hf : |(𝔼 x, f x) - 1| ≤ delta) (hg : |(𝔼 x, g x) - 1| ≤ delta) :
    |(𝔼 x, 𝔼 d, f (x + a * d) * g (x + b * d)) - 1| ≤ 3 * delta := by
  rw [expect_two_slope_product a b hab]
  exact product_near_one hdelta hdelta1 hf hg

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def pivotCellForm {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (z : Fin l → Fin q → R) (x d : R) (beta : Fin l → Fin q) : R :=
  x + slope * d + ∑ a, (slope - v a) * z a (beta a)

noncomputable def pivotGridFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  ∏ beta : Fin l → Fin q, f (pivotCellForm v slope z x d beta)

noncomputable def pivotRootFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (w : R) : ℝ :=
  ∏ beta : Fin l → Fin q, f (w + ∑ a, (slope - v a) * z a (beta a))

noncomputable def pivotKernelFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (a b : R) (parameter : ℝ) (f g : R → ℝ)
    (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  ∏ beta : Fin l → Fin q, countingKernel parameter
    (f (pivotCellForm v a z x d beta)) (g (pivotCellForm v b z x d beta))

noncomputable def pivotStageIntegrand {I R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  (∏ i ∈ S, pivotGridFactor v (slopes i) (mu i) z x d) *
    pivotKernelFactor v a b parameter f g z x d

noncomputable def pivotStageCount {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) : ℝ :=
  𝔼 z : Fin l → Fin q → R, 𝔼 x, 𝔼 d, pivotStageIntegrand v S slopes mu a b parameter f g z x d

theorem pivotGridFactor_root {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (x d : R) :
    pivotGridFactor v slope f z x d = pivotRootFactor v slope f z (x + slope * d) := rfl

theorem pivotRootFactor_nonneg {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (hf : ∀ x, 0 ≤ f x)
    (z : Fin l → Fin q → R) (w : R) : 0 ≤ pivotRootFactor v slope f z w :=
  Finset.prod_nonneg (fun _ _ => hf _)

theorem pivotRootFactor_le_exp {R : Type*} [CommRing R] {l q : ℕ} {p : ℝ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p)
    (z : Fin l → Fin q → R) (w : R) :
    pivotRootFactor v slope f z w ≤ Real.exp ((q ^ l : ℕ) * p) := by
  calc
    _ ≤ ∏ _beta : Fin l → Fin q, Real.exp p :=
      Finset.prod_le_prod₀ (fun beta _ => (hf _).1) (fun beta _ => (hf _).2)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivot_weighted_dyadic_step {R Z : Type*} [CommRing R] [Fintype R]
    [Fintype Z] [Nonempty Z] (n : ℕ) (p : R) (D : Z → R → ℝ) (H : Z → R → R → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z w, 0 ≤ D z w) (hcap : ∀ z w, D z w ≤ B) :
    |𝔼 z, 𝔼 x, 𝔼 d, D z (x + p * d) * H z x d| ^ (2 ^ (n + 1)) ≤
      (𝔼 z, 𝔼 w, D z w) ^ (2 ^ (n + 1) - 1) * B *
        (𝔼 z, 𝔼 x, 𝔼 d, 𝔼 t : Fin (2 ^ (n + 1)) → R, ∏ i, H z (x - p * t i) (d + t i)) := by
  have heven : Even (2 ^ (n + 1)) := by
    refine ⟨2 ^ n, ?_⟩
    rw [pow_succ]
    omega
  have hchange (z : Z) :
      (𝔼 x, 𝔼 d, D z (x + p * d) * H z x d) =
        𝔼 w, D z w * (𝔼 d, H z (w - p * d) d) := by
    rw [expect_pivot_change p]
    simp only [sub_add_cancel, ← Finset.mul_expect]
  let D' : Z × R → ℝ := fun u => D u.1 u.2
  let H' : Z × R → ℝ := fun u => 𝔼 d, H u.1 (u.2 - p * d) d
  have h := weighted_dyadic_holder (n + 1) D' H' hB (fun u => hD u.1 u.2) (fun u => hcap u.1 u.2)
  have hm (z : Z) := pivot_even_moment (2 ^ (n + 1)) heven p (H z)
  simpa only [D', H', expect_prod_split, hchange, hm] using h

end Erdos3

end

section

namespace Erdos3

def PivotCompatible {I R : Type*} [CommRing R] {l : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (a b : R) : Prop :=
  IsUnit (b - a) ∧
    (∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i)) ∧
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) ∧
    (∀ j, IsUnit (a - v j) ∧ IsUnit (b - v j) ∧
      ∀ i ∈ S, IsUnit (slopes i - v j))

theorem PivotCompatible.cons_erase {I R : Type*} [DecidableEq I] [CommRing R] {l : ℕ}
    {v : Fin l → R} {S : Finset I} {slopes : I → R} {a b : R}
    (h : PivotCompatible v S slopes a b) {i : I} (hi : i ∈ S) :
    PivotCompatible (Fin.cons (slopes i) v) (S.erase i) slopes a b := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro j hj
    exact h.2.1 j (Finset.mem_of_mem_erase hj)
  · intro j hj k hk hjk
    exact h.2.2.1 j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨(h.2.1 i hi).1, (h.2.1 i hi).2, ?_⟩
      intro k hk
      exact h.2.2.1 k (Finset.mem_of_mem_erase hk) i hi (Finset.ne_of_mem_erase hk)
    · exact ⟨(h.2.2.2 j).1, (h.2.2.2 j).2.1,
        fun k hk => (h.2.2.2 j).2.2 k (Finset.mem_of_mem_erase hk)⟩

theorem pivotCompatible_zero {I R : Type*} [CommRing R]
    (v : Fin 0 → R) (S : Finset I) (slopes : I → R) (a b : R)
    (hab : IsUnit (b - a))
    (hends : ∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i))
    (hpairs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) :
    PivotCompatible v S slopes a b :=
  ⟨hab, hends, hpairs, fun j => Fin.elim0 j⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotCellForm_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot slope : R) (z : Fin l → Fin q → R) (t : Fin q → R)
    (x d : R) (i : Fin q) (beta : Fin l → Fin q) :
    pivotCellForm (Fin.cons pivot v) slope (Fin.cons t z) x d (Fin.cons i beta) =
      pivotCellForm v slope z (x - pivot * t i) (d + t i) beta := by
  simp only [pivotCellForm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem pivotGridFactor_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (t : Fin q → R)
    (x d : R) :
    pivotGridFactor (Fin.cons pivot v) slope f (Fin.cons t z) x d =
      ∏ i : Fin q, pivotGridFactor v slope f z (x - pivot * t i) (d + t i) := by
  unfold pivotGridFactor
  rw [prod_dependent_fin_cons]
  simp only [pivotCellForm_cons]
  rw [Finset.prod_comm]

theorem pivotKernelFactor_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot a b : R) (parameter : ℝ) (f g : R → ℝ)
    (z : Fin l → Fin q → R) (t : Fin q → R) (x d : R) :
    pivotKernelFactor (Fin.cons pivot v) a b parameter f g (Fin.cons t z) x d =
      ∏ i : Fin q, pivotKernelFactor v a b parameter f g z (x - pivot * t i) (d + t i) := by
  unfold pivotKernelFactor
  rw [prod_dependent_fin_cons]
  simp only [pivotCellForm_cons]
  rw [Finset.prod_comm]

theorem pivotStageIntegrand_cons {I R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (t : Fin q → R) (x d : R) :
    pivotStageIntegrand (Fin.cons pivot v) S slopes mu a b parameter f g (Fin.cons t z) x d =
      ∏ i : Fin q, pivotStageIntegrand v S slopes mu a b parameter f g z
        (x - pivot * t i) (d + t i) := by
  simp only [pivotStageIntegrand, pivotGridFactor_cons, pivotKernelFactor_cons, Finset.prod_mul_distrib]
  rw [Finset.prod_comm]

theorem pivotStageIntegrand_peel {I R : Type*} [DecidableEq I] [CommRing R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (x d : R)
    {i : I} (hi : i ∈ S) :
    pivotStageIntegrand v S slopes mu a b parameter f g z x d =
      pivotRootFactor v (slopes i) (mu i) z (x + slopes i * d) *
        pivotStageIntegrand v (S.erase i) slopes mu a b parameter f g z x d := by
  unfold pivotStageIntegrand
  rw [← Finset.mul_prod_erase S _ hi, pivotGridFactor_root]
  ring

theorem pivotStageCount_cons {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) (Fin.cons pivot v) S slopes mu a b parameter f g =
      𝔼 z : Fin l → Fin q → R, 𝔼 x, 𝔼 d, 𝔼 t : Fin q → R,
        ∏ i : Fin q, pivotStageIntegrand v S slopes mu a b parameter f g z
          (x - pivot * t i) (d + t i) := by
  rw [pivotStageCount, expect_fin_cons]
  simp only [pivotStageIntegrand_cons]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro z _
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotStageCount_cons_nonneg {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (hq : Even q) (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    0 ≤ pivotStageCount (q := q) (Fin.cons pivot v) S slopes mu a b parameter f g := by
  rw [pivotStageCount_cons]
  have hm (z : Fin l → Fin q → R) :=
    pivot_even_moment q hq pivot (pivotStageIntegrand v S slopes mu a b parameter f g z)
  simp only [hm]
  exact Finset.expect_nonneg (fun z _ => Finset.expect_nonneg (fun w _ => pow_nonneg (abs_nonneg _) _))

theorem pivotStageCount_step {I R : Type*} [DecidableEq I] [CommRing R] [Fintype R]
    {l : ℕ} (n : ℕ) (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) {i : I} (hi : i ∈ S) {p : ℝ}
    (hmu : ∀ x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) :
    |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ^ (2 ^ (n + 1)) ≤
      (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w, pivotRootFactor v (slopes i) (mu i) z w) ^
        (2 ^ (n + 1) - 1) * Real.exp (((2 ^ (n + 1)) ^ l : ℕ) * p) *
      pivotStageCount (q := 2 ^ (n + 1)) (Fin.cons (slopes i) v) (S.erase i) slopes mu a b parameter f g := by
  let D : (Fin l → Fin (2 ^ (n + 1)) → R) → R → ℝ := pivotRootFactor v (slopes i) (mu i)
  let H : (Fin l → Fin (2 ^ (n + 1)) → R) → R → R → ℝ :=
    pivotStageIntegrand v (S.erase i) slopes mu a b parameter f g
  have h := pivot_weighted_dyadic_step n (slopes i) D H (Real.exp_nonneg _)
    (fun z w => pivotRootFactor_nonneg v (slopes i) (mu i) (fun x => (hmu x).1) z w)
    (fun z w => pivotRootFactor_le_exp v (slopes i) (mu i) hmu z w)
  have hleft : (𝔼 z, 𝔼 x, 𝔼 d, D z (x + slopes i * d) * H z x d) =
      pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g := by
    unfold pivotStageCount
    apply Finset.expect_congr rfl
    intro z _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro d _
    exact (pivotStageIntegrand_peel v S slopes mu a b parameter f g z x d hi).symm
  have hright : (𝔼 z, 𝔼 x, 𝔼 d, 𝔼 t : Fin (2 ^ (n + 1)) → R,
      ∏ j, H z (x - slopes i * t j) (d + t j)) =
        pivotStageCount (q := 2 ^ (n + 1)) (Fin.cons (slopes i) v) (S.erase i) slopes mu a b parameter f g := by
    exact (pivotStageCount_cons v (slopes i) (S.erase i) slopes mu a b parameter f g).symm
  rw [hleft, hright] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotGridFactor_zero {R : Type*} [CommRing R] {q : ℕ}
    (v : Fin 0 → R) (slope : R) (f : R → ℝ) (z : Fin 0 → Fin q → R) (x d : R) :
    pivotGridFactor v slope f z x d = f (x + slope * d) := by
  unfold pivotGridFactor
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp [pivotCellForm]

theorem pivotKernelFactor_zero {R : Type*} [CommRing R] {q : ℕ}
    (v : Fin 0 → R) (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin 0 → Fin q → R) (x d : R) :
    pivotKernelFactor v a b parameter f g z x d = countingKernel parameter (f (x + a * d)) (g (x + b * d)) := by
  unfold pivotKernelFactor
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp [pivotCellForm]

theorem pivotStageCount_zero {I R : Type*} [CommRing R] [Fintype R] {q : ℕ}
    (v : Fin 0 → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) v S slopes mu a b parameter f g =
      𝔼 x, 𝔼 d, (∏ i ∈ S, mu i (x + slopes i * d)) *
        countingKernel parameter (f (x + a * d)) (g (x + b * d)) := by
  simp only [pivotStageCount, pivotStageIntegrand, pivotGridFactor_zero,
    pivotKernelFactor_zero, Fintype.expect_const]

theorem pivotStageCount_terminal {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (hab : IsUnit (b - a)) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) v (∅ : Finset I) slopes mu a b parameter f g =
      𝔼 z : Fin l → Fin q → R, countingKernelProductAverage parameter
        (fun (beta : Fin l → Fin q) (u : R) => f (u + ∑ j, (a - v j) * z j (beta j)))
        (fun (beta : Fin l → Fin q) (w : R) => g (w + ∑ j, (b - v j) * z j (beta j))) := by
  simp only [pivotStageCount, pivotStageIntegrand, Finset.prod_empty, one_mul]
  apply Finset.expect_congr rfl
  intro z _
  exact expect_two_slopes a b hab (fun u w => ∏ beta : Fin l → Fin q,
    countingKernel parameter (f (u + ∑ j, (a - v j) * z j (beta j)))
      (g (w + ∑ j, (b - v j) * z j (beta j))))

end Erdos3

end

end OAI
