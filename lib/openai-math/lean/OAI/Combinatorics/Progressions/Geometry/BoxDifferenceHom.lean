import OAI.Combinatorics.Progressions.Estimates.DenseProductApproximation
import OAI.Combinatorics.Progressions.Polynomial.PhasePreservingCauchySchwarz
import OAI.Combinatorics.Progressions.Probability.FiniteMassErrorSelection

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_prod_split {X Y M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] [Module ℚ≥0 M] (F : X × Y → M) :
    (𝔼 p, F p) = 𝔼 x, 𝔼 y, F (x,y) := by
  simpa using (Finset.expect_product' (Finset.univ : Finset X)
    (Finset.univ : Finset Y) (fun x y => F (x,y)))

theorem expect_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = F (fun i => Fin.elim0 i) := by
  calc
    (𝔼 x, F x) = 𝔼 _x : ∀ i, X i, F (fun i => Fin.elim0 i) := by
      apply Finset.expect_congr rfl
      intro x _
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := Fintype.expect_const _

theorem expect_two_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → (∀ i, X i) → M) :
    (𝔼 x, 𝔼 y, F x y) =
      𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
        𝔼 v : ∀ i : Fin n, X i.succ, F (Fin.cons a u) (Fin.cons b v) := by
  rw [expect_dependent_fin_cons]
  apply Finset.expect_congr rfl
  intro a _
  simp_rw [expect_dependent_fin_cons]
  exact Finset.expect_comm _ _ _

theorem expect_pow_two_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (n : ℕ) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, f x)^(2^n) ≤ 𝔼 x, (f x)^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, pow_mul]
    calc
      ((𝔼 x, f x)^(2^n))^2 ≤ (𝔼 x, (f x)^(2^n))^2 :=
        pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg (fun x _ => hf x)) _) ih 2
      _ ≤ 𝔼 x, ((f x)^(2^n))^2 := expect_square_le _

theorem expect_double_pow_two_pow_le {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (n : ℕ) (f : X → Y → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    (𝔼 x, 𝔼 y, f x y)^(2^n) ≤ 𝔼 x, 𝔼 y, (f x y)^(2^n) := by
  apply (expect_pow_two_pow_le n (fun x => 𝔼 y, f x y)
    (fun x => Finset.expect_nonneg (fun y _ => hf x y))).trans
  exact Finset.expect_le_expect (fun x _ => expect_pow_two_pow_le n (f x) (hf x))

theorem norm_mean_first_difference {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] (F : X → Y → ℂ) :
    ‖𝔼 x, 𝔼 y, F x y‖^2 ≤ 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ := by
  have h := finite_family_cauchy_schwarz (fun _ : Y => (1 : ℂ)) F
    (show ∀ _ : Y, ‖(1 : ℂ)‖ ≤ (1 : ℝ) by intro; norm_num)
  simpa only [one_mul, one_pow, Finset.expect_comm (Finset.univ : Finset Y)
    (Finset.univ : Finset X)] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxCorrelation {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) : ℂ :=
  𝔼 x, 𝔼 x', 𝔼 y, 𝔼 y',
    F x y * star (F x' y) * star (F x y') * F x' y'

theorem finiteBoxCorrelation_re_eq_mean_square {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) :
    (finiteBoxCorrelation F).re = 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
  unfold finiteBoxCorrelation
  simp_rw [square_norm_mean_eq_cross_re, ← expect_re]
  congr 1
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro x' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  simp only [star_mul, star_star]
  ring

theorem finiteBoxCorrelation_re_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) : 0 ≤ (finiteBoxCorrelation F).re := by
  rw [finiteBoxCorrelation_re_eq_mean_square]
  exact Finset.expect_nonneg (fun _ _ => Finset.expect_nonneg (fun _ _ => sq_nonneg _))

theorem norm_weighted_expect_sq_le {X : Type*} [Fintype X] [Nonempty X]
    (a f : X → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1) :
    ‖𝔼 x, a x * f x‖ ^ 2 ≤ 𝔼 x, ‖f x‖ ^ 2 := by
  have hcs := norm_expect_mul_star_sq_le a (fun x => star (f x))
  simp only [star_star, norm_star] at hcs
  have ha2 : (𝔼 x, ‖a x‖ ^ 2) ≤ 1 := by
    exact (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (ha x) 2)).trans_eq (by simp)
  exact hcs.trans ((mul_le_mul_of_nonneg_right ha2
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _))).trans_eq (one_mul _))

theorem norm_weighted_pair_mean_pow_four_le_box {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : X → Y → ℂ) (a : X → ℂ) (b : Y → ℂ)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ y, ‖b y‖ ≤ 1) :
    ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 4 ≤ (finiteBoxCorrelation F).re := by
  let m : ℂ := 𝔼 x, 𝔼 x', a x * star (a x') * (𝔼 y, F x y * star (F x' y))
  have hleft : (𝔼 y, b y * (𝔼 x, F x y * a x)) = 𝔼 x, 𝔼 y, F x y * a x * b y := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    ring
  have hright : (𝔼 x, 𝔼 x', 𝔼 y, (F x y * a x) * star (F x' y * a x')) = m := by
    dsimp [m]
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro x' _
    apply Finset.expect_congr rfl
    intro y _
    rw [map_mul]
    ring
  have hfirst : ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2 ≤ m.re := by
    simpa only [hleft, hright, one_pow, one_mul] using
      finite_family_cauchy_schwarz_re b (fun x y => F x y * a x) hb
  have hsecond : ‖m‖ ^ 2 ≤ 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
    have hh := norm_weighted_expect_sq_le
      (fun u : X × X => a u.1 * star (a u.2))
      (fun u : X × X => 𝔼 y, F u.1 y * star (F u.2 y)) (fun u => by
        rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ha _)).trans (ha _))
    simpa only [← Finset.univ_product_univ, Finset.expect_product, m] using hh
  have hm : 0 ≤ m.re := (sq_nonneg _).trans hfirst
  calc
    _ = (‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2) ^ 2 := by ring
    _ ≤ m.re ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ hm (Complex.re_le_norm m) 2
    _ ≤ _ := hsecond.trans_eq (finiteBoxCorrelation_re_eq_mean_square F).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def iteratedBoxDifference {Z : Type*} :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → ℂ) →
      (∀ i, X i) → (∀ i, X i) → Z → ℂ
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => iteratedBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z * star (F (Fin.cons (v 0) x) z))
      (Fin.tail u) (Fin.tail v) z

theorem iterated_box_cauchy_schwarz (n : ℕ) {X : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    {Z : Type*} [Fintype Z] [Nonempty Z] (F : (∀ i, X i) → Z → ℂ) :
    ‖𝔼 x, 𝔼 z, F x z‖^(2^n) ≤
      𝔼 u, 𝔼 v, ‖𝔼 z, iteratedBoxDifference n F u v z‖ := by
  induction n with
  | zero => simp only [pow_zero, pow_one, expect_empty_tuple, iteratedBoxDifference, le_refl]
  | succ n ih =>
    let G := fun a b (x : ∀ i : Fin n, X i.succ) z =>
      F (Fin.cons a x) z * star (F (Fin.cons b x) z)
    have hcs : ‖𝔼 x, 𝔼 z, F x z‖^2 ≤
        𝔼 a : X 0, 𝔼 b : X 0, ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖ := by
      rw [expect_dependent_fin_cons]
      have h := norm_mean_first_difference
        (fun (a : X 0) (p : (∀ i : Fin n, X i.succ) × Z) => F (Fin.cons a p.1) p.2)
      simpa only [expect_prod_split] using h
    calc
      _ = (‖𝔼 x, 𝔼 z, F x z‖^2)^(2^n) := by rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ (𝔼 a : X 0, 𝔼 b : X 0,
          ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖)^(2^n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 a : X 0, 𝔼 b : X 0,
          ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖^(2^n) :=
        expect_double_pow_two_pow_le n _ (fun _ _ => norm_nonneg _)
      _ ≤ 𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
          𝔼 v : ∀ i : Fin n, X i.succ, ‖𝔼 z, iteratedBoxDifference n (G a b) u v z‖ := by
        apply Finset.expect_le_expect
        intro a _
        apply Finset.expect_le_expect
        intro b _
        exact ih (G a b)
      _ = _ := by
        rw [expect_two_dependent_fin_cons]
        rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxSlice {X : Type*} (a z : Fin 2 → X) : Fin 4 → X := ![z 0, a 0, z 1, a 1]

def boxSliceEquiv (X : Type*) : ((Fin 2 → X) × (Fin 2 → X)) ≃ (Fin 4 → X) where
  toFun p := boxSlice p.1 p.2
  invFun x := (![x 1, x 3], ![x 0, x 2])
  left_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem expect_boxSlice {X M : Type*} [Fintype X] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 4 → X) → M) :
    (𝔼 x, F x) = 𝔼 a : Fin 2 → X, 𝔼 z : Fin 2 → X, F (boxSlice a z) := by
  calc
    _ = 𝔼 p : (Fin 2 → X) × (Fin 2 → X), F (boxSlice p.1 p.2) :=
      (Fintype.expect_equiv (boxSliceEquiv X) _ F (fun _ => rfl)).symm
    _ = _ := by
      simpa using (Finset.expect_product' Finset.univ Finset.univ
        (fun a z => F (boxSlice a z)))

noncomputable def boxKernel {X : Type*} (K : X → X → ℂ) (x : Fin 4 → X) : ℂ :=
  K (x 0) (x 2) * star (K (x 1) (x 2)) * star (K (x 0) (x 3)) * K (x 1) (x 3)

noncomputable def boxAnchorFactor {X : Type*} (K : X → X → ℂ)
    (a z : Fin 2 → X) : ℂ :=
  star (K (a 0) (z 1)) * star (K (z 0) (a 1)) * K (a 0) (a 1)

theorem boxKernel_slice {X : Type*} (K : X → X → ℂ) (a z : Fin 2 → X) :
    boxKernel K (boxSlice a z) = K (z 0) (z 1) * boxAnchorFactor K a z := by
  simp [boxKernel, boxSlice, boxAnchorFactor, mul_assoc]

theorem boxKernel_mean {X : Type*} [Fintype X] (K : X → X → ℂ) :
    (𝔼 x : Fin 4 → X, boxKernel K x) = finiteBoxCorrelation K := by
  simp_rw [expect_fin_cons]
  unfold finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro b _
  change (𝔼 _ : Fin 0 → X, K x y * star (K a y) * star (K x b) * K a b) = _
  rw [Fintype.expect_const]

theorem boxAnchorFactor_norm_le_one {X : Type*} (K : X → X → ℂ)
    (hK : ∀ x y, ‖K x y‖ ≤ 1) (a z : Fin 2 → X) : ‖boxAnchorFactor K a z‖ ≤ 1 := by
  simp only [boxAnchorFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (hK _ _)).trans (hK _ _))).trans (hK _ _)

theorem boxAnchorFactor_mean_square {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → ℂ) (hK : ∀ x y, ‖K x y‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbias : δ ≤ (finiteBoxCorrelation K).re) :
    δ ^ 2 ≤ 𝔼 a : Fin 2 → X, 𝔼 z : Fin 2 → X, ‖boxAnchorFactor K a z‖ ^ 2 := by
  calc
    _ ≤ ‖finiteBoxCorrelation K‖ ^ 2 :=
      pow_le_pow_left₀ hδ (hbias.trans (Complex.re_le_norm _)) 2
    _ ≤ 𝔼 x : Fin 4 → X, ‖boxKernel K x‖ ^ 2 := by
      rw [← boxKernel_mean]
      exact norm_expect_sq_le_expect_norm_sq _
    _ = 𝔼 a : Fin 2 → X, 𝔼 z : Fin 2 → X, ‖boxKernel K (boxSlice a z)‖ ^ 2 :=
      expect_boxSlice _
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro a _
      apply Finset.expect_le_expect
      intro z _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [boxKernel_slice, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hK _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteTripleBoxCorrelation {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (F : X → Y → Z → ℂ) : ℂ :=
  𝔼 x, 𝔼 x', finiteBoxCorrelation (fun y z => F x y z * star (F x' y z))

theorem finiteTripleBoxCorrelation_re_nonneg {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (F : X → Y → Z → ℂ) :
    0 ≤ (finiteTripleBoxCorrelation F).re := by
  simp only [finiteTripleBoxCorrelation, expect_re]
  exact Finset.expect_nonneg (fun _ _ => Finset.expect_nonneg (fun _ _ =>
    finiteBoxCorrelation_re_nonneg _))

theorem norm_pairwise_weighted_mean_pow_eight_le_box {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y] [Nonempty Z]
    (F : X → Y → Z → ℂ) (A : X → Y → ℂ) (B : Y → Z → ℂ) (D : X → Z → ℂ)
    (hA : ∀ x y, ‖A x y‖ ≤ 1) (hB : ∀ y z, ‖B y z‖ ≤ 1)
    (hD : ∀ x z, ‖D x z‖ ≤ 1) :
    ‖𝔼 x, 𝔼 y, 𝔼 z, F x y z * A x y * B y z * D x z‖ ^ 8 ≤
      (finiteTripleBoxCorrelation F).re := by
  let v (x : X) (u : Y × Z) := F x u.1 u.2 * A x u.1 * D x u.2
  let G (x x' : X) (y : Y) (z : Z) := F x y z * star (F x' y z)
  let A₂ (x x' : X) (y : Y) := A x y * star (A x' y)
  let D₂ (x x' : X) (z : Z) := D x z * star (D x' z)
  let M (x x' : X) := 𝔼 y, 𝔼 z, G x x' y z * A₂ x x' y * D₂ x x' z
  let m : ℂ := 𝔼 x, 𝔼 x', M x x'
  have hleft : (𝔼 u : Y × Z, B u.1 u.2 * (𝔼 x, v x u)) =
      𝔼 x, 𝔼 y, 𝔼 z, F x y z * A x y * B y z * D x z := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    simp_rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    apply Finset.expect_congr rfl
    intro z _
    dsimp only [v]
    ring
  have hright : (𝔼 x, 𝔼 x', 𝔼 u : Y × Z, v x u * star (v x' u)) = m := by
    dsimp only [m, M]
    simp_rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro x' _
    apply Finset.expect_congr rfl
    intro y _
    apply Finset.expect_congr rfl
    intro z _
    simp only [v, G, A₂, D₂, star_mul]
    ring
  have hfirst : ‖𝔼 x, 𝔼 y, 𝔼 z, F x y z * A x y * B y z * D x z‖ ^ 2 ≤ m.re := by
    simpa only [hleft, hright, one_pow, one_mul] using
      finite_family_cauchy_schwarz_re (fun u : Y × Z => B u.1 u.2) v (fun u => hB u.1 u.2)
  have hnorm : ‖m‖ ≤ 𝔼 x, 𝔼 x', ‖M x x'‖ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact Finset.expect_le_expect (fun x _ => RCLike.norm_expect_le (K := ℂ))
  have hpower : ‖m‖ ^ 4 ≤ 𝔼 x, 𝔼 x', ‖M x x'‖ ^ 4 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 4).trans
      (expect_double_pow_two_pow_le 2 (fun x x' => ‖M x x'‖) (fun _ _ => norm_nonneg _))
  have hpair (x x' : X) : ‖M x x'‖ ^ 4 ≤ (finiteBoxCorrelation (G x x')).re := by
    exact norm_weighted_pair_mean_pow_four_le_box (G x x') (A₂ x x') (D₂ x x')
      (fun y => by
        simp only [A₂, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hA x y)).trans (hA x' y))
      (fun z => by
        simp only [D₂, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hD x z)).trans (hD x' z))
  calc
    _ = (‖𝔼 x, 𝔼 y, 𝔼 z, F x y z * A x y * B y z * D x z‖ ^ 2) ^ 4 := by ring
    _ ≤ ‖m‖ ^ 4 := pow_le_pow_left₀ (sq_nonneg _) (hfirst.trans (Complex.re_le_norm m)) 4
    _ ≤ 𝔼 x, 𝔼 x', ‖M x x'‖ ^ 4 := hpower
    _ ≤ _ := by
      simp only [finiteTripleBoxCorrelation, expect_re]
      exact Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun x' _ => hpair x x'))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def additiveBoxDifference {Z R : Type*} [AddGroup R] :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → R) →
      (∀ i, X i) → (∀ i, X i) → Z → R
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => additiveBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z - F (Fin.cons (v 0) x) z)
      (Fin.tail u) (Fin.tail v) z

theorem additiveBoxDifference_sum {Z R J : Type*} [AddCommGroup R]
    (n : ℕ) {X : Fin n → Type*} (S : Finset J)
    (F : J → (∀ i, X i) → Z → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x z => ∑ j ∈ S, F j x z) u v z =
      ∑ j ∈ S, additiveBoxDifference n (F j) u v z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← Finset.sum_sub_distrib]
    exact ih (fun j x z => F j (Fin.cons (u 0) x) z - F j (Fin.cons (v 0) x) z)
      (Fin.tail u) (Fin.tail v)

theorem additiveBoxDifference_product {Z R : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (a : Z → R) (f : ∀ i, X i → R)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x z => a z * ∏ i, f i (x i)) u v z =
      a z * ∏ i, (f i (u i)-f i (v i)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference]
    have he : (fun x z =>
        a z * ∏ i, f i (Fin.cons (u 0) x i) - a z * ∏ i, f i (Fin.cons (v 0) x i)) =
        (fun (x : ∀ i : Fin n, X i.succ) z =>
          (a z*(f 0 (u 0)-f 0 (v 0))) * ∏ i, f i.succ (x i)) := by
      funext x z
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    rw [he, ih]
    simp only [Fin.prod_univ_succ, Fin.tail_def]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_box_anchor_approximation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → ℂ) (hK : ∀ x y, ‖K x y‖ ≤ 1) (F : (Fin 4 → X) → ℂ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hbias : δ ≤ (finiteBoxCorrelation K).re)
    (herr : (𝔼 x : Fin 4 → X, ‖boxKernel K x - F x‖) ≤ ε) :
    ∃ a : Fin 2 → X,
      δ ^ 2 / 2 ≤ (𝔼 z : Fin 2 → X, ‖boxAnchorFactor K a z‖ ^ 2) ∧
      δ ^ 2 / 2 ≤ (𝔼 z : Fin 2 → X, ‖K (z 0) (z 1) * boxAnchorFactor K a z‖ ^ 2) ∧
      (𝔼 z : Fin 2 → X,
        ‖K (z 0) (z 1) * boxAnchorFactor K a z - F (boxSlice a z)‖) ≤ 2 * ε / δ ^ 2 := by
  let A := fun a : Fin 2 → X =>
    𝔼 z : Fin 2 → X, ‖K (z 0) (z 1) * boxAnchorFactor K a z‖ ^ 2
  let B := fun a : Fin 2 → X => 𝔼 z : Fin 2 → X, ‖boxKernel K (boxSlice a z) - F (boxSlice a z)‖
  have hA : ∀ a, A a ≤ 1 := by
    intro a
    have hnorm (z : Fin 2 → X) : ‖K (z 0) (z 1) * boxAnchorFactor K a z‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hK _ _)).trans
        (boxAnchorFactor_norm_le_one K hK a z)
    exact (Finset.expect_le_expect (fun z _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hnorm z) 2)).trans_eq (by simp)
  have hB : ∀ a, 0 ≤ B a := fun a => Finset.expect_nonneg (fun z _ => norm_nonneg _)
  have hmass : δ ^ 2 ≤ 𝔼 a, A a := by
    calc
      _ ≤ ‖finiteBoxCorrelation K‖ ^ 2 :=
        pow_le_pow_left₀ hδ.le (hbias.trans (Complex.re_le_norm _)) 2
      _ ≤ 𝔼 x : Fin 4 → X, ‖boxKernel K x‖ ^ 2 := by
        rw [← boxKernel_mean]
        exact norm_expect_sq_le_expect_norm_sq _
      _ = _ := by simpa only [A, boxKernel_slice] using expect_boxSlice (fun x => ‖boxKernel K x‖ ^ 2)
  have herror : (𝔼 a, B a) ≤ ε := by
    rw [expect_boxSlice] at herr
    exact herr
  obtain ⟨a, ha, he⟩ := exists_mass_error_point A B (sq_pos_of_pos hδ) hε hA hB hmass herror
  refine ⟨a, ha.trans ?_, ha, by simpa only [B, boxKernel_slice] using he⟩
  apply Finset.expect_le_expect
  intro z _
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hK _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_box_anchor_correlation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → ℂ) :
    ∃ a : Fin 2 → X, (finiteBoxCorrelation K).re ≤
      ‖𝔼 z : Fin 2 → X, K (z 0) (z 1) * boxAnchorFactor K a z‖ := by
  have hmean : (finiteBoxCorrelation K).re =
      𝔼 a : Fin 2 → X, (𝔼 z : Fin 2 → X,
        K (z 0) (z 1) * boxAnchorFactor K a z).re := by
    rw [← boxKernel_mean, expect_boxSlice, expect_re]
    simp_rw [boxKernel_slice]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

end Erdos3

end

section

namespace Erdos3

theorem additiveBoxDifference_hom {Z R S : Type*} [AddGroup R] [AddGroup S]
    (L : R →+ S) (n : ℕ) {X : Fin n → Type*}
    (F : (∀ i, X i) → Z → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => L (F x t)) u v z =
      L (additiveBoxDifference n F u v z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← map_sub]
    exact ih (fun x t => F (Fin.cons (u 0) x) t - F (Fin.cons (v 0) x) t)
      (Fin.tail u) (Fin.tail v)

end Erdos3

end

end OAI
