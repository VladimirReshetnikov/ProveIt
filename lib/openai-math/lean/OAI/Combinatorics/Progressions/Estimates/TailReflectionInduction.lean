import OAI.Combinatorics.Progressions.Geometry.BoxCornerMean

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_family_reflected_correlation
    {T G : Type*} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (F : T → G → G → ℂ) (b₁ b₂ b₃ : T → G → ℂ)
    (hb₁ : ∀ t x, ‖b₁ t x‖ ≤ 1) (hb₂ : ∀ t y, ‖b₂ t y‖ ≤ 1)
    (hb₃ : ∀ t z, ‖b₃ t z‖ ≤ 1) :
    ∃ (z : G) (b : T → G → ℂ), (∀ t y, ‖b t y‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y)‖ ^ 2 ≤
        (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
          b t y * star (b t y')).re := by
  let B (z : G) (t : T) (y : G) := b₂ t y * star (b₃ t (z - y))
  let v (y : G) (u : T × G) := F u.1 y u.2 * b₂ u.1 y * b₃ u.1 (u.2 + y)
  have hleft : (𝔼 u : T × G, b₁ u.1 u.2 * (𝔼 y, v y u)) =
      𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y) := by
    simp_rw [expect_prod_split, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    dsimp only [v]
    ring
  have hchange (t : T) : (𝔼 y, 𝔼 y', 𝔼 x,
      v y (t, x) * star (v y' (t, x))) =
      𝔼 z, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y') := by
    calc
      _ = 𝔼 y, 𝔼 y', 𝔼 z, F t y (z - y - y') * star (F t y' (z - y - y')) *
          B z t y * star (B z t y') := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro y' _
        apply Fintype.expect_equiv (Equiv.addRight (y + y'))
        intro x
        have h₁ : x + (y + y') - y = x + y' := by abel
        have h₂ : x + (y + y') - y' = x + y := by abel
        simp only [Equiv.coe_addRight, v, B, h₁, h₂, add_sub_cancel_right,
          star_mul, star_star]
        ring
      _ = 𝔼 y, 𝔼 z, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
          B z t y * star (B z t y') := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hright : (𝔼 y, 𝔼 y', 𝔼 u : T × G, v y u * star (v y' u)) =
      𝔼 z, 𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y') := by
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 y, 𝔼 t, 𝔼 y', 𝔼 x, v y (t, x) * star (v y' (t, x)) := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 y, 𝔼 y', 𝔼 x, v y (t, x) * star (v y' (t, x)) :=
        Finset.expect_comm _ _ _
      _ = _ := by simp_rw [hchange]; exact Finset.expect_comm _ _ _
  have hcs := finite_family_cauchy_schwarz_re (fun u : T × G => b₁ u.1 u.2)
    v (fun u => hb₁ u.1 u.2)
  simp only [one_pow, one_mul, hleft, hright] at hcs
  rw [expect_re, Fintype.expect_eq_sum_div_card (fun z : G =>
    (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
      B z t y * star (B z t y')).re)] at hcs
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ _z : G,
      ‖𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y)‖ ^ 2) ≤
      ∑ z : G, (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y')).re := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ hcard).mp hcs
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨z, B z, ?_, hz⟩
  intro t y
  simp only [B, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb₂ t y)).trans (hb₃ t _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_reflected_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    (K : G → G → G → ℂ) (f : G → ℂ) (A B D : G → G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hA : ∀ h n, ‖A h n‖ ≤ 1)
    (hB : ∀ n k, ‖B n k‖ ≤ 1) (hD : ∀ h k, ‖D h k‖ ≤ 1) :
    ∃ (z : G) (b : (G × G) → G → ℂ), (∀ t h, ‖b t h‖ ≤ 1) ∧
      ‖𝔼 k, 𝔼 h, 𝔼 n, f (n + h + k) * K h n k * A h n * B n k * D h k‖ ^ 4 ≤
        (𝔼 t : G × G, 𝔼 h, 𝔼 h',
          (K h (z - h - h') t.1 * star (K h (z - h - h') t.2)) *
            star (K h' (z - h - h') t.1 * star (K h' (z - h - h') t.2)) *
              b t h * star (b t h')).re := by
  let v (k : G) (u : G × G) :=
    f (u.2 + u.1 + k) * K u.1 u.2 k * B u.2 k * D u.1 k
  let F (t : G × G) (h n : G) := K h n t.1 * star (K h n t.2)
  let b₁ (t : G × G) (n : G) := B n t.1 * star (B n t.2)
  let b₂ (t : G × G) (h : G) := D h t.1 * star (D h t.2)
  let b₃ (t : G × G) (w : G) := f (w + t.1) * star (f (w + t.2))
  let m := 𝔼 t, 𝔼 n, 𝔼 h, F t h n * b₁ t n * b₂ t h * b₃ t (n + h)
  have hleft : (𝔼 u : G × G, A u.1 u.2 * (𝔼 k, v k u)) =
      𝔼 k, 𝔼 h, 𝔼 n, f (n + h + k) * K h n k * A h n * B n k * D h k := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    simp_rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro k _
    apply Finset.expect_congr rfl
    intro h _
    apply Finset.expect_congr rfl
    intro n _
    dsimp only [v]
    ring
  have hright : (𝔼 k, 𝔼 k', 𝔼 u : G × G, v k u * star (v k' u)) = m := by
    dsimp only [m]
    simp_rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro k _
    apply Finset.expect_congr rfl
    intro k' _
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro n _
    apply Finset.expect_congr rfl
    intro h _
    simp only [v, F, b₁, b₂, b₃, star_mul]
    ring
  have hfirst := finite_family_cauchy_schwarz_re (fun u : G × G => A u.1 u.2)
    v (fun u => hA u.1 u.2)
  simp only [hleft, hright, one_pow, one_mul] at hfirst
  obtain ⟨z, b, hb, hsecond⟩ := exists_family_reflected_correlation F b₁ b₂ b₃
    (fun t n => by
      simp only [b₁, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hB n _)).trans (hB n _))
    (fun t h => by
      simp only [b₂, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hD h _)).trans (hD h _))
    (fun t w => by
      simp only [b₃, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hf _))
  refine ⟨z, b, hb, ?_⟩
  calc
    _ = (‖𝔼 k, 𝔼 h, 𝔼 n,
        f (n + h + k) * K h n k * A h n * B n k * D h k‖ ^ 2) ^ 2 := by ring
    _ ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ (sq_nonneg _) (hfirst.trans (Complex.re_le_norm m)) 2
    _ ≤ _ := hsecond

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_family_cubic_reflected_correlation
    {T G : Type*} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → G → ℂ) (f : T → G → ℂ) (A B D : T → G → G → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t h n, ‖A t h n‖ ≤ 1)
    (hB : ∀ t n k, ‖B t n k‖ ≤ 1) (hD : ∀ t h k, ‖D t h k‖ ≤ 1) :
    ∃ (z : G) (b : (T × (G × G)) → G → ℂ), (∀ t h, ‖b t h‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 k, 𝔼 h, 𝔼 n,
        f t (n + h + k) * K t h n k * A t h n * B t n k * D t h k‖ ^ 4 ≤
        (𝔼 t : T × (G × G), 𝔼 h, 𝔼 h',
          (K t.1 h (z - h - h') t.2.1 * star (K t.1 h (z - h - h') t.2.2)) *
            star (K t.1 h' (z - h - h') t.2.1 * star (K t.1 h' (z - h - h') t.2.2)) *
              b t h * star (b t h')).re := by
  let v (k : G) (u : T × (G × G)) :=
    f u.1 (u.2.2 + u.2.1 + k) * K u.1 u.2.1 u.2.2 k * B u.1 u.2.2 k * D u.1 u.2.1 k
  let F (t : T × (G × G)) (h n : G) := K t.1 h n t.2.1 * star (K t.1 h n t.2.2)
  let b₁ (t : T × (G × G)) (n : G) := B t.1 n t.2.1 * star (B t.1 n t.2.2)
  let b₂ (t : T × (G × G)) (h : G) := D t.1 h t.2.1 * star (D t.1 h t.2.2)
  let b₃ (t : T × (G × G)) (w : G) := f t.1 (w + t.2.1) * star (f t.1 (w + t.2.2))
  let m := 𝔼 t, 𝔼 n, 𝔼 h, F t h n * b₁ t n * b₂ t h * b₃ t (n + h)
  have hleft : (𝔼 u : T × (G × G), A u.1 u.2.1 u.2.2 * (𝔼 k, v k u)) =
      𝔼 t, 𝔼 k, 𝔼 h, 𝔼 n,
        f t (n + h + k) * K t h n k * A t h n * B t n k * D t h k := by
    simp_rw [Finset.mul_expect, expect_prod_split]
    apply Finset.expect_congr rfl
    intro t _
    calc
      _ = 𝔼 h, 𝔼 k, 𝔼 n, A t h n * v k (t, h, n) := by
        apply Finset.expect_congr rfl
        intro h _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 k, 𝔼 h, 𝔼 n, A t h n * v k (t, h, n) := Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro k _
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro n _
        dsimp only [v]
        ring
  have hright : (𝔼 k, 𝔼 k', 𝔼 u : T × (G × G), v k u * star (v k' u)) = m := by
    dsimp only [m]
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 k, 𝔼 t, 𝔼 k', 𝔼 h, 𝔼 n, v k (t, h, n) * star (v k' (t, h, n)) := by
        apply Finset.expect_congr rfl
        intro k _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 k, 𝔼 k', 𝔼 h, 𝔼 n, v k (t, h, n) * star (v k' (t, h, n)) :=
        Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro t _
        apply Finset.expect_congr rfl
        intro k _
        apply Finset.expect_congr rfl
        intro k' _
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro n _
        apply Finset.expect_congr rfl
        intro h _
        simp only [v, F, b₁, b₂, b₃, star_mul]
        ring
  have hfirst := finite_family_cauchy_schwarz_re
    (fun u : T × (G × G) => A u.1 u.2.1 u.2.2) v (fun u => hA u.1 u.2.1 u.2.2)
  simp only [hleft, hright, one_pow, one_mul] at hfirst
  obtain ⟨z, b, hb, hsecond⟩ := exists_family_reflected_correlation F b₁ b₂ b₃
    (fun t n => by
      simp only [b₁, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hB _ _ _)).trans (hB _ _ _))
    (fun t h => by
      simp only [b₂, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hD _ _ _)).trans (hD _ _ _))
    (fun t w => by
      simp only [b₃, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _ _)).trans (hf _ _))
  refine ⟨z, b, hb, ?_⟩
  calc
    _ = (‖𝔼 t, 𝔼 k, 𝔼 h, 𝔼 n,
        f t (n + h + k) * K t h n k * A t h n * B t n k * D t h k‖ ^ 2) ^ 2 := by ring
    _ ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ (sq_nonneg _) (hfirst.trans (Complex.re_le_norm m)) 2
    _ ≤ _ := hsecond

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticReflectionKernel {G : Type*} (K : G → G → G → G → ℂ)
    (t : (G × G) × (G × G)) (h n : G) : ℂ :=
  (K h n t.2.1 t.1.1 * star (K h n t.2.1 t.1.2)) *
    star (K h n t.2.2 t.1.1 * star (K h n t.2.2 t.1.2))

theorem exists_quartic_reflected_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    (K : G → G → G → G → ℂ) (f : G → ℂ) (A₀ A₁ A₂ A₃ : G → G → G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hA₀ : ∀ n k l, ‖A₀ n k l‖ ≤ 1)
    (hA₁ : ∀ h k l, ‖A₁ h k l‖ ≤ 1) (hA₂ : ∀ h n l, ‖A₂ h n l‖ ≤ 1)
    (hA₃ : ∀ h n k, ‖A₃ h n k‖ ≤ 1) :
    ∃ (z : G) (b : ((G × G) × (G × G)) → G → ℂ), (∀ t h, ‖b t h‖ ≤ 1) ∧
      ‖𝔼 l, 𝔼 k, 𝔼 h, 𝔼 n,
        f (n + h + k + l) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k‖ ^ 8 ≤
        (𝔼 t : (G × G) × (G × G), 𝔼 h, 𝔼 h',
          quarticReflectionKernel K t h (z - h - h') *
            star (quarticReflectionKernel K t h' (z - h - h')) * b t h * star (b t h')).re := by
  let v (l : G) (u : G × (G × G)) :=
    f (u.2.2 + u.2.1 + u.1 + l) * K u.2.1 u.2.2 u.1 l *
      A₀ u.2.2 u.1 l * A₁ u.2.1 u.1 l * A₂ u.2.1 u.2.2 l
  let K' (t : G × G) (h n k : G) := K h n k t.1 * star (K h n k t.2)
  let f' (t : G × G) (w : G) := f (w + t.1) * star (f (w + t.2))
  let A (t : G × G) (h n : G) := A₂ h n t.1 * star (A₂ h n t.2)
  let B (t : G × G) (n k : G) := A₀ n k t.1 * star (A₀ n k t.2)
  let D (t : G × G) (h k : G) := A₁ h k t.1 * star (A₁ h k t.2)
  let m := 𝔼 t, 𝔼 k, 𝔼 h, 𝔼 n,
    f' t (n + h + k) * K' t h n k * A t h n * B t n k * D t h k
  have hleft : (𝔼 u : G × (G × G), A₃ u.2.1 u.2.2 u.1 * (𝔼 l, v l u)) =
      𝔼 l, 𝔼 k, 𝔼 h, 𝔼 n,
        f (n + h + k + l) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    simp_rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro l _
    apply Finset.expect_congr rfl
    intro k _
    apply Finset.expect_congr rfl
    intro h _
    apply Finset.expect_congr rfl
    intro n _
    dsimp only [v]
    ring
  have hright : (𝔼 l, 𝔼 l', 𝔼 u : G × (G × G), v l u * star (v l' u)) = m := by
    dsimp only [m]
    simp_rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro l _
    apply Finset.expect_congr rfl
    intro l' _
    apply Finset.expect_congr rfl
    intro k _
    apply Finset.expect_congr rfl
    intro h _
    apply Finset.expect_congr rfl
    intro n _
    simp only [v, K', f', A, B, D, star_mul]
    ring
  have hfirst := finite_family_cauchy_schwarz_re
    (fun u : G × (G × G) => A₃ u.2.1 u.2.2 u.1) v (fun u => hA₃ u.2.1 u.2.2 u.1)
  simp only [hleft, hright, one_pow, one_mul] at hfirst
  obtain ⟨z, b, hb, hsecond⟩ := exists_family_cubic_reflected_correlation K' f' A B D
    (fun t w => by
      simp only [f', norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hf _))
    (fun t h n => by
      simp only [A, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hA₂ _ _ _)).trans (hA₂ _ _ _))
    (fun t n k => by
      simp only [B, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hA₀ _ _ _)).trans (hA₀ _ _ _))
    (fun t h k => by
      simp only [D, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hA₁ _ _ _)).trans (hA₁ _ _ _))
  refine ⟨z, b, hb, ?_⟩
  calc
    _ = (‖𝔼 l, 𝔼 k, 𝔼 h, 𝔼 n,
        f (n + h + k + l) * K h n k l * A₀ n k l * A₁ h k l * A₂ h n l * A₃ h n k‖ ^ 2) ^ 4 := by ring
    _ ≤ ‖m‖ ^ 4 := pow_le_pow_left₀ (sq_nonneg _) (hfirst.trans (Complex.re_le_norm m)) 4
    _ ≤ _ := hsecond

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

structure TailReflectionData (n : ℕ) (T G : Type*) where
  kernel : T → G → G → (Fin n → G) → ℂ
  signal : T → G → ℂ
  leftWeight : T → G → (Fin n → G) → ℂ
  rightWeight : T → G → (Fin n → G) → ℂ
  tailWeight : T → Fin n → G → G → (Fin n → G) → ℂ
  signal_norm : ∀ t x, ‖signal t x‖ ≤ 1
  left_norm : ∀ t x v, ‖leftWeight t x v‖ ≤ 1
  right_norm : ∀ t x v, ‖rightWeight t x v‖ ≤ 1
  tail_norm : ∀ t i h m v, ‖tailWeight t i h m v‖ ≤ 1
  tail_misses : ∀ t i h m, MissesBoxCoordinate (tailWeight t i h m) i

namespace TailReflectionData

noncomputable def correlation {n : ℕ} {T G : Type*} [Fintype T]
    [AddCommGroup G] [Fintype G] (D : TailReflectionData n T G) : ℂ :=
  𝔼 t, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
    D.signal t (m + h + ∑ i, v i) * D.kernel t h m v *
      D.leftWeight t m v * D.rightWeight t h v * ∏ i, D.tailWeight t i h m v

noncomputable def pair {n : ℕ} {T G : Type*} [AddCommGroup G]
    (D : TailReflectionData (n + 1) T G) : TailReflectionData n (T × (G × G)) G where
  kernel t h m v := D.kernel t.1 h m (Fin.cons t.2.1 v) *
    star (D.kernel t.1 h m (Fin.cons t.2.2 v))
  signal t w := D.signal t.1 (w + t.2.1) * star (D.signal t.1 (w + t.2.2))
  leftWeight t m v := D.leftWeight t.1 m (Fin.cons t.2.1 v) *
    star (D.leftWeight t.1 m (Fin.cons t.2.2 v))
  rightWeight t h v := D.rightWeight t.1 h (Fin.cons t.2.1 v) *
    star (D.rightWeight t.1 h (Fin.cons t.2.2 v))
  tailWeight t i h m v := boxTailTests (fun j => D.tailWeight t.1 j h m) t.2.1 t.2.2 i v
  signal_norm t w := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.signal_norm _ _)).trans (D.signal_norm _ _)
  left_norm t m v := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.left_norm _ _ _)).trans (D.left_norm _ _ _)
  right_norm t h v := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.right_norm _ _ _)).trans (D.right_norm _ _ _)
  tail_norm t i h m v := boxTailTests_norm (fun j => D.tailWeight t.1 j h m)
    (fun j x => D.tail_norm t.1 j h m x) t.2.1 t.2.2 i v
  tail_misses t i h m := boxTailTests_misses (fun j => D.tailWeight t.1 j h m)
    (fun j => D.tail_misses t.1 j h m) t.2.1 t.2.2 i

noncomputable def reflectedKernel {n : ℕ} {T G : Type*} (D : TailReflectionData n T G)
    (t : T) (u v : Fin n → G) (h m : G) : ℂ :=
  iteratedBoxDifference n (fun x (a : G × G) => D.kernel t a.1 a.2 x) u v (h, m)

theorem reflectedKernel_cons {n : ℕ} {T G : Type*} [AddCommGroup G]
    (D : TailReflectionData (n + 1) T G) (t : T) (a b : G)
    (u v : Fin n → G) (h m : G) :
    D.reflectedKernel t (Fin.cons a u) (Fin.cons b v) h m =
      D.pair.reflectedKernel (t, (a, b)) u v h m := by
  simp only [reflectedKernel, iteratedBoxDifference, Fin.cons_zero, Fin.tail_cons, pair]

end TailReflectionData

end Erdos3

end

section

namespace Erdos3.TailReflectionData

open scoped BigOperators Classical

theorem correlation_square_le_pair {n : ℕ} {T G : Type*} [Fintype T] [Nonempty T]
    [AddCommGroup G] [Fintype G] (D : TailReflectionData (n + 1) T G) :
    ‖D.correlation‖ ^ 2 ≤ D.pair.correlation.re := by
  let C (q : T × ((Fin n → G) × (G × G))) : ℂ :=
    D.tailWeight q.1 0 q.2.2.2 q.2.2.1 (Fin.cons 0 q.2.1)
  let V (a : G) (q : T × ((Fin n → G) × (G × G))) : ℂ :=
    D.signal q.1 (q.2.2.1 + q.2.2.2 + ∑ i, (Fin.cons a q.2.1) i) *
      D.kernel q.1 q.2.2.2 q.2.2.1 (Fin.cons a q.2.1) *
      D.leftWeight q.1 q.2.2.1 (Fin.cons a q.2.1) *
      D.rightWeight q.1 q.2.2.2 (Fin.cons a q.2.1) *
      ∏ i : Fin n, D.tailWeight q.1 i.succ q.2.2.2 q.2.2.1 (Fin.cons a q.2.1)
  have hleft : (𝔼 q, C q * (𝔼 a, V a q)) = D.correlation := by
    unfold correlation
    simp_rw [expect_dependent_fin_cons, Finset.mul_expect]
    rw [Finset.expect_comm]
    simp_rw [expect_prod_split]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro a _
    apply Finset.expect_congr rfl
    intro v _
    apply Finset.expect_congr rfl
    intro m _
    apply Finset.expect_congr rfl
    intro h _
    dsimp only [C, V]
    rw [Fin.prod_univ_succ,
      missesBoxCoordinate_head (D.tail_misses t 0 h m) a 0 v]
    ring
  have hright : (𝔼 a, 𝔼 b, 𝔼 q, V a q * star (V b q)) = D.pair.correlation := by
    unfold correlation
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 a, 𝔼 t, 𝔼 b, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
          V a (t, (v, (m, h))) * star (V b (t, (v, (m, h)))) := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 a, 𝔼 b, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
          V a (t, (v, (m, h))) * star (V b (t, (v, (m, h)))) :=
        Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro t _
        apply Finset.expect_congr rfl
        intro a _
        apply Finset.expect_congr rfl
        intro b _
        apply Finset.expect_congr rfl
        intro v _
        apply Finset.expect_congr rfl
        intro m _
        apply Finset.expect_congr rfl
        intro h _
        dsimp only [V, pair]
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, boxTailTests,
          star_mul, star_prod, Finset.prod_mul_distrib]
        have ha : m + h + (a + ∑ i, v i) = (m + h + ∑ i, v i) + a := by abel
        have hb : m + h + (b + ∑ i, v i) = (m + h + ∑ i, v i) + b := by abel
        rw [ha, hb]
        ring
  have hcs := finite_family_cauchy_schwarz_re C V
    (fun q => D.tail_norm q.1 0 q.2.2.2 q.2.2.1 (Fin.cons 0 q.2.1))
  simpa only [hleft, hright, one_pow, one_mul] using hcs

end Erdos3.TailReflectionData

end

section

namespace Erdos3.TailReflectionData

open scoped BigOperators Classical

universe u

theorem exists_reflected_correlation (n : ℕ) :
    ∀ {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
      (D : TailReflectionData n T G),
      ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
        (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
        ‖D.correlation‖ ^ (2 ^ (n + 1)) ≤
          (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
            D.reflectedKernel t u v h (z - h - h') *
              star (D.reflectedKernel t u v h' (z - h - h')) *
                b t u v h * star (b t u v h')).re := by
  induction n with
  | zero =>
      intro T G _ _ _ _ D
      let e : Fin 0 → G := fun i => Fin.elim0 i
      obtain ⟨z, b, hb, hcorr⟩ := exists_family_reflected_correlation
        (fun t h m => D.kernel t h m e)
        (fun t m => D.leftWeight t m e) (fun t h => D.rightWeight t h e) D.signal
        (fun t m => D.left_norm t m e) (fun t h => D.right_norm t h e) D.signal_norm
      refine ⟨z, (fun t _ _ h => b t h), (fun t _ _ h => hb t h), ?_⟩
      simpa only [correlation, reflectedKernel, iteratedBoxDifference, expect_empty_tuple,
        Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one, one_mul, Nat.zero_add, pow_one,
        e, mul_comm, mul_left_comm, mul_assoc] using hcorr
  | succ n ih =>
      intro T G _ _ _ _ D
      obtain ⟨z, b, hb, hcorr⟩ := ih D.pair
      let B (t : T) (u v : Fin (n + 1) → G) (h : G) :=
        b (t, (u 0, v 0)) (Fin.tail u) (Fin.tail v) h
      refine ⟨z, B, (fun t u v h => hb _ _ _ _), ?_⟩
      have hmean :
          (𝔼 t, 𝔼 u : Fin (n + 1) → G, 𝔼 v : Fin (n + 1) → G, 𝔼 h, 𝔼 h',
            D.reflectedKernel t u v h (z - h - h') *
              star (D.reflectedKernel t u v h' (z - h - h')) *
                B t u v h * star (B t u v h')) =
          𝔼 t : T × (G × G), 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
            D.pair.reflectedKernel t u v h (z - h - h') *
              star (D.pair.reflectedKernel t u v h' (z - h - h')) *
                b t u v h * star (b t u v h') := by
        simp_rw [expect_prod_split]
        apply Finset.expect_congr rfl
        intro t _
        rw [expect_two_dependent_fin_cons]
        simp only [B, Fin.cons_zero, Fin.tail_cons, reflectedKernel_cons]
      rw [hmean]
      calc
        _ = (‖D.correlation‖ ^ 2) ^ (2 ^ (n + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          omega
        _ ≤ ‖D.pair.correlation‖ ^ (2 ^ (n + 1)) :=
          pow_le_pow_left₀ (sq_nonneg _)
            (D.correlation_square_le_pair.trans (Complex.re_le_norm _)) _
        _ ≤ _ := hcorr

end Erdos3.TailReflectionData

end

end OAI
