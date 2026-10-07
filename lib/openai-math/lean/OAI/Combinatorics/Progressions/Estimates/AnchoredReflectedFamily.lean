import OAI.Combinatorics.Progressions.Estimates.TailReflectionInduction
import OAI.Combinatorics.Progressions.Geometry.MissingCoordinateProducts

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

universe u

noncomputable def mixedTailDifference {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (u v : Fin n → G) (h m : G) : ℂ :=
  iteratedBoxDifference n (fun x (a : G × G) => K a.1 a.2 x) u v (h, m)

theorem exists_mixed_reflected_correlation (n : ℕ)
    {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → (Fin n → G) → ℂ) (f : T → G → ℂ)
    (A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t i x, ‖A t i x‖ ≤ 1)
    (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i) :
    ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
      (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x))‖ ^
          (2 ^ (n + 1)) ≤
        (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
          mixedTailDifference (K t) u v h (z - h - h') *
            star (mixedTailDifference (K t) u v h' (z - h - h')) *
              b t u v h * star (b t u v h')).re := by
  let D : TailReflectionData n T G := {
    kernel := K
    signal := f
    leftWeight := fun t m x => A t 0 (Fin.cons 0 (Fin.cons m x))
    rightWeight := fun t h x => A t 1 (Fin.cons h (Fin.cons 0 x))
    tailWeight := fun t i h m x => A t i.succ.succ (Fin.cons h (Fin.cons m x))
    signal_norm := hf
    left_norm := fun t m x => hA t 0 _
    right_norm := fun t h x => hA t 1 _
    tail_norm := fun t i h m x => hA t i.succ.succ _
    tail_misses := by
      intro t i h m x a
      simp only [Fin.cons_update]
      exact hmiss t i.succ.succ _ a }
  have hleft (t : T) (h m : G) (x : Fin n → G) :
      A t 0 (Fin.cons h (Fin.cons m x)) = A t 0 (Fin.cons 0 (Fin.cons m x)) :=
    missesBoxCoordinate_head (hmiss t 0) h 0 (Fin.cons m x)
  have hright (t : T) (h m : G) (x : Fin n → G) :
      A t 1 (Fin.cons h (Fin.cons m x)) = A t 1 (Fin.cons h (Fin.cons 0 x)) := by
    have H := hmiss t 1 (Fin.cons h (Fin.cons m x)) 0
    change A t 1 (Function.update (Fin.cons h (Fin.cons m x))
      (0 : Fin (n + 1)).succ 0) = _ at H
    rw [← Fin.cons_update, Fin.update_cons_zero] at H
    exact H.symm
  have hcorr_eq : D.correlation =
      𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x)) := by
    unfold TailReflectionData.correlation
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro m _
    apply Finset.expect_congr rfl
    intro h _
    dsimp only [D]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    change _ = _ * (A t 0 (Fin.cons h (Fin.cons m x)) *
      (A t 1 (Fin.cons h (Fin.cons m x)) *
        ∏ i : Fin n, A t i.succ.succ (Fin.cons h (Fin.cons m x))))
    simp only [hleft, hright]
    ring
  obtain ⟨z, b, hb, hcorr⟩ := TailReflectionData.exists_reflected_correlation n D
  refine ⟨z, b, hb, ?_⟩
  simpa only [hcorr_eq, TailReflectionData.reflectedKernel, mixedTailDifference, D] using hcorr

theorem exists_mixed_reflected_exp_correlation (n : ℕ)
    {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → (Fin n → G) → ℂ) (f : T → G → ℂ)
    (A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t i x, ‖A t i x‖ ≤ 1)
    (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i) {p : ℝ}
    (hcorr : Real.exp (-p) ≤
      ‖𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x))‖) :
    ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
      (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
      Real.exp (-((2 ^ (n + 1) : ℕ) : ℝ) * p) ≤
        (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
          mixedTailDifference (K t) u v h (z - h - h') *
            star (mixedTailDifference (K t) u v h' (z - h - h')) *
              b t u v h * star (b t u v h')).re := by
  obtain ⟨z, b, hb, hbound⟩ := exists_mixed_reflected_correlation n K f A hf hA hmiss
  refine ⟨z, b, hb, ?_⟩
  have hpower : Real.exp (-((2 ^ (n + 1) : ℕ) : ℝ) * p) =
      Real.exp (-p) ^ (2 ^ (n + 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpower]
  exact (pow_le_pow_left₀ (Real.exp_nonneg _) hcorr _).trans hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedTailDifference_eq_anchor {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (u a : Fin n → G) (h m : G) :
    mixedTailDifference K u a h m =
      K h m u * boxCornerAnchor (fun x => K h m x) a u := by
  rw [mixedTailDifference, iteratedBoxDifference_eq_cornerProduct, boxCornerProduct_eq_mul_anchor]

theorem mixedTailDifference_norm {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (u a : Fin n → G) (h m : G) : ‖mixedTailDifference K u a h m‖ ≤ 1 := by
  rw [mixedTailDifference_eq_anchor, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hK h m u)).trans
    (boxCornerAnchor_norm_le_one (fun x => K h m x) (hK h m) a u)

theorem mixedTailDifference_map {n : ℕ} {X G : Type*} (φ : X → G)
    (K : G → G → (Fin n → G) → ℂ) (u v : Fin n → X) (h m : X) :
    mixedTailDifference (fun h m x => K (φ h) (φ m) (fun i => φ (x i))) u v h m =
      mixedTailDifference K (fun i => φ (u i)) (fun i => φ (v i)) (φ h) (φ m) := by
  simp only [mixedTailDifference, iteratedBoxDifference_eq_cornerProduct]
  exact boxCornerProduct_map φ (fun x => K (φ h) (φ m) x) u v

noncomputable def mixedReflectedCorner {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (c : G) (a : Fin n → G) (ω : Fin n → Bool)
    (x : Fin (n + 2) → G) : ℂ :=
  conjugationPower (booleanWeight ω)
      (K (x 0) (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)) *
    star (conjugationPower (booleanWeight ω)
      (K (x 1) (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)))

theorem mixedReflectedCorner_norm {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (c : G) (a : Fin n → G) (ω : Fin n → Bool) (x : Fin (n + 2) → G) :
    ‖mixedReflectedCorner K c a ω x‖ ≤ 1 := by
  have hc (h m : G) (v : Fin n → G) :
      ‖conjugationPower (booleanWeight ω) (K h m v)‖ ≤ 1 := by
    rw [conjugationPower_eq_if_mod]
    split_ifs <;> simpa only [norm_star] using hK h m v
  rw [mixedReflectedCorner, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc _ _ _)).trans (hc _ _ _)

theorem mixedReflectedCorner_independent {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (c : G) (a : Fin n → G) (ω : Fin n → Bool)
    (j : Fin n) (hj : ω j = true) (x y : Fin (n + 2) → G)
    (hxy : ∀ k, k ≠ j.succ.succ → x k = y k) :
    mixedReflectedCorner K c a ω x = mixedReflectedCorner K c a ω y := by
  have h0 : x 0 = y 0 := hxy 0 (Fin.succ_ne_zero j.succ).symm
  have hne : j.succ.succ ≠ (1 : Fin (n + 2)) := by
    intro heq
    exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
  have h1 : x 1 = y 1 := hxy 1 hne.symm
  have hcorner : boxCorner (fun i => x i.succ.succ) a ω =
      boxCorner (fun i => y i.succ.succ) a ω := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [boxCorner, hj]
    · have hk : k.succ.succ ≠ j.succ.succ := by
        intro heq
        exact hkj (Fin.succ_injective n (Fin.succ_injective (n + 1) heq))
      simp only [boxCorner, hxy k.succ.succ hk]
  simp only [mixedReflectedCorner, h0, h1, hcorner]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_mixed_anchor_weights {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (c : G) (a : Fin n → G) (b d : (Fin n → G) → G → ℂ)
    (hb : ∀ u h, ‖b u h‖ ≤ 1) (hd : ∀ u h, ‖d u h‖ ≤ 1) :
    ∃ A : Fin (n + 2) → (Fin (n + 2) → G) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, (mixedTailDifference K (fun i => x i.succ.succ) a (x 0) (c - x 0 - x 1) *
          star (mixedTailDifference K (fun i => x i.succ.succ) a (x 1) (c - x 0 - x 1)) *
          b (fun i => x i.succ.succ) (x 0) * d (fun i => x i.succ.succ) (x 1)) =
        (K (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) *
          star (K (x 1) (c - x 0 - x 1) (fun i => x i.succ.succ))) * ∏ i, A i x := by
  let S : Finset (Fin n → Bool) := Finset.univ.erase (fun _ => false)
  let F (ω : S) (x : Fin (n + 2) → G) := mixedReflectedCorner K c a ω.val x
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := fun ω x => mixedReflectedCorner_norm K hK c a ω.val x
  have hFind : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    have hne : ω.val ≠ fun _ => false := (Finset.mem_erase.mp ω.property).1
    obtain ⟨i, hi⟩ := exists_true_of_ne_false hne
    exact ⟨i.succ.succ, mixedReflectedCorner_independent K c a ω.val i hi⟩
  obtain ⟨D, hD, hDind, hDprod⟩ := exists_missing_coordinate_product_factors F hF hFind
  have hFprod (x : Fin (n + 2) → G) : (∏ ω : S, F ω x) =
      boxCornerAnchor (fun v => K (x 0) (c - x 0 - x 1) v) a (fun i => x i.succ.succ) *
        star (boxCornerAnchor (fun v => K (x 1) (c - x 0 - x 1) v) a (fun i => x i.succ.succ)) := by
    simp only [F, mixedReflectedCorner, Finset.prod_mul_distrib, ← star_prod]
    have he (h : G) :
        (∏ ω : S, conjugationPower (booleanWeight ω.val)
          (K h (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω.val))) =
          boxCornerAnchor (fun v => K h (c - x 0 - x 1) v) a (fun i => x i.succ.succ) :=
      Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (K h (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)))
    rw [he, he]
  let H (i : Fin (n + 2)) (x : Fin (n + 2) → G) : ℂ :=
    Fin.cases (d (fun j => x j.succ.succ) (x 1))
      (Fin.cases (b (fun j => x j.succ.succ) (x 0)) (fun _ => 1)) i
  have hH : ∀ i x, ‖H i x‖ ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro x
      exact hd _ _
    · refine Fin.cases ?_ (fun j => ?_) i
      · intro x
        exact hb _ _
      · intro x
        change ‖(1 : ℂ)‖ ≤ 1
        norm_num
  have hHind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → H i x = H i y := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro x y hxy
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (Fin.succ_ne_zero j.succ))
      change d (fun j => x j.succ.succ) (x 1) = d (fun j => y j.succ.succ) (y 1)
      rw [ht, hxy 1 (Fin.succ_ne_zero (0 : Fin (n + 1)))]
    · refine Fin.cases ?_ (fun j => ?_) i
      · intro x y hxy
        have hne (j : Fin n) : j.succ.succ ≠ (1 : Fin (n + 2)) := by
          intro heq
          exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
        have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
          funext (fun j => hxy j.succ.succ (hne j))
        change b (fun j => x j.succ.succ) (x 0) = b (fun j => y j.succ.succ) (y 0)
        rw [ht, hxy 0 (Fin.succ_ne_zero (0 : Fin (n + 1))).symm]
      · intro x y _
        rfl
  have hHprod (x : Fin (n + 2) → G) : (∏ i, H i x) =
      d (fun j => x j.succ.succ) (x 1) * b (fun j => x j.succ.succ) (x 0) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    change _ * (_ * (∏ _j : Fin n, (1 : ℂ))) = _
    simp only [Finset.prod_const_one, mul_one]
    rfl
  refine ⟨(fun i x => H i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH i x)).trans (hD i x)
  · intro i x y hxy
    change H i x * D i x = H i y * D i y
    rw [hHind i x y hxy, hDind i x y hxy]
  · intro x
    rw [Finset.prod_mul_distrib, hHprod, hDprod, hFprod]
    simp only [mixedTailDifference_eq_anchor, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_anchored_reflected_family {n : ℕ} {T X G : Type*}
    [Fintype T] [Nonempty T] [Fintype X] [Nonempty X] [AddCommGroup G]
    (φ : X → G) (ψ : G → X) (hψ : ∀ x, ψ (φ x) = x)
    (K : T → G → G → (Fin n → G) → ℂ) (hK : ∀ t h m u, ‖K t h m u‖ ≤ 1)
    (c : G) (B C : T → (Fin n → X) → (Fin n → X) → G → ℂ)
    (hB : ∀ t u v h, ‖B t u v h‖ ≤ 1) (hC : ∀ t u v h, ‖C t u v h‖ ≤ 1)
    {δ : ℝ} (hcorr : δ ≤ ‖𝔼 t, 𝔼 u : Fin n → X, 𝔼 v : Fin n → X, 𝔼 x, 𝔼 y,
      mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ x) (c - φ x - φ y) *
        star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ y)
          (c - φ x - φ y)) * B t u v (φ x) * C t u v (φ y)‖) :
    ∃ A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ,
      (∀ t i x, ‖A t i x‖ ≤ 1) ∧
      (∀ t i x y, (∀ k, k ≠ i → x k = y k) → A t i x = A t i y) ∧
      δ ≤ ‖𝔼 t, 𝔼 u : Fin n → X, 𝔼 x, 𝔼 y,
        (K t (φ x) (c - φ x - φ y) (fun i => φ (u i)) *
          star (K t (φ y) (c - φ x - φ y) (fun i => φ (u i)))) *
            ∏ i, A t i (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))))‖ := by
  let F (t : T) (u v : Fin n → X) := 𝔼 x : X, 𝔼 y : X,
    mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ x) (c - φ x - φ y) *
      star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ y)
        (c - φ x - φ y)) * B t u v (φ x) * C t u v (φ y)
  have hcomm : (𝔼 t, 𝔼 u, 𝔼 v, F t u v) = 𝔼 v, 𝔼 t, 𝔼 u, F t u v := by
    calc
      _ = 𝔼 t, 𝔼 v, 𝔼 u, F t u v :=
        Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)
      _ = _ := Finset.expect_comm _ _ _
  change δ ≤ ‖𝔼 t, 𝔼 u, 𝔼 v, F t u v‖ at hcorr
  rw [hcomm] at hcorr
  have hmean : δ ≤ 𝔼 v, ‖𝔼 t, 𝔼 u, F t u v‖ :=
    hcorr.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hweights (t : T) := exists_mixed_anchor_weights (K t) (hK t) c (fun i => φ (a i))
    (fun u h => B t (fun i => ψ (u i)) a h) (fun u h => C t (fun i => ψ (u i)) a h)
    (fun u h => hB t _ a h) (fun u h => hC t _ a h)
  choose A hA hAind hpoint using hweights
  refine ⟨A, hA, hAind, ?_⟩
  have heq : (𝔼 t, 𝔼 u, F t u a) =
      𝔼 t, 𝔼 u : Fin n → X, 𝔼 x, 𝔼 y,
        (K t (φ x) (c - φ x - φ y) (fun i => φ (u i)) *
          star (K t (φ y) (c - φ x - φ y) (fun i => φ (u i)))) *
            ∏ i, A t i (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j)))) := by
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro u _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    have H := hpoint t (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))))
    have h1 : (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))) :
        Fin (n + 2) → G) 1 = φ y := rfl
    simpa only [Fin.cons_zero, Fin.cons_succ, h1, hψ] using H
  rw [← heq]
  exact ha

end Erdos3

end

end OAI
