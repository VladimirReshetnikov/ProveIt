import IntegerPoints.Lemma9Tools
import IntegerPoints.ZhaiCao
import Mathlib.Algebra.Order.Chebyshev

/-!
# Zhai–Cao, Lemma 9: the Cauchy–Schwarz step (Heath-Brown's method)

For `S = ∑_{n ∼ N} a_n ∑_{u ∼ U} b_u ∑_{v ∼ V} c_v e(√(nx)/(uv))` we sort the pairs
`(v, n)` into `Q` classes according to the value of `√n/v`, apply Cauchy–Schwarz
over `(u, class)`, expand the square and sum over `u` first:

`‖S‖² ≤ #{u ∼ U} (Q+1) ∑_{(p₁, p₂) : |λ(p₁,p₂)| ≤ 2√N/(VQ)} ‖∑_{u ∼ U} e(√x λ(p₁,p₂)/u)‖`,

where `λ((v₁,n₁),(v₂,n₂)) = √n₁/v₁ − √n₂/v₂`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace L9

/-- `φ(v, n) = √n / v`. -/
noncomputable def phi (p : ℕ × ℕ) : ℝ := Real.sqrt p.2 / p.1

/-- The class of `(v, n)`: `⌊φ(v,n) · VQ/(2√N)⌋₊`. -/
noncomputable def cls (V N : ℝ) (Q : ℕ) (p : ℕ × ℕ) : ℕ :=
  ⌊phi p * (V * Q / (2 * Real.sqrt N))⌋₊

theorem lamOf_eq (p : (ℕ × ℕ) × (ℕ × ℕ)) : lamOf p = phi p.1 - phi p.2 := rfl

theorem phi_nonneg (p : ℕ × ℕ) : 0 ≤ phi p := by unfold phi; positivity

/-- Pairs in the same class are `2√N/(VQ)`-close. -/
theorem close_of_cls_eq {V N : ℝ} {Q : ℕ} (hV : 0 < V) (hN : 0 < N) (hQ : 1 ≤ Q)
    {p₁ p₂ : ℕ × ℕ} (h : cls V N Q p₁ = cls V N Q p₂) :
    |lamOf (p₁, p₂)| ≤ 2 * Real.sqrt N / (V * Q) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set s : ℝ := V * Q / (2 * Real.sqrt N) with hs
  have hs0 : 0 < s := by positivity
  unfold cls at h
  rw [← hs] at h
  have h1 := Nat.floor_le (mul_nonneg (phi_nonneg p₁) hs0.le)
  have h1' := Nat.lt_floor_add_one (phi p₁ * s)
  have h2 := Nat.floor_le (mul_nonneg (phi_nonneg p₂) hs0.le)
  have h2' := Nat.lt_floor_add_one (phi p₂ * s)
  rw [h] at h1 h1'
  have hd : |phi p₁ * s - phi p₂ * s| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_mul, abs_mul, abs_of_pos hs0] at hd
  have e : 2 * Real.sqrt N / (V * Q) = 1 / s := by
    rw [hs]
    field_simp
  show |phi p₁ - phi p₂| ≤ 2 * Real.sqrt N / (V * Q)
  rw [e, le_div_iff₀ hs0]
  exact hd.le

/-- The classes lie in `range (Q + 1)`. -/
theorem cls_mem_range {V N : ℝ} {Q : ℕ} (hV : 1 ≤ V) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    {p : ℕ × ℕ} (hp : p ∈ dyadic V ×ˢ dyadic N) : cls V N Q p ∈ Finset.range (Q + 1) := by
  rw [Finset.mem_product] at hp
  obtain ⟨hv1, hv2⟩ := mem_dyadic_bounds (by linarith) hp.1
  obtain ⟨hn1, hn2⟩ := mem_dyadic_bounds (by linarith) hp.2
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [Finset.mem_range, Nat.lt_succ_iff, cls]
  apply Nat.floor_le_of_le
  -- phi p * (V Q / (2√N)) ≤ Q ⟸ phi p ≤ 2√N/V
  have hphi : phi p ≤ 2 * Real.sqrt N / V := by
    unfold phi
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : Real.sqrt p.2 ≤ 2 * Real.sqrt N := by
      calc Real.sqrt p.2 ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 * Real.sqrt N := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    nlinarith [Real.sqrt_nonneg (p.2 : ℝ)]
  calc phi p * (V * Q / (2 * Real.sqrt N)) ≤ 2 * Real.sqrt N / V * (V * Q / (2 * Real.sqrt N)) :=
        mul_le_mul_of_nonneg_right hphi (by positivity)
    _ = Q := by field_simp

/-- The weighted inner sum over a class: `T(u, q) = ∑_{(v,n) : cls = q} a_n c_v e(√x φ/u)`. -/
noncomputable def Tq (x V N : ℝ) (Q : ℕ) (a c : ℕ → ℂ) (u q : ℕ) : ℂ :=
  ∑ p ∈ (dyadic V ×ˢ dyadic N).filter (fun p => cls V N Q p = q),
    a p.2 * c p.1 * e (Real.sqrt x * phi p / u)

/-- `S = ∑_u b_u ∑_q T(u, q)`. -/
theorem tripleSum_eq {x V N : ℝ} (U : ℝ) (Q : ℕ) (hV : 1 ≤ V) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (a b c : ℕ → ℂ) :
    tripleSumZC x N U V a b c =
      ∑ u ∈ dyadic U, b u * ∑ q ∈ Finset.range (Q + 1), Tq x V N Q a c u q := by
  classical
  unfold tripleSumZC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∑ q ∈ Finset.range (Q + 1), Tq x V N Q a c u q =
      ∑ p ∈ dyadic V ×ˢ dyadic N, a p.2 * c p.1 * e (Real.sqrt x * phi p / u) := by
    unfold Tq
    exact Finset.sum_fiberwise_of_maps_to (fun p hp => cls_mem_range hV hN hQ hp) _
  rw [h1, Finset.mul_sum, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  have e1 : Real.sqrt (n * x) / (u * v) = Real.sqrt x * phi (v, n) / u := by
    unfold phi
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    ring
  rw [e1]
  ring

/-- Cauchy–Schwarz: `‖S‖² ≤ #U (Q+1) ∑_{u,q} ‖T(u,q)‖²`. -/
theorem cauchy_tripleSum {x V N : ℝ} (U : ℝ) (Q : ℕ) (hV : 1 ≤ V) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (a b c : ℕ → ℂ) (hb : UnitBounded b) :
    ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
      (((dyadic U).card * (Q + 1) : ℕ) : ℝ) *
        ∑ u ∈ dyadic U, ∑ q ∈ Finset.range (Q + 1), ‖Tq x V N Q a c u q‖ ^ 2 := by
  rw [tripleSum_eq U Q hV hN hQ a b c]
  have h1 : ‖∑ u ∈ dyadic U, b u * ∑ q ∈ Finset.range (Q + 1), Tq x V N Q a c u q‖ ≤
      ∑ u ∈ dyadic U, ∑ q ∈ Finset.range (Q + 1), ‖Tq x V N Q a c u q‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_mul]
    calc ‖b u‖ * ‖∑ q ∈ Finset.range (Q + 1), Tq x V N Q a c u q‖
        ≤ 1 * ∑ q ∈ Finset.range (Q + 1), ‖Tq x V N Q a c u q‖ :=
          mul_le_mul (hb u) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2 : (∑ u ∈ dyadic U, ∑ q ∈ Finset.range (Q + 1), ‖Tq x V N Q a c u q‖) ^ 2 ≤
      (((dyadic U).card * (Q + 1) : ℕ) : ℝ) *
        ∑ u ∈ dyadic U, ∑ q ∈ Finset.range (Q + 1), ‖Tq x V N Q a c u q‖ ^ 2 := by
    rw [← Finset.sum_product' (dyadic U) (Finset.range (Q + 1)),
      ← Finset.sum_product' (dyadic U) (Finset.range (Q + 1))]
    have := sq_sum_le_card_mul_sum_sq (s := dyadic U ×ˢ Finset.range (Q + 1))
      (f := fun p => ‖Tq x V N Q a c p.1 p.2‖)
    rw [Finset.card_product, Finset.card_range] at this
    exact this
  calc ‖∑ u ∈ dyadic U, b u * ∑ q ∈ Finset.range (Q + 1), Tq x V N Q a c u q‖ ^ 2
      ≤ (∑ u ∈ dyadic U, ∑ q ∈ Finset.range (Q + 1), ‖Tq x V N Q a c u q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- Expanding the square and summing over `u`:
`∑_u ‖T(u,q)‖² ≤ ∑_{p₁, p₂ ∈ class q} ‖∑_u e(√x λ(p₁,p₂)/u)‖`. -/
theorem sum_sq_Tq_le {x V N : ℝ} (U : ℝ) (Q : ℕ) (a c : ℕ → ℂ) (ha : UnitBounded a)
    (hc : UnitBounded c) (q : ℕ) :
    ∑ u ∈ dyadic U, ‖Tq x V N Q a c u q‖ ^ 2 ≤
      ∑ p₁ ∈ (dyadic V ×ˢ dyadic N).filter (fun p => cls V N Q p = q),
        ∑ p₂ ∈ (dyadic V ×ˢ dyadic N).filter (fun p => cls V N Q p = q),
          ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf (p₁, p₂) / u)‖ := by
  classical
  set P := (dyadic V ×ˢ dyadic N).filter (fun p => cls V N Q p = q) with hP
  set w : ℕ × ℕ → ℂ := fun p => a p.2 * c p.1 with hw
  have hw1 : ∀ p, ‖w p‖ ≤ 1 := by
    intro p
    rw [hw]
    simp only
    rw [norm_mul]
    exact mul_le_one₀ (ha _) (norm_nonneg _) (hc _)
  -- `‖T‖² = Re (T · conj T)`, expanded
  have hexp : ∀ u : ℕ, ‖Tq x V N Q a c u q‖ ^ 2 =
      (∑ p₁ ∈ P, ∑ p₂ ∈ P, w p₁ * starRingEnd ℂ (w p₂) *
        e (Real.sqrt x * lamOf (p₁, p₂) / u)).re := by
    intro u
    have h1 : ‖Tq x V N Q a c u q‖ ^ 2 =
        (Tq x V N Q a c u q * starRingEnd ℂ (Tq x V N Q a c u q)).re := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [h1]
    congr 1
    unfold Tq
    rw [← hP, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
    rw [map_mul, lamOf_eq, show Real.sqrt x * (phi p₁ - phi p₂) / u =
      Real.sqrt x * phi p₁ / u + -(Real.sqrt x * phi p₂ / u) by ring, KL.e_add, KL.e_neg]
    rw [hw]
    simp only
    ring
  simp_rw [hexp]
  rw [← Complex.re_sum]
  -- `Re ≤ ‖·‖`, swap the sums, bound termwise
  have hswap : ∑ u ∈ dyadic U, ∑ p₁ ∈ P, ∑ p₂ ∈ P,
      w p₁ * starRingEnd ℂ (w p₂) * e (Real.sqrt x * lamOf (p₁, p₂) / u) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, w p₁ * starRingEnd ℂ (w p₂) *
        ∑ u ∈ dyadic U, e (Real.sqrt x * lamOf (p₁, p₂) / u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p₂ _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p₁ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p₂ _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc ‖w p₁‖ * ‖w p₂‖ * ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf (p₁, p₂) / u)‖
      ≤ 1 * 1 * ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf (p₁, p₂) / u)‖ := by
        gcongr
        · exact hw1 p₁
        · exact hw1 p₂
    _ = _ := by ring

/-- Summing the class sums: pairs in the same class are close. -/
theorem sum_classes_le {x V N : ℝ} (U : ℝ) (Q : ℕ) (hV : 1 ≤ V) (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.range (Q + 1),
      ∑ p₁ ∈ (dyadic V ×ˢ dyadic N).filter (fun p => cls V N Q p = q),
        ∑ p₂ ∈ (dyadic V ×ˢ dyadic N).filter (fun p => cls V N Q p = q),
          ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf (p₁, p₂) / u)‖ ≤
      ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ 2 * Real.sqrt N / (V * Q)),
        ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf p / u)‖ := by
  classical
  set P := dyadic V ×ˢ dyadic N with hP
  set G : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun p => ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf p / u)‖
    with hG
  have hG0 : ∀ p, 0 ≤ G p := fun p => norm_nonneg _
  -- the left side is a sum over the pairs with equal classes
  have h1 : ∀ q ∈ Finset.range (Q + 1),
      ∑ p₁ ∈ P.filter (fun p => cls V N Q p = q), ∑ p₂ ∈ P.filter (fun p => cls V N Q p = q),
        G (p₁, p₂) =
      ∑ p ∈ (P ×ˢ P).filter (fun p : (ℕ × ℕ) × (ℕ × ℕ) => cls V N Q p.1 = q ∧ cls V N Q p.2 = q),
        G p := by
    intro q _
    rw [← Finset.sum_product', ← Finset.filter_product]
  have h2 : ∑ q ∈ Finset.range (Q + 1),
      ∑ p ∈ (P ×ˢ P).filter (fun p : (ℕ × ℕ) × (ℕ × ℕ) => cls V N Q p.1 = q ∧ cls V N Q p.2 = q),
        G p =
      ∑ p ∈ (P ×ˢ P).filter (fun p : (ℕ × ℕ) × (ℕ × ℕ) => cls V N Q p.1 = cls V N Q p.2), G p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (P ×ˢ P).filter
      (fun p : (ℕ × ℕ) × (ℕ × ℕ) => cls V N Q p.1 = cls V N Q p.2))
      (t := Finset.range (Q + 1)) (g := fun p => cls V N Q p.1) (f := G) ?_]
    · refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hp, h1, h2⟩
        exact ⟨⟨hp, by rw [h1, h2]⟩, h1⟩
      · rintro ⟨⟨hp, h⟩, h1⟩
        exact ⟨hp, h1, by rw [← h, h1]⟩
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      exact cls_mem_range hV hN hQ hp.1.1
  calc _ = ∑ q ∈ Finset.range (Q + 1),
      ∑ p ∈ (P ×ˢ P).filter (fun p : (ℕ × ℕ) × (ℕ × ℕ) => cls V N Q p.1 = q ∧ cls V N Q p.2 = q),
        G p := Finset.sum_congr rfl h1
    _ = ∑ p ∈ (P ×ˢ P).filter (fun p : (ℕ × ℕ) × (ℕ × ℕ) => cls V N Q p.1 = cls V N Q p.2),
        G p := h2
    _ ≤ ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ 2 * Real.sqrt N / (V * Q)), G p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => hG0 p)
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, close_of_cls_eq (by linarith) (by linarith) hQ hp.2⟩

/-- **The Cauchy–Schwarz step.** -/
theorem cauchy_step {x U V N : ℝ} (Q : ℕ) (hQ : 1 ≤ Q) (hV : 1 ≤ V) (hN : 1 ≤ N)
    (a b c : ℕ → ℂ) (ha : UnitBounded a) (hb : UnitBounded b) (hc : UnitBounded c) :
    ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
      (((dyadic U).card * (Q + 1) : ℕ) : ℝ) *
        ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ 2 * Real.sqrt N / (V * Q)),
          ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf p / u)‖ := by
  refine (cauchy_tripleSum U Q hV hN hQ a b c hb).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.sum_comm]
  refine le_trans (Finset.sum_le_sum fun q _ => sum_sq_Tq_le U Q a c ha hc q) ?_
  exact sum_classes_le U Q hV hN hQ

end L9

end LeanProofs.IntegerPoints
