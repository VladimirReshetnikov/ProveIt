import GowersSzemeredi.Proofs16CommonValue

/-! The common-value extraction with the sharp rectangle bound and general
projections (used for Milićević's Claim 9.5, arXiv:2601.01682, printed
p. 67).

`exists_dense_value_class` pays `((|X| + |Y|)/2)²` by AM–GM, which is
lossy when the two sides have different sizes. In Claim 9.5 one side is a
single coordinate and the other is nine, so the loss would be a power of
`N`. Cauchy–Schwarz over the value classes,
`∑_v √x_v √y_v ≤ √(∑x_v) √(∑y_v)`, gives the sharp `|X|·|Y|`.
* `exists_dense_value_class_sharp`: an edge set with `f(x) = h(y)` on
  every edge has a value class with `|S|² ≤ |S_v|·|X|·|Y|`.
* `exists_common_value_sharp`: a family `T` indexed by any type, with
  projections `x, a, y` that are jointly injective on `T` and satisfy
  `F(x, a) = H(a, y)`, has `Θ : A → V` with
  `|T|² ≤ |A|·|X|·|Y| · |{t ∈ T : F(x, a) = Θ(a)}|`.
* `exists_common_value_det`: the same, from the hypothesis that `F(x, a)`
  is determined by `(a, y)` on `T`, with no explicit `H`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **A value class with the sharp rectangle bound.** -/
theorem exists_dense_value_class_sharp {ι X Y V : Type*} [Fintype X] [Fintype Y] [Nonempty V]
    [DecidableEq V]
    (S : Finset ι) (p : ι → X) (q : ι → Y) (hinj : Set.InjOn (fun i => (p i, q i)) S)
    (f : X → V) (h : Y → V) (hS : ∀ i ∈ S, f (p i) = h (q i)) :
    ∃ v, (S.card : Real) ^ 2 ≤ ((S.filter fun i => f (p i) = v).card : Real) *
      ((Fintype.card X : Real) * Fintype.card Y) := by
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨Classical.arbitrary V, ?_⟩
    rw [hS0, Finset.card_empty]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  set W := S.image fun i => f (p i) with hW
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image W
    (fun v => (S.filter fun i => f (p i) = v).card) (hSne.image _)
  refine ⟨v, ?_⟩
  set M : Real := ((S.filter fun i => f (p i) = v).card : Real) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  let xs : V → Nat := fun w => (Finset.univ.filter fun x : X => f x = w).card
  let ys : V → Nat := fun w => (Finset.univ.filter fun y : Y => h y = w).card
  let ss : V → Nat := fun w => (S.filter fun i => f (p i) = w).card
  have hrect : ∀ w, ss w ≤ xs w * ys w := by
    intro w
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun i => (p i, q i)) ?_ ?_
    · intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hh : h (q i) = w := by rw [← hS i hi'.1]; exact hi'.2
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and]
      exact ⟨hi'.2, hh⟩
    · intro i hi j hj hij
      exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
  -- each class is at most `√M · √x_w · √y_w`
  have hclass : ∀ w ∈ W, (ss w : Real) ≤
      Real.sqrt M * (Real.sqrt (xs w) * Real.sqrt (ys w)) := by
    intro w hw
    have h1 : (ss w : Real) ≤ M := by rw [hM]; exact_mod_cast hv w hw
    have h2 : (ss w : Real) ≤ (xs w : Real) * ys w := by exact_mod_cast hrect w
    have hs0 : (0 : Real) ≤ ss w := Nat.cast_nonneg _
    have hsq : (ss w : Real) ^ 2 ≤ M * ((xs w : Real) * ys w) := by
      calc (ss w : Real) ^ 2 = ss w * ss w := sq _
        _ ≤ M * ((xs w : Real) * ys w) := mul_le_mul h1 h2 hs0 hM0
    calc (ss w : Real) = Real.sqrt ((ss w : Real) ^ 2) := (Real.sqrt_sq hs0).symm
      _ ≤ Real.sqrt (M * ((xs w : Real) * ys w)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt M * (Real.sqrt (xs w) * Real.sqrt (ys w)) := by
          rw [Real.sqrt_mul hM0, Real.sqrt_mul (Nat.cast_nonneg _)]
  have hsum : (S.card : Real) = ∑ w ∈ W, (ss w : Real) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i => f (p i)) (t := W)
      (fun i hi => Finset.mem_image_of_mem _ hi)]
    push_cast; rfl
  have hX : ∑ w ∈ W, (xs w : Real) ≤ Fintype.card X := by
    have : ∑ w ∈ W, xs w ≤ Fintype.card X := by
      simp only [xs]
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      exact Finset.card_le_univ _
    exact_mod_cast this
  have hY : ∑ w ∈ W, (ys w : Real) ≤ Fintype.card Y := by
    have : ∑ w ∈ W, ys w ≤ Fintype.card Y := by
      simp only [ys]
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      exact Finset.card_le_univ _
    exact_mod_cast this
  have hCS : ∑ w ∈ W, Real.sqrt (xs w) * Real.sqrt (ys w) ≤
      Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card Y) :=
    (Real.sum_sqrt_mul_sqrt_le W (fun w => Nat.cast_nonneg (xs w))
      (fun w => Nat.cast_nonneg (ys w))).trans
      (mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
  have hbound : (S.card : Real) ≤
      Real.sqrt M * (Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card Y)) := by
    rw [hsum]
    calc ∑ w ∈ W, (ss w : Real) ≤
          ∑ w ∈ W, Real.sqrt M * (Real.sqrt (xs w) * Real.sqrt (ys w)) :=
          Finset.sum_le_sum hclass
      _ = Real.sqrt M * ∑ w ∈ W, Real.sqrt (xs w) * Real.sqrt (ys w) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt M * (Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card Y)) :=
          mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg _)
  have hS0 : (0 : Real) ≤ S.card := Nat.cast_nonneg _
  calc (S.card : Real) ^ 2 ≤
        (Real.sqrt M * (Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card Y))) ^ 2 :=
        pow_le_pow_left₀ hS0 hbound 2
    _ = M * ((Fintype.card X : Real) * Fintype.card Y) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hM0, Real.sq_sqrt (Nat.cast_nonneg _),
          Real.sq_sqrt (Nat.cast_nonneg _)]

/-- **A common value with general projections and the sharp bound.** -/
theorem exists_common_value_sharp {ι X A Y V : Type*} [Fintype X] [Fintype A] [Fintype Y]
    [Nonempty V] [DecidableEq A] [DecidableEq V]
    (T : Finset ι) (px : ι → X) (pa : ι → A) (py : ι → Y)
    (hinj : Set.InjOn (fun i => (px i, pa i, py i)) T)
    (F : X → A → V) (H : A → Y → V) (hT : ∀ i ∈ T, F (px i) (pa i) = H (pa i) (py i)) :
    ∃ Θ : A → V, (T.card : Real) ^ 2 ≤ Fintype.card A *
      ((Fintype.card X : Real) * Fintype.card Y) *
        (T.filter fun i => F (px i) (pa i) = Θ (pa i)).card := by
  have key : ∀ a : A, ∃ v, ((T.filter fun i => pa i = a).card : Real) ^ 2 ≤
      (((T.filter fun i => pa i = a).filter fun i => F (px i) a = v).card : Real) *
        ((Fintype.card X : Real) * Fintype.card Y) := by
    intro a
    have hinj' : Set.InjOn (fun i => (px i, py i)) ↑(T.filter fun i => pa i = a) := by
      intro i hi j hj hij
      simp only [Prod.mk.injEq] at hij
      have ha := (Finset.mem_filter.mp hi).2
      have ha' := (Finset.mem_filter.mp hj).2
      exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
        (Prod.ext hij.1 (Prod.ext (ha.trans ha'.symm) hij.2))
    have hS : ∀ i ∈ T.filter (fun i => pa i = a), F (px i) a = H a (py i) := by
      intro i hi
      have h := Finset.mem_filter.mp hi
      have := hT i h.1
      rw [h.2] at this
      exact this
    exact exists_dense_value_class_sharp (ι := ι) (X := X) (Y := Y) (V := V)
      (T.filter fun i => pa i = a) px py hinj' (fun x => F x a) (H a) hS
  choose Θ hΘ using key
  refine ⟨Θ, ?_⟩
  have hTsum : (T.card : Real) = ∑ a, ((T.filter fun i => pa i = a).card : Real) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := pa) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast; rfl
  have hfib : ∀ a, ((T.filter fun i => F (px i) (pa i) = Θ (pa i)).filter fun i => pa i = a) =
      ((T.filter fun i => pa i = a).filter fun i => F (px i) a = Θ a) := by
    intro a
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h3 ▸ h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h3 ▸ h2⟩, h3⟩
  have hFsum : ((T.filter fun i => F (px i) (pa i) = Θ (pa i)).card : Real) =
      ∑ a, (((T.filter fun i => pa i = a).filter fun i => F (px i) a = Θ a).card : Real) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := pa) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast
    exact Finset.sum_congr rfl fun a _ => by rw [hfib a]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset A))
    (f := fun a => ((T.filter fun i => pa i = a).card : Real))
  rw [Finset.card_univ] at hcs
  rw [hTsum, hFsum, mul_assoc, Finset.mul_sum]
  refine hcs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_)
    (Nat.cast_nonneg _))
  rw [mul_comm ((Fintype.card X : Real) * Fintype.card Y)]
  exact hΘ a

/-- **A common value from a determination property.** If on `T` the value
`F(x, a)` is determined by `(a, y)`, it is a function of `a` on a dense part. -/
theorem exists_common_value_det {ι X A Y V : Type*} [Fintype X] [Fintype A] [Fintype Y]
    [Nonempty V] [DecidableEq A] [DecidableEq V]
    (T : Finset ι) (px : ι → X) (pa : ι → A) (py : ι → Y)
    (hinj : Set.InjOn (fun i => (px i, pa i, py i)) T) (F : X → A → V)
    (hdet : ∀ i ∈ T, ∀ i' ∈ T, pa i = pa i' → py i = py i' →
      F (px i) (pa i) = F (px i') (pa i')) :
    ∃ Θ : A → V, (T.card : Real) ^ 2 ≤ Fintype.card A *
      ((Fintype.card X : Real) * Fintype.card Y) *
        (T.filter fun i => F (px i) (pa i) = Θ (pa i)).card := by
  let H : A → Y → V := fun a y =>
    if h : ∃ i ∈ T, pa i = a ∧ py i = y then F (px h.choose) a else Classical.arbitrary V
  refine exists_common_value_sharp T px pa py hinj F H fun i hi => ?_
  have hex : ∃ i' ∈ T, pa i' = pa i ∧ py i' = py i := ⟨i, hi, rfl, rfl⟩
  simp only [H, dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  have := hdet i hi _ h1 h2.symm h3.symm
  rw [this, h2]

end LeanProofs.GowersSzemeredi
