import GowersSzemeredi.Definitions
import Mathlib.Algebra.Order.Chebyshev

/-! A common value from two-sided dependence (the passage from Claim 9.4's
escaping frequencies to one new map, Milićević arXiv:2601.01682, printed
p. 66).

On the selected triples of Claim 9.4 the escaping frequency
`ψ₀(x+a) − ψ₁(x) = ψ₂(y+a) − ψ₃(y)` depends only on `(x, a)` and also
only on `(a, y)`. For fixed `a`, the edges `(x, y)` of value `v` lie in
`f⁻¹(v) × h⁻¹(v)`, and these rectangles are disjoint. So some value
class carries a square fraction of the edges.
* `exists_dense_value_class`: an edge set `S` with `f(x) = h(y)` on every
  edge has a value `v` with `|S|² ≤ |S_v| · ((|X| + |Y|)/2)²`.
* `exists_common_value`: summing over `a` with Cauchy–Schwarz, a triple set
  `T` with `F(x, a) = H(a, y)` on `T` has `Θ : A → V` with
  `|T|² ≤ |A|·((|X| + |Y|)/2)² · |{t ∈ T : F(x, a) = Θ(a)}|`.

No connected components are needed: the value classes already partition
both sides. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **One value class carries a square fraction of the edges.** -/
theorem exists_dense_value_class {ι X Y V : Type*} [Fintype X] [Fintype Y] [Nonempty V]
    [DecidableEq V]
    (S : Finset ι) (p : ι → X) (q : ι → Y) (hinj : Set.InjOn (fun i => (p i, q i)) S)
    (f : X → V) (h : Y → V) (hS : ∀ i ∈ S, f (p i) = h (q i)) :
    ∃ v, (S.card : Real) ^ 2 ≤ (S.filter fun i => f (p i) = v).card *
      (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) ^ 2 := by
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨Classical.arbitrary V, ?_⟩
    rw [hS0, Finset.card_empty]
    simp
  set W := S.image fun i => f (p i) with hW
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image W
    (fun v => (S.filter fun i => f (p i) = v).card) (hSne.image _)
  refine ⟨v, ?_⟩
  set M : Real := ((S.filter fun i => f (p i) = v).card : Real) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  set μ := Real.sqrt M with hμ
  have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
  have hμ2 : μ ^ 2 = M := Real.sq_sqrt hM0
  let xs : V → Nat := fun w => (Finset.univ.filter fun x : X => f x = w).card
  let ys : V → Nat := fun w => (Finset.univ.filter fun y : Y => h y = w).card
  let ss : V → Nat := fun w => (S.filter fun i => f (p i) = w).card
  -- each class lies in a rectangle
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
  -- each class is at most `μ (x_w + y_w) / 2`
  have hclass : ∀ w ∈ W, (ss w : Real) ≤ μ * ((xs w : Real) + ys w) / 2 := by
    intro w hw
    have h1 : (ss w : Real) ≤ M := by rw [hM]; exact_mod_cast hv w hw
    have h2 : (ss w : Real) ≤ (xs w : Real) * ys w := by exact_mod_cast hrect w
    have hs0 : (0 : Real) ≤ ss w := Nat.cast_nonneg _
    have hx0 : (0 : Real) ≤ xs w := Nat.cast_nonneg _
    have hy0 : (0 : Real) ≤ ys w := Nat.cast_nonneg _
    have hsq : (ss w : Real) ^ 2 ≤ (μ * ((xs w : Real) + ys w) / 2) ^ 2 := by
      have : (ss w : Real) ^ 2 ≤ M * ((xs w : Real) * ys w) := by
        calc (ss w : Real) ^ 2 = ss w * ss w := sq _
          _ ≤ M * ((xs w : Real) * ys w) := mul_le_mul h1 h2 hs0 hM0
      calc (ss w : Real) ^ 2 ≤ M * ((xs w : Real) * ys w) := this
        _ ≤ M * (((xs w : Real) + ys w) / 2) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hM0
            nlinarith [sq_nonneg ((xs w : Real) - ys w)]
        _ = (μ * ((xs w : Real) + ys w) / 2) ^ 2 := by rw [← hμ2]; ring
    have ht0 : 0 ≤ μ * ((xs w : Real) + ys w) / 2 := by positivity
    nlinarith
  -- the classes partition `S`, and the rectangles' sides partition `X` and `Y`
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
  have hbound : (S.card : Real) ≤ μ * (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) := by
    rw [hsum]
    calc ∑ w ∈ W, (ss w : Real) ≤ ∑ w ∈ W, μ * ((xs w : Real) + ys w) / 2 :=
          Finset.sum_le_sum hclass
      _ = μ * ((∑ w ∈ W, (xs w : Real)) + ∑ w ∈ W, (ys w : Real)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
      _ ≤ μ * (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) := by
          push_cast
          have := add_le_add hX hY
          nlinarith
  have hS0 : (0 : Real) ≤ S.card := Nat.cast_nonneg _
  calc (S.card : Real) ^ 2 ≤ (μ * (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2)) ^ 2 :=
        pow_le_pow_left₀ hS0 hbound 2
    _ = M * (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) ^ 2 := by
        rw [mul_pow, hμ2]

/-- **A common value for a triple family with two-sided dependence.** -/
theorem exists_common_value {X A Y V : Type*} [Fintype X] [Fintype A] [Fintype Y] [Nonempty V]
    [DecidableEq A] [DecidableEq V]
    (T : Finset (X × A × Y)) (F : X → A → V) (H : A → Y → V)
    (hT : ∀ t ∈ T, F t.1 t.2.1 = H t.2.1 t.2.2) :
    ∃ Θ : A → V, (T.card : Real) ^ 2 ≤ Fintype.card A *
      (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) ^ 2 *
        (T.filter fun t => F t.1 t.2.1 = Θ t.2.1).card := by
  have key : ∀ a : A, ∃ v, ((T.filter fun t => t.2.1 = a).card : Real) ^ 2 ≤
      (((T.filter fun t => t.2.1 = a).filter fun t => F t.1 a = v).card : Real) *
        (((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) ^ 2 := by
    intro a
    have hinj : Set.InjOn (fun t : X × A × Y => (t.1, t.2.2))
        ↑(T.filter fun t => t.2.1 = a) := by
      intro t ht t' ht' htt
      simp only [Prod.mk.injEq] at htt
      have ha := (Finset.mem_filter.mp ht).2
      have ha' := (Finset.mem_filter.mp ht').2
      exact Prod.ext htt.1 (Prod.ext (ha.trans ha'.symm) htt.2)
    have hS : ∀ t ∈ T.filter (fun t => t.2.1 = a), F t.1 a = H a t.2.2 := by
      intro t ht
      have h := Finset.mem_filter.mp ht
      have := hT t h.1
      rw [h.2] at this
      exact this
    exact exists_dense_value_class (ι := X × A × Y) (X := X) (Y := Y) (V := V) (T.filter fun t => t.2.1 = a)
      (fun t => t.1) (fun t => t.2.2) hinj (fun x => F x a) (H a) hS
  choose Θ hΘ using key
  refine ⟨Θ, ?_⟩
  have hTsum : (T.card : Real) =
      ∑ a, ((T.filter fun t => t.2.1 = a).card : Real) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.2.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast; rfl
  have hfib : ∀ a, ((T.filter fun t => F t.1 t.2.1 = Θ t.2.1).filter fun t => t.2.1 = a) =
      ((T.filter fun t => t.2.1 = a).filter fun t => F t.1 a = Θ a) := by
    intro a
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h3 ▸ h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h3 ▸ h2⟩, h3⟩
  have hFsum : ((T.filter fun t => F t.1 t.2.1 = Θ t.2.1).card : Real) =
      ∑ a, (((T.filter fun t => t.2.1 = a).filter fun t => F t.1 a = Θ a).card : Real) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.2.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast
    exact Finset.sum_congr rfl fun a _ => by rw [hfib a]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset A))
    (f := fun a => ((T.filter fun t => t.2.1 = a).card : Real))
  rw [Finset.card_univ] at hcs
  rw [hTsum, hFsum, mul_assoc, Finset.mul_sum]
  refine hcs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_)
    (Nat.cast_nonneg _))
  rw [mul_comm (((((Fintype.card X + Fintype.card Y : Nat) : Real) / 2) ^ 2))]
  exact hΘ a

end LeanProofs.GowersSzemeredi
