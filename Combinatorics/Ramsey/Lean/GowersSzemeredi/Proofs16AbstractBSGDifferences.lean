import GowersSzemeredi.Proofs16FourWalkLadder

/-! Popular differences and the per-difference ladder: the first part of the
proof of Milićević's abstract Balog–Szemerédi–Gowers theorem
(arXiv:2601.01682, Theorem 4.1, printed pp. 48–49).

`G` is a finite abelian group, `A ⊆ X ⊆ G`, and `Q : ℕ → G → G → G → G → Prop`
is a ladder of quadruple families. Pairs of pairs are written
`(x + d, x), (y + d, y)`.
* `diffGoodCount A good d` counts the pairs `(x, y) ∈ A²` with
  `x + d, y + d ∈ A` and `good (x + d) x (y + d) y`.
* `exists_popular_differences`: if these counts sum to at least `c|X|³`
  and `|X − X| ≤ K|X|`, then at least `(c/2)|X|` differences `d ∈ X − X`
  each have count at least `(c/2K)|X|²`.
* `difference_ladder_rel_four`: fix such a `d`. Suppose `Q 1` has the
  symmetry `(S1)` and `Q` is weakly transitive against `Q 1` with
  constant `c' ≤ (c/2K)^5/2^17`. Then a set of at least `3c|X|/(16K)`
  vertices `u` (pairs `(u + d, u)` in `A²`) has
  `Q 4 (u + d) u (v + d) v` for any two of its vertices. This is
  Claim 4.3 in four-walk form. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- Good pairs of pairs with difference `d`. -/
def diffGoodCount {G : Type*} [AddCommGroup G] (A : Finset G)
    (good : G → G → G → G → Prop) (d : G) : Nat :=
  ((A ×ˢ A).filter fun p => p.1 + d ∈ A ∧ p.2 + d ∈ A ∧
    good (p.1 + d) p.1 (p.2 + d) p.2).card

theorem diffGoodCount_le {G : Type*} [AddCommGroup G] {A X : Finset G} (hAX : A ⊆ X)
    (good : G → G → G → G → Prop) (d : G) :
    (diffGoodCount A good d : Real) ≤ (X.card : Real) ^ 2 := by
  have h : diffGoodCount A good d ≤ X.card ^ 2 := by
    unfold diffGoodCount
    calc _ ≤ (A ×ˢ A).card := Finset.card_filter_le _ _
      _ = A.card * A.card := Finset.card_product _ _
      _ ≤ X.card * X.card := Nat.mul_le_mul (Finset.card_le_card hAX) (Finset.card_le_card hAX)
      _ = X.card ^ 2 := (sq _).symm
  exact_mod_cast h

theorem diffGoodCount_eq_zero {G : Type*} [AddCommGroup G] {A X : Finset G}
    (hAX : A ⊆ X) (good : G → G → G → G → Prop) {d : G} (hd : d ∉ X - X) :
    diffGoodCount A good d = 0 := by
  unfold diffGoodCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp ⟨h1, _, _⟩
  apply hd
  have h := Finset.sub_mem_sub (hAX h1) (hAX (Finset.mem_product.mp hp).1)
  rwa [add_sub_cancel_left] at h

/-- **Popular differences.** -/
theorem exists_popular_differences {G : Type*} [AddCommGroup G]
    {A X : Finset G} (hAX : A ⊆ X) (good : G → G → G → G → Prop) {c K : Real}
    (hK : 0 < K) (hdoub : ((X - X).card : Real) ≤ K * X.card)
    (hgood : c * (X.card : Real) ^ 3 ≤ ∑ d ∈ X - X, (diffGoodCount A good d : Real)) :
    c / 2 * X.card ≤ (((X - X).filter fun d =>
      c / (2 * K) * (X.card : Real) ^ 2 ≤ diffGoodCount A good d).card : Real) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans (by positivity)
  let p : G → Prop := fun d => c / (2 * K) * (X.card : Real) ^ 2 ≤ diffGoodCount A good d
  let D := (X - X).filter p
  have hin : ∑ d ∈ D, (diffGoodCount A good d : Real) ≤ D.card * (X.card : Real) ^ 2 := by
    calc _ ≤ ∑ _d ∈ D, (X.card : Real) ^ 2 :=
          Finset.sum_le_sum fun d _ => diffGoodCount_le hAX good d
      _ = D.card * (X.card : Real) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hout : ∑ d ∈ (X - X).filter (fun d => ¬ p d), (diffGoodCount A good d : Real) ≤
      c / 2 * (X.card : Real) ^ 3 := by
    calc _ ≤ ∑ _d ∈ (X - X).filter (fun d => ¬ p d), c / (2 * K) * (X.card : Real) ^ 2 :=
            Finset.sum_le_sum fun d hd => (not_le.mp (Finset.mem_filter.mp hd).2).le
        _ = (((X - X).filter fun d => ¬ p d).card : Real) * (c / (2 * K) * (X.card : Real) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (K * X.card) * (c / (2 * K) * (X.card : Real) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact (by exact_mod_cast Finset.card_filter_le _ _ :
              (((X - X).filter fun d => ¬ p d).card : Real) ≤ (X - X).card).trans hdoub
        _ = c / 2 * (X.card : Real) ^ 3 := by field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not (X - X) p
    (fun d => (diffGoodCount A good d : Real))
  rcases Nat.eq_zero_or_pos X.card with h0 | hpos
  · simp [h0]
  have hX2 : (0 : Real) < (X.card : Real) ^ 2 := by positivity
  have h1 : c / 2 * (X.card : Real) * (X.card : Real) ^ 2 ≤ D.card * (X.card : Real) ^ 2 := by
    have : c * (X.card : Real) ^ 3 ≤ D.card * (X.card : Real) ^ 2 + c / 2 * (X.card : Real) ^ 3 := by
      linarith
    nlinarith
  exact le_of_mul_le_mul_right h1 hX2

/-- **Claim 4.3 for one popular difference.** -/
theorem difference_ladder_rel_four {G : Type*} [AddCommGroup G]
    {A X : Finset G} (hX : X.Nonempty) (hAX : A ⊆ X) (Q : Nat → G → G → G → G → Prop)
    (hS1 : ∀ a₁ a₂ a₃ a₄, Q 1 a₁ a₂ a₃ a₄ → Q 1 a₃ a₄ a₁ a₂) {c' δ : Real} (hc'0 : 0 < c')
    (hδ : 0 < δ)
    (hWT : ∀ i, i + 1 ≤ 4 → ∀ a₁ a₂ a₃ a₄, c' * X.card ≤ (((A ×ˢ A).filter fun p =>
        Q i a₁ a₂ p.1 p.2 ∧ Q 1 p.1 p.2 a₃ a₄).card : Real) → Q (i + 1) a₁ a₂ a₃ a₄)
    (hc' : 8 * c' ≤ δ ^ 5 / 16384) {d : G}
    (hcount : δ * (X.card : Real) ^ 2 ≤ diffGoodCount A (Q 1) d) :
    ∃ T : Finset G, T ⊆ X ∧ 3 * δ * X.card / 8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ∈ A ∧ u + d ∈ A ∧ Q 4 (u + d) u (v + d) v := by
  let V := {x : G // x ∈ X}
  haveI : Nonempty V := ⟨⟨hX.choose, hX.choose_spec⟩⟩
  have hcardV : Fintype.card V = X.card := by simp only [V, Fintype.card_coe]
  let R : Nat → V → V → Prop := fun i x y =>
    (x : G) ∈ A ∧ (x : G) + d ∈ A ∧ (y : G) ∈ A ∧ (y : G) + d ∈ A ∧
      Q i ((x : G) + d) x ((y : G) + d) y
  have hsym : ∀ a b, R 1 a b → R 1 b a := fun a b ⟨h1, h2, h3, h4, hq⟩ =>
    ⟨h3, h4, h1, h2, hS1 _ _ _ _ hq⟩
  -- the edge count is the good count for `d`
  have hpairs : (Finset.univ.filter fun p : V × V => R 1 p.1 p.2).card =
      diffGoodCount A (Q 1) d := by
    unfold diffGoodCount
    refine Finset.card_bij (fun p _ => ((p.1 : G), (p.2 : G))) ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2, h3, h4, hq⟩ := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h3⟩, h2, h4, hq⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · intro q hq
      obtain ⟨hmem, h2, h4, hq'⟩ := Finset.mem_filter.mp hq
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hmem
      exact ⟨(⟨q.1, hAX h1⟩, ⟨q.2, hAX h3⟩),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3, h4, hq'⟩, rfl⟩
  have hedges : δ * (Fintype.card V : Real) ^ 2 ≤
      ∑ x : V, ((graphNeighbours (R 1) x).card : Real) := by
    have hsum : (∑ x : V, (graphNeighbours (R 1) x).card) =
        (Finset.univ.filter fun p : V × V => R 1 p.1 p.2).card := by
      simp only [graphNeighbours, Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by congr
    rw [hcardV]
    calc δ * (X.card : Real) ^ 2 ≤ diffGoodCount A (Q 1) d := hcount
      _ = ∑ x : V, ((graphNeighbours (R 1) x).card : Real) := by
          rw [← hpairs, ← hsum]; push_cast; rfl
  -- weak transitivity transfers to the ladder on `V`
  have hWTV : ∀ i, i + 1 ≤ 4 → ∀ x y, c' * (Fintype.card V : Real) ≤
      ((Finset.univ.filter fun z => R i x z ∧ R 1 z y).card : Real) → R (i + 1) x y := by
    intro i hi x y h
    rw [hcardV] at h
    have hpos : 0 < (Finset.univ.filter fun z => R i x z ∧ R 1 z y).card := by
      have : (0 : Real) < c' * X.card := mul_pos hc'0 (by exact_mod_cast hX.card_pos)
      exact_mod_cast this.trans_le h
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨⟨hx1, hx2, -, -, -⟩, ⟨-, -, hy1, hy2, -⟩⟩ := (Finset.mem_filter.mp hz).2
    refine ⟨hx1, hx2, hy1, hy2, hWT i hi _ _ _ _ (h.trans ?_)⟩
    have hinj : ((Finset.univ.filter fun z => R i x z ∧ R 1 z y).card : Real) ≤
        (((A ×ˢ A).filter fun p => Q i ((x : G) + d) x p.1 p.2 ∧
          Q 1 p.1 p.2 ((y : G) + d) y).card : Real) := by
      have := Finset.card_le_card_of_injOn (fun z : V => ((z : G) + d, (z : G)))
        (s := Finset.univ.filter fun z => R i x z ∧ R 1 z y)
        (t := (A ×ˢ A).filter fun p => Q i ((x : G) + d) x p.1 p.2 ∧
          Q 1 p.1 p.2 ((y : G) + d) y)
        (fun z hz => by
          obtain ⟨⟨-, -, hz1, hz2, hq1⟩, ⟨-, -, -, -, hq2⟩⟩ := (Finset.mem_filter.mp hz).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz2, hz1⟩, hq1, hq2⟩)
        (fun z _ w _ h => Subtype.ext (by simpa using congrArg Prod.snd h))
      exact_mod_cast this
    exact hinj
  obtain ⟨T, hT, hall⟩ := rel_four_on_four_walk_set R hsym hδ hedges
    (fun i hi x y h => hWTV i hi x y (by convert h using 3; ext z; simp only [Finset.mem_filter]))
    hc'
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hu
    exact x.2
  · rw [Finset.card_map, ← hcardV]; exact hT
  · intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨h1, h2, -, -, hq⟩ := hall x hx y hy
    exact ⟨h1, h2, hq⟩

end LeanProofs.GowersSzemeredi
