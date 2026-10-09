import GowersSzemeredi.Definitions

/-! Quasirandom bipartite graphs: [49] Appendix B (Lemmas 41 and 43).

For `f : X → Y → ℝ`, `boxSum f = Σ_{x₀,x₁} (Σ_y f(x₀,y) f(x₁,y))²` is the
unnormalized fourth power of the box norm, so `‖f‖□ ≤ ε` in [49]'s
normalization reads `boxSum f ≤ ε⁴|X|²|Y|²`.

* `box_correlation_pow_four_le` (Lemma 41, fourth-power form):
  `(Σ_{x,y} f(x,y)u(x)v(y))⁴ ≤ (Σu²)²(Σv²)²·boxSum f`, by two applications
  of Cauchy–Schwarz.
* `abs_box_correlation_le`: for `|u|,|v| ≤ 1` and `boxSum f ≤ ε⁴|X|²|Y|²`,
  the correlation is at most `ε|X||Y|`.
* `box_swap_bound`: one edge of a product pattern. If the summand is
  `f(x i₀, w j₀)·U·V` with `U` independent of `w j₀` and `V` independent
  of `x i₀`, both bounded by one, the sum over `x : I → X`, `w : J → Y` is
  at most `ε·|X^I|·|Y^J|`.
* `bipartite_counting`: for `0 ≤ G ≤ 1`, `0 ≤ δ ≤ 1` and
  `boxSum (G − δ) ≤ ε⁴|X|²|Y|²`, and weights `0 ≤ W ≤ 1` on `J → Y`,
  `Σ_{x,w} W(w) Π_{(i,j)} G(x i, w j)` is within `|I||J|ε|X^I||Y^J|` of
  `δ^{|I||J|}·|X^I|·Σ_w W(w)`. The proof telescopes over the set of
  edges kept from `G`, one `box_swap_bound` per edge.
* `common_neighbourhood_second_moment` (Lemma 43, second moment): for
  `M ⊆ Y^J`, with `C(x) = Σ_{y∈M} Π_{(i,j)} G(x i, y j)`,
  `Σ_x (C(x) − δ^{|I||J|}|M|)² ≤ 4|I||J|ε·|X^I|·|Y^J|²`.
* `common_neighbourhood_deviation_card` (Lemma 43): at most
  `4|I||J|ε η⁻²·|X^I|` tuples `x` have
  `|C(x) − δ^{|I||J|}|M|| ≥ η|Y^J|`. Lemma 42 is the case `|J| = 1`,
  `M = Y^J`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Finset

section Box

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The unnormalized fourth power of the box norm. -/
def boxSum (f : X → Y → ℝ) : ℝ :=
  ∑ x₀ : X, ∑ x₁ : X, (∑ y : Y, f x₀ y * f x₁ y) ^ 2

theorem boxSum_nonneg (f : X → Y → ℝ) : 0 ≤ boxSum f := by
  unfold boxSum; positivity

/-- **[49] Lemma 41, fourth-power form.** -/
theorem box_correlation_pow_four_le (f : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) :
    (∑ x, ∑ y, f x y * u x * v y) ^ 4 ≤
      (∑ x, u x ^ 2) ^ 2 * (∑ y, v y ^ 2) ^ 2 * boxSum f := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ y, (∑ x, f x y * u x) ^ 2 := ⟨_, rfl⟩
  have hS : (∑ x, ∑ y, f x y * u x * v y) = ∑ y, v y * (∑ x, f x y * u x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    ring
  have h1 : (∑ x, ∑ y, f x y * u x * v y) ^ 2 ≤ (∑ y, v y ^ 2) * T := by
    rw [hS, hT]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hTexp : T = ∑ p : X × X, (u p.1 * u p.2) * (∑ y, f p.1 y * f p.2 y) := by
    rw [hT, Fintype.sum_prod_type]
    simp_rw [sq, Finset.sum_mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x₀ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _
    ring
  have h2 : T ^ 2 ≤ (∑ x, u x ^ 2) ^ 2 * boxSum f := by
    rw [hTexp]
    calc _ ≤ (∑ p : X × X, (u p.1 * u p.2) ^ 2) *
          ∑ p : X × X, (∑ y, f p.1 y * f p.2 y) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by
          congr 1
          · rw [Fintype.sum_prod_type, pow_two (∑ x, u x ^ 2), Finset.sum_mul_sum]
            apply Finset.sum_congr rfl; intro _ _
            apply Finset.sum_congr rfl; intro _ _
            ring
          · unfold boxSum
            rw [Fintype.sum_prod_type]
  calc (∑ x, ∑ y, f x y * u x * v y) ^ 4 = ((∑ x, ∑ y, f x y * u x * v y) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ y, v y ^ 2) * T) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (∑ y, v y ^ 2) ^ 2 * T ^ 2 := by ring
    _ ≤ (∑ y, v y ^ 2) ^ 2 * ((∑ x, u x ^ 2) ^ 2 * boxSum f) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- A function bounded by one has squared mass at most the cardinality. -/
theorem sum_sq_le_card_of_abs_le_one {Z : Type*} [Fintype Z] (u : Z → ℝ)
    (hu : ∀ z, |u z| ≤ 1) : ∑ z, u z ^ 2 ≤ Fintype.card Z := by
  calc ∑ z, u z ^ 2 ≤ ∑ _z : Z, (1 : ℝ) := Finset.sum_le_sum fun z _ => by
        rw [← sq_abs]
        nlinarith [abs_nonneg (u z), hu z]
    _ = Fintype.card Z := by simp

/-- **[49] Lemma 41.** -/
theorem abs_box_correlation_le (f : X → Y → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbox : boxSum f ≤ ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)
    (u : X → ℝ) (v : Y → ℝ) (hu : ∀ x, |u x| ≤ 1) (hv : ∀ y, |v y| ≤ 1) :
    |∑ x, ∑ y, f x y * u x * v y| ≤ ε * Fintype.card X * Fintype.card Y := by
  have hu2 := sum_sq_le_card_of_abs_le_one u hu
  have hv2 := sum_sq_le_card_of_abs_le_one v hv
  have h4 := box_correlation_pow_four_le f u v
  have hb : |∑ x, ∑ y, f x y * u x * v y| ^ 4 ≤
      (ε * Fintype.card X * Fintype.card Y) ^ 4 := by
    have habs : |∑ x, ∑ y, f x y * u x * v y| ^ 4 = (∑ x, ∑ y, f x y * u x * v y) ^ 4 := by
      rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [habs]
    calc _ ≤ (∑ x, u x ^ 2) ^ 2 * (∑ y, v y ^ 2) ^ 2 * boxSum f := h4
      _ ≤ (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 *
          (ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2) := by
          have hu0 : 0 ≤ ∑ x, u x ^ 2 := by positivity
          have hv0 : 0 ≤ ∑ y, v y ^ 2 := by positivity
          have hb0 := boxSum_nonneg f
          gcongr
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num)).mp hb

end Box

section Split

variable {α β : Type*} [DecidableEq α]

theorem splitAt_symm_self (i : α) (a : β) (g : {j // j ≠ i} → β) :
    (Equiv.funSplitAt i β).symm (a, g) i = a := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem splitAt_symm_of_ne (i : α) (a : β) (g : {j // j ≠ i} → β) {j : α} (hj : j ≠ i) :
    (Equiv.funSplitAt i β).symm (a, g) j = g ⟨j, hj⟩ := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]

theorem splitAt_symm_eq_update (i : α) (a a' : β) (g : {j // j ≠ i} → β) :
    (Equiv.funSplitAt i β).symm (a, g) =
      Function.update ((Equiv.funSplitAt i β).symm (a', g)) i a := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, splitAt_symm_self]
  · rw [Function.update_of_ne hj, splitAt_symm_of_ne _ _ _ hj, splitAt_symm_of_ne _ _ _ hj]

end Split

section Counting

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **One edge of a product pattern.** -/
theorem box_swap_bound (f : X → Y → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbox : boxSum f ≤ ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)
    (i₀ : I) (j₀ : J) (U V : (I → X) → (J → Y) → ℝ)
    (hU : ∀ x w, |U x w| ≤ 1) (hV : ∀ x w, |V x w| ≤ 1)
    (hUw : ∀ x w b, U x (Function.update w j₀ b) = U x w)
    (hVx : ∀ x w a, V (Function.update x i₀ a) w = V x w) :
    |∑ x : I → X, ∑ w : J → Y, f (x i₀) (w j₀) * U x w * V x w| ≤
      ε * Fintype.card (I → X) * Fintype.card (J → Y) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨a₀⟩⟩
  · haveI : IsEmpty (I → X) := ⟨fun x => hX.false (x i₀)⟩
    simp
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨b₀⟩⟩
  · haveI : IsEmpty (J → Y) := ⟨fun w => hY.false (w j₀)⟩
    simp
  let sX := (Equiv.funSplitAt i₀ X).symm
  let sY := (Equiv.funSplitAt j₀ Y).symm
  let F : (I → X) → (J → Y) → ℝ := fun x w => f (x i₀) (w j₀) * U x w * V x w
  have hsum : ∑ x : I → X, ∑ w : J → Y, F x w =
      ∑ x' : {i // i ≠ i₀} → X, ∑ w' : {j // j ≠ j₀} → Y,
        ∑ a : X, ∑ b : Y, F (sX (a, x')) (sY (b, w')) := by
    calc ∑ x : I → X, ∑ w : J → Y, F x w
        = ∑ p : X × ({i // i ≠ i₀} → X), ∑ w : J → Y, F (sX p) w :=
          (Equiv.sum_comp sX (fun x => ∑ w : J → Y, F x w)).symm
      _ = ∑ p : X × ({i // i ≠ i₀} → X), ∑ q : Y × ({j // j ≠ j₀} → Y),
            F (sX p) (sY q) :=
          Finset.sum_congr rfl fun p _ => (Equiv.sum_comp sY (fun w => F (sX p) w)).symm
      _ = ∑ a : X, ∑ x' : {i // i ≠ i₀} → X, ∑ b : Y, ∑ w' : {j // j ≠ j₀} → Y,
            F (sX (a, x')) (sY (b, w')) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ x' : {i // i ≠ i₀} → X, ∑ a : X, ∑ b : Y, ∑ w' : {j // j ≠ j₀} → Y,
            F (sX (a, x')) (sY (b, w')) := Finset.sum_comm
      _ = ∑ x' : {i // i ≠ i₀} → X, ∑ a : X, ∑ w' : {j // j ≠ j₀} → Y, ∑ b : Y,
            F (sX (a, x')) (sY (b, w')) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hinner : ∀ (x' : {i // i ≠ i₀} → X) (w' : {j // j ≠ j₀} → Y),
      |∑ a : X, ∑ b : Y, F (sX (a, x')) (sY (b, w'))| ≤
        ε * Fintype.card X * Fintype.card Y := by
    intro x' w'
    have hF : ∀ a b, F (sX (a, x')) (sY (b, w')) =
        f a b * U (sX (a, x')) (sY (b₀, w')) * V (sX (a₀, x')) (sY (b, w')) := by
      intro a b
      simp only [F]
      have hx : sX (a, x') i₀ = a := splitAt_symm_self i₀ a x'
      have hw : sY (b, w') j₀ = b := splitAt_symm_self j₀ b w'
      have hUe : U (sX (a, x')) (sY (b, w')) = U (sX (a, x')) (sY (b₀, w')) := by
        rw [show sY (b, w') = Function.update (sY (b₀, w')) j₀ b from
          splitAt_symm_eq_update j₀ b b₀ w', hUw]
      have hVe : V (sX (a, x')) (sY (b, w')) = V (sX (a₀, x')) (sY (b, w')) := by
        rw [show sX (a, x') = Function.update (sX (a₀, x')) i₀ a from
          splitAt_symm_eq_update i₀ a a₀ x', hVx]
      rw [hx, hw, hUe, hVe]
    simp_rw [hF]
    exact abs_box_correlation_le f hε hbox _ _ (fun a => hU _ _) (fun b => hV _ _)
  have hcardX : (Fintype.card (I → X) : ℝ) =
      Fintype.card X * Fintype.card ({i // i ≠ i₀} → X) := by
    rw [Fintype.card_congr (Equiv.funSplitAt i₀ X), Fintype.card_prod]; push_cast; ring
  have hcardY : (Fintype.card (J → Y) : ℝ) =
      Fintype.card Y * Fintype.card ({j // j ≠ j₀} → Y) := by
    rw [Fintype.card_congr (Equiv.funSplitAt j₀ Y), Fintype.card_prod]; push_cast; ring
  show |∑ x : I → X, ∑ w : J → Y, F x w| ≤ _
  rw [hsum]
  calc _ ≤ ∑ x' : {i // i ≠ i₀} → X, |∑ w' : {j // j ≠ j₀} → Y,
          ∑ a : X, ∑ b : Y, F (sX (a, x')) (sY (b, w'))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x' : {i // i ≠ i₀} → X, ∑ _w' : {j // j ≠ j₀} → Y,
          ε * Fintype.card X * Fintype.card Y := by
        apply Finset.sum_le_sum; intro x' _
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun w' _ => hinner x' w')
    _ = _ := by
        rw [hcardX, hcardY]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- One factor of a partially replaced product: an edge of `G` if the
index lies in `S`, the constant `δ` otherwise. -/
def edgeFactor (G : X → Y → ℝ) (δ : ℝ) (S : Finset (I × J)) (x : I → X) (w : J → Y)
    (q : I × J) : ℝ :=
  if q ∈ S then G (x q.1) (w q.2) else δ

theorem edgeFactor_mem_Icc {G : X → Y → ℝ} {δ : ℝ} (hG0 : ∀ x y, 0 ≤ G x y)
    (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset (I × J))
    (x : I → X) (w : J → Y) (q : I × J) :
    0 ≤ edgeFactor G δ S x w q ∧ edgeFactor G δ S x w q ≤ 1 := by
  unfold edgeFactor
  split_ifs
  · exact ⟨hG0 _ _, hG1 _ _⟩
  · exact ⟨hδ0, hδ1⟩

theorem prod_edgeFactor_abs_le {G : X → Y → ℝ} {δ : ℝ} (hG0 : ∀ x y, 0 ≤ G x y)
    (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (S T : Finset (I × J))
    (x : I → X) (w : J → Y) : |∏ q ∈ T, edgeFactor G δ S x w q| ≤ 1 := by
  have h := fun q => edgeFactor_mem_Icc hG0 hG1 hδ0 hδ1 S x w q
  rw [abs_of_nonneg (Finset.prod_nonneg fun q _ => (h q).1)]
  exact Finset.prod_le_one (fun q _ => (h q).1) fun q _ => (h q).2

/-- The weighted sum of the partially replaced product. -/
def edgeSum (G : X → Y → ℝ) (δ : ℝ) (W : (J → Y) → ℝ) (S : Finset (I × J)) : ℝ :=
  ∑ x : I → X, ∑ w : J → Y, W w * ∏ q : I × J, edgeFactor G δ S x w q

/-- Adding one edge changes the weighted sum by at most `ε|X^I||Y^J|`. -/
theorem edgeSum_insert_sub_le {G : X → Y → ℝ} {δ ε : ℝ} (hG0 : ∀ x y, 0 ≤ G x y)
    (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hbox : boxSum (fun x y => G x y - δ) ≤
      ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)
    {W : (J → Y) → ℝ} (hW0 : ∀ w, 0 ≤ W w) (hW1 : ∀ w, W w ≤ 1)
    (S : Finset (I × J)) {p : I × J} (hp : p ∉ S) :
    |edgeSum G δ W (insert p S) - edgeSum G δ W S| ≤
      ε * Fintype.card (I → X) * Fintype.card (J → Y) := by
  let U : (I → X) → (J → Y) → ℝ := fun x w =>
    ∏ q ∈ (Finset.univ.erase p).filter (fun q => q.1 = p.1), edgeFactor G δ S x w q
  let V : (I → X) → (J → Y) → ℝ := fun x w =>
    W w * ∏ q ∈ (Finset.univ.erase p).filter (fun q => q.1 ≠ p.1), edgeFactor G δ S x w q
  have hsplit : ∀ (T : Finset (I × J)) (x : I → X) (w : J → Y),
      (∀ q, q ≠ p → (q ∈ T ↔ q ∈ S)) →
      ∏ q : I × J, edgeFactor G δ T x w q =
        edgeFactor G δ T x w p * U x w *
          ∏ q ∈ (Finset.univ.erase p).filter (fun q => q.1 ≠ p.1), edgeFactor G δ S x w q := by
    intro T x w hT
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
      ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase p) (fun q => q.1 = p.1)]
    have hcong : ∀ q ∈ Finset.univ.erase p, edgeFactor G δ T x w q = edgeFactor G δ S x w q := by
      intro q hq
      unfold edgeFactor
      rw [if_congr (hT q (Finset.ne_of_mem_erase hq)) rfl rfl]
    rw [Finset.prod_congr rfl fun q hq => hcong q (Finset.mem_of_mem_filter q hq),
      Finset.prod_congr rfl fun q hq => hcong q (Finset.mem_of_mem_filter q hq)]
    simp only [U, mul_assoc]
  have hdiff : edgeSum G δ W (insert p S) - edgeSum G δ W S =
      ∑ x : I → X, ∑ w : J → Y, (fun x y => G x y - δ) (x p.1) (w p.2) * U x w * V x w := by
    unfold edgeSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro w _
    rw [hsplit (insert p S) x w (fun q hq => by simp [hq]),
      hsplit S x w (fun q _ => Iff.rfl)]
    have h1 : edgeFactor G δ (insert p S) x w p = G (x p.1) (w p.2) := by
      unfold edgeFactor; rw [if_pos (Finset.mem_insert_self p S)]
    have h2 : edgeFactor G δ S x w p = δ := by
      unfold edgeFactor; rw [if_neg hp]
    rw [h1, h2]
    simp only [V]
    ring
  rw [hdiff]
  apply box_swap_bound _ hε hbox p.1 p.2 U V
  · intro x w; exact prod_edgeFactor_abs_le hG0 hG1 hδ0 hδ1 S _ x w
  · intro x w
    simp only [V]
    rw [abs_mul, abs_of_nonneg (hW0 w)]
    exact mul_le_one₀ (hW1 w) (abs_nonneg _) (prod_edgeFactor_abs_le hG0 hG1 hδ0 hδ1 S _ x w)
  · intro x w b
    simp only [U]
    apply Finset.prod_congr rfl
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq'.1
    have h2 : q.2 ≠ p.2 := fun h => hqp (Prod.ext hq'.2 h)
    unfold edgeFactor
    rw [Function.update_of_ne h2]
  · intro x w a
    simp only [V]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    have h1 : q.1 ≠ p.1 := (Finset.mem_filter.mp hq).2
    unfold edgeFactor
    rw [Function.update_of_ne h1]

/-- **The bipartite counting lemma.** -/
theorem bipartite_counting {G : X → Y → ℝ} {δ ε : ℝ} (hG0 : ∀ x y, 0 ≤ G x y)
    (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hbox : boxSum (fun x y => G x y - δ) ≤
      ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)
    (W : (J → Y) → ℝ) (hW0 : ∀ w, 0 ≤ W w) (hW1 : ∀ w, W w ≤ 1) :
    |∑ x : I → X, ∑ w : J → Y, W w * ∏ q : I × J, G (x q.1) (w q.2) -
        δ ^ (Fintype.card I * Fintype.card J) * Fintype.card (I → X) * ∑ w : J → Y, W w| ≤
      Fintype.card I * Fintype.card J * ε * Fintype.card (I → X) * Fintype.card (J → Y) := by
  have hind : ∀ S : Finset (I × J), |edgeSum G δ W S - edgeSum G δ W (∅ : Finset (I × J))| ≤
      S.card * (ε * Fintype.card (I → X) * Fintype.card (J → Y)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert p S hp ih =>
      rw [Finset.card_insert_of_notMem hp]
      have hstep := edgeSum_insert_sub_le hG0 hG1 hδ0 hδ1 hε hbox hW0 hW1 S hp
      calc _ ≤ |edgeSum G δ W (insert p S) - edgeSum G δ W S| +
            |edgeSum G δ W S - edgeSum G δ W (∅ : Finset (I × J))| := abs_sub_le _ _ _
        _ ≤ _ := by push_cast; linarith
  have hfull : edgeSum G δ W (Finset.univ : Finset (I × J)) =
      ∑ x : I → X, ∑ w : J → Y, W w * ∏ q : I × J, G (x q.1) (w q.2) := by
    unfold edgeSum edgeFactor
    simp only [Finset.mem_univ, if_true]
  have hempty : edgeSum G δ W (∅ : Finset (I × J)) =
      δ ^ (Fintype.card I * Fintype.card J) * Fintype.card (I → X) * ∑ w : J → Y, W w := by
    unfold edgeSum edgeFactor
    simp only [Finset.notMem_empty, if_false, Finset.prod_const, Finset.card_univ,
      Fintype.card_prod]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro w _
    ring
  have h := hind Finset.univ
  rw [hfull, hempty, Finset.card_univ, Fintype.card_prod] at h
  push_cast at h
  linarith

/-- The common-neighbourhood count of an `I`-tuple inside `M ⊆ Y^J`. -/
def commonCount (G : X → Y → ℝ) (M : Finset (J → Y)) (x : I → X) : ℝ :=
  ∑ y ∈ M, ∏ q : I × J, G (x q.1) (y q.2)

theorem sum_indicator_eq_card (M : Finset (J → Y)) :
    ∑ w : J → Y, (if w ∈ M then (1 : ℝ) else 0) = M.card := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The square of a common count is a count over pairs of `J`-tuples. -/
theorem commonCount_sq (G : X → Y → ℝ) (M : Finset (J → Y)) (x : I → X) :
    commonCount G M x ^ 2 =
      ∑ w : J ⊕ J → Y, (if w ∘ Sum.inl ∈ M then (1 : ℝ) else 0) *
        (if w ∘ Sum.inr ∈ M then (1 : ℝ) else 0) *
          ∏ q : I × (J ⊕ J), G (x q.1) (w q.2) := by
  obtain ⟨P, hP⟩ : ∃ P : (J → Y) → ℝ, P = fun y => ∏ q : I × J, G (x q.1) (y q.2) :=
    ⟨_, rfl⟩
  have hprod : ∀ y z : J → Y,
      ∏ q : I × (J ⊕ J), G (x q.1) (Sum.elim y z q.2) = P y * P z := by
    intro y z
    rw [hP]
    simp only [Fintype.prod_prod_type, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_mul_distrib]
  have hrhs : (∑ w : J ⊕ J → Y, (if w ∘ Sum.inl ∈ M then (1 : ℝ) else 0) *
        (if w ∘ Sum.inr ∈ M then (1 : ℝ) else 0) * ∏ q : I × (J ⊕ J), G (x q.1) (w q.2)) =
      ∑ y : J → Y, ∑ z : J → Y, (if y ∈ M then (1 : ℝ) else 0) *
        (if z ∈ M then (1 : ℝ) else 0) * (P y * P z) := by
    rw [← (Equiv.sumArrowEquivProdArrow J J Y).symm.sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro z _
    change (if Sum.elim y z ∘ Sum.inl ∈ M then (1 : ℝ) else 0) *
        (if Sum.elim y z ∘ Sum.inr ∈ M then (1 : ℝ) else 0) *
          ∏ q : I × (J ⊕ J), G (x q.1) (Sum.elim y z q.2) = _
    rw [Sum.elim_comp_inl, Sum.elim_comp_inr, hprod]
  have hC : commonCount G M x = ∑ y ∈ M, P y := by rw [hP]; rfl
  rw [hrhs, hC, sq, Finset.sum_mul_sum]
  have hin : ∀ y : J → Y, ∑ z : J → Y, (if y ∈ M then (1 : ℝ) else 0) *
      (if z ∈ M then (1 : ℝ) else 0) * (P y * P z) =
      if y ∈ M then ∑ z : J → Y, (if z ∈ M then P y * P z else 0) else 0 := by
    intro y
    split_ifs with hy
    · apply Finset.sum_congr rfl; intro z _
      split_ifs <;> simp
    · simp
  simp_rw [hin]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_boole_mul_eq_sum_mem (M : Finset (J → Y)) (g : (J → Y) → ℝ) :
    ∑ w : J → Y, (if w ∈ M then (1 : ℝ) else 0) * g w = ∑ w ∈ M, g w := by
  simp only [boole_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **[49] Lemma 43, second moment.** -/
theorem common_neighbourhood_second_moment {G : X → Y → ℝ} {δ ε : ℝ}
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε)
    (hbox : boxSum (fun x y => G x y - δ) ≤
      ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)
    (M : Finset (J → Y)) :
    ∑ x : I → X, (commonCount G M x - δ ^ (Fintype.card I * Fintype.card J) * M.card) ^ 2 ≤
      4 * Fintype.card I * Fintype.card J * ε * Fintype.card (I → X) *
        (Fintype.card (J → Y) : ℝ) ^ 2 := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = δ ^ (Fintype.card I * Fintype.card J) * M.card := ⟨_, rfl⟩
  rw [← hD]
  obtain ⟨NX, hNX⟩ : ∃ NX : ℝ, NX = Fintype.card (I → X) := ⟨_, rfl⟩
  obtain ⟨NY, hNY⟩ : ∃ NY : ℝ, NY = Fintype.card (J → Y) := ⟨_, rfl⟩
  rw [← hNX, ← hNY]
  have hA := bipartite_counting (I := I) (J := J) hG0 hG1 hδ0 hδ1 hε hbox
    (fun w => if w ∈ M then (1 : ℝ) else 0) (fun w => by split_ifs <;> norm_num)
    (fun w => by split_ifs <;> norm_num)
  have hB := bipartite_counting (I := I) (J := J ⊕ J) hG0 hG1 hδ0 hδ1 hε hbox
    (fun w => (if w ∘ Sum.inl ∈ M then (1 : ℝ) else 0) * (if w ∘ Sum.inr ∈ M then (1 : ℝ) else 0))
    (fun w => by split_ifs <;> norm_num) (fun w => by split_ifs <;> norm_num)
  have hAeq : ∑ x : I → X, ∑ w : J → Y, (if w ∈ M then (1 : ℝ) else 0) *
      ∏ q : I × J, G (x q.1) (w q.2) = ∑ x : I → X, commonCount G M x := by
    apply Finset.sum_congr rfl; intro x _
    rw [sum_boole_mul_eq_sum_mem]; rfl
  have hBeq : ∑ x : I → X, ∑ w : J ⊕ J → Y, (if w ∘ Sum.inl ∈ M then (1 : ℝ) else 0) *
      (if w ∘ Sum.inr ∈ M then (1 : ℝ) else 0) * ∏ q : I × (J ⊕ J), G (x q.1) (w q.2) =
      ∑ x : I → X, commonCount G M x ^ 2 := by
    apply Finset.sum_congr rfl; intro x _
    rw [commonCount_sq]
  have hW1 : ∑ w : J → Y, (if w ∈ M then (1 : ℝ) else 0) = M.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hW2 : ∑ w : J ⊕ J → Y, (if w ∘ Sum.inl ∈ M then (1 : ℝ) else 0) *
      (if w ∘ Sum.inr ∈ M then (1 : ℝ) else 0) = (M.card : ℝ) ^ 2 := by
    rw [← (Equiv.sumArrowEquivProdArrow J J Y).symm.sum_comp, Fintype.sum_prod_type]
    change ∑ y : J → Y, ∑ z : J → Y, (if Sum.elim y z ∘ Sum.inl ∈ M then (1 : ℝ) else 0) *
        (if Sum.elim y z ∘ Sum.inr ∈ M then (1 : ℝ) else 0) = _
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [sq, ← hW1, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro z _
    congr
  have hcardJJ : Fintype.card (J ⊕ J) = 2 * Fintype.card J := by
    rw [Fintype.card_sum]; ring
  have hcardF : (Fintype.card (J ⊕ J → Y) : ℝ) = NY ^ 2 := by
    rw [hNY, Fintype.card_fun, Fintype.card_fun, Fintype.card_sum]
    push_cast
    ring
  rw [hAeq, hW1, ← hNX, ← hNY] at hA
  rw [hBeq, hW2, ← hNX, hcardF, hcardJJ] at hB
  have hpow : δ ^ (Fintype.card I * (2 * Fintype.card J)) * NX * (M.card : ℝ) ^ 2 =
      NX * D ^ 2 := by
    rw [hD, show Fintype.card I * (2 * Fintype.card J) =
      (Fintype.card I * Fintype.card J) * 2 by ring, pow_mul]
    ring
  rw [hpow] at hB
  push_cast at hB
  have hA' : δ ^ (Fintype.card I * Fintype.card J) * NX * (M.card : ℝ) = NX * D := by
    rw [hD]; ring
  rw [hA'] at hA
  obtain ⟨hA1, _⟩ := abs_le.mp hA
  obtain ⟨_, hB2⟩ := abs_le.mp hB
  have hexp : ∑ x : I → X, (commonCount G M x - D) ^ 2 =
      ∑ x : I → X, commonCount G M x ^ 2 - 2 * D * ∑ x : I → X, commonCount G M x +
        NX * D ^ 2 := by
    have h : ∀ x : I → X, (commonCount G M x - D) ^ 2 =
        commonCount G M x ^ 2 - 2 * D * commonCount G M x + D ^ 2 := fun x => by ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hNX]
  rw [hexp]
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hDle : D ≤ NY := by
    rw [hD, hNY]
    have h1 : δ ^ (Fintype.card I * Fintype.card J) ≤ 1 := pow_le_one₀ hδ0 hδ1
    have h2 : (M.card : ℝ) ≤ Fintype.card (J → Y) := by
      exact_mod_cast (show M.card ≤ Fintype.card (J → Y) by
        simpa using Finset.card_le_univ M)
    calc δ ^ (Fintype.card I * Fintype.card J) * (M.card : ℝ) ≤ 1 * Fintype.card (J → Y) :=
          mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = _ := one_mul _
  have hNX0 : 0 ≤ NX := by rw [hNX]; positivity
  have hK : 0 ≤ (Fintype.card I : ℝ) * Fintype.card J * ε * NX * NY := by
    have : (0 : ℝ) ≤ NY := hD0.trans hDle
    positivity
  have hDK := mul_le_mul_of_nonneg_left hDle hK
  nlinarith

/-- **[49] Lemma 43.** Few `I`-tuples have an atypical common neighbourhood
count in `M`. -/
theorem common_neighbourhood_deviation_card [Nonempty Y] {G : X → Y → ℝ} {δ ε : ℝ}
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x y, G x y ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε)
    (hbox : boxSum (fun x y => G x y - δ) ≤
      ε ^ 4 * (Fintype.card X : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2)
    (M : Finset (J → Y)) {η : ℝ} (hη : 0 ≤ η) :
    ((Finset.univ.filter fun x : I → X => η * Fintype.card (J → Y) ≤
        |commonCount G M x - δ ^ (Fintype.card I * Fintype.card J) * M.card|).card : ℝ) *
        η ^ 2 ≤
      4 * Fintype.card I * Fintype.card J * ε * Fintype.card (I → X) := by
  have h2 := common_neighbourhood_second_moment (I := I) hG0 hG1 hδ0 hδ1 hε hbox M
  have hNY : (0 : ℝ) < Fintype.card (J → Y) := by exact_mod_cast Fintype.card_pos
  set F := Finset.univ.filter fun x : I → X => η * Fintype.card (J → Y) ≤
    |commonCount G M x - δ ^ (Fintype.card I * Fintype.card J) * M.card| with hF
  have hmark : (F.card : ℝ) * (η * Fintype.card (J → Y)) ^ 2 ≤
      ∑ x : I → X, (commonCount G M x - δ ^ (Fintype.card I * Fintype.card J) * M.card) ^ 2 := by
    calc (F.card : ℝ) * (η * Fintype.card (J → Y)) ^ 2 =
          ∑ _x ∈ F, (η * Fintype.card (J → Y) : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ F, (commonCount G M x -
            δ ^ (Fintype.card I * Fintype.card J) * M.card) ^ 2 := by
          apply Finset.sum_le_sum; intro x hx
          have h := (Finset.mem_filter.mp hx).2
          rw [← sq_abs (commonCount G M x - _)]
          exact pow_le_pow_left₀ (by positivity) h 2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
  have h3 : ((F.card : ℝ) * η ^ 2) * (Fintype.card (J → Y) : ℝ) ^ 2 ≤
      (4 * Fintype.card I * Fintype.card J * ε * Fintype.card (I → X)) *
        (Fintype.card (J → Y) : ℝ) ^ 2 := by
    calc ((F.card : ℝ) * η ^ 2) * (Fintype.card (J → Y) : ℝ) ^ 2 =
          (F.card : ℝ) * (η * Fintype.card (J → Y)) ^ 2 := by ring
      _ ≤ _ := hmark.trans h2
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 (by positivity)

end Counting

end LeanProofs.GowersSzemeredi
