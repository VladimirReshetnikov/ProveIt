import GowersSzemeredi.Proofs16AbstractBSGUnion

/-! Claim 4.4 of Milićević's abstract Balog–Szemerédi–Gowers theorem
(arXiv:2601.01682, printed pp. 50–51), in four-walk form.

Let `P ⊆ A × A` be a graph with property (20) for `Q 4`: two edges with the
same difference are `Q 4`-related. Suppose that between any two vertices of
`B` there are at least `η|X|^3` four-walks `walkSet P X u v` with
intermediate vertices in `X`. Then for `B₁, B₂ ⊆ B` of densities
`ε₁, ε₂`, many additive quadruples `(b₁, b₁′, b₂, b₂′) ∈ B₁² × B₂²` lie in
`Q 16`.
* `chainCount_three_eq_card`: `chainCount r S 3` as a filtered card.
* `collisions_ge`: fiber Cauchy–Schwarz,
  `|W|² ≤ |D|·#{(w,w′) : f w = f w′}` when `f` maps `W` into `D`.
* `claim_4_4`: the claim, with `κ = (ε₁ε₂η)²/K⁴`. At least `(κ/2)|X|³`
  additive quadruples lie in `Q 16`, provided `16c′ ≤ κ`.

Proof: count the walks `b₁–z₁–z₂–z₃–b₂`. Apply Cauchy–Schwarz over
their difference sequences, of which there are at most `(K|X|)⁴`. Two walks
with equal differences give, by (20) and the symmetry (S3), a `Q 4`-chain of
pairs of the same difference `e = b₁ − b₁′`. Averaging over quadruples and
the weak-transitivity ladder (`rel_of_chainCount`) at levels `4i` then
give `Q 16`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

theorem chainCount_three_eq_card {V : Type*} (r : V → V → Prop) (S : Finset V) (u v : V) :
    chainCount r S 3 u v = ((S ×ˢ S ×ˢ S).filter fun t =>
      r u t.2.2 ∧ r t.2.2 t.2.1 ∧ r t.2.1 t.1 ∧ r t.1 v).card := by
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_congr rfl fun _ _ => Finset.sum_product _ _ _]
  simp only [chainCount, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x3 _
  apply Finset.sum_congr rfl; intro x2 _
  apply Finset.sum_congr rfl; intro x1 _
  by_cases h1 : r u x1 <;> by_cases h2 : r x1 x2 <;> by_cases h3 : r x2 x3 <;>
    by_cases h4 : r x3 v <;> simp [h1, h2, h3, h4]

/-- **Fiber Cauchy–Schwarz.** -/
theorem collisions_ge {α β : Type*} (W : Finset α) (f : α → β) (D : Finset β)
    (hf : ∀ w ∈ W, f w ∈ D) :
    (W.card : Real) ^ 2 ≤ D.card * ((W ×ˢ W).filter fun p => f p.1 = f p.2).card := by
  let F : β → Finset α := fun y => W.filter fun w => f w = y
  have hW : W.card = ∑ y ∈ D, (F y).card := Finset.card_eq_sum_card_fiberwise hf
  have hC : ((W ×ˢ W).filter fun p => f p.1 = f p.2).card = ∑ y ∈ D, (F y).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => f p.1)
      (t := D) (fun p hp => hf p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
    apply Finset.sum_congr rfl
    intro y _
    rw [sq, ← Finset.card_product]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, F]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, h2, h3 ▸ h4⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩
      exact ⟨⟨⟨h1, h2⟩, h4.trans h3.symm⟩, h4⟩
  have hcs := sq_sum_le_card_mul_sum_sq (s := D) (f := fun y => ((F y).card : Real))
  rw [hW, hC]
  push_cast
  exact hcs

/-- Four-walks from `u` to `v` with intermediate vertices in `X`. -/
def walkSet {G : Type*} (P : Finset (G × G)) (X : Finset G) (u v : G) : Finset (G × G × G) :=
  (X ×ˢ X ×ˢ X).filter fun t =>
    (u, t.1) ∈ P ∧ (t.1, t.2.1) ∈ P ∧ (t.2.1, t.2.2) ∈ P ∧ (t.2.2, v) ∈ P

/-- Walk tuples `(b₁, (z₁, z₂, z₃), b₂)` with `b₁ ∈ B₁`, `b₂ ∈ B₂`. -/
def walkTuples {G : Type*} (P : Finset (G × G)) (X B₁ B₂ : Finset G) :
    Finset (G × (G × G × G) × G) :=
  (B₁ ×ˢ (X ×ˢ X ×ˢ X) ×ˢ B₂).filter fun w =>
    (w.1, w.2.1.1) ∈ P ∧ (w.2.1.1, w.2.1.2.1) ∈ P ∧ (w.2.1.2.1, w.2.1.2.2) ∈ P ∧
      (w.2.1.2.2, w.2.2) ∈ P

theorem walkTuples_card {G : Type*} (P : Finset (G × G)) (X B₁ B₂ : Finset G) :
    (walkTuples P X B₁ B₂).card = ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂, (walkSet P X b₁ b₂).card := by
  unfold walkTuples walkSet
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro b₁ _
  rw [Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b₂ _
  rw [Finset.card_filter]

/-- The difference sequence of a walk tuple. -/
def walkDiffs {G : Type*} [AddCommGroup G] (w : G × (G × G × G) × G) : G × G × G × G :=
  (w.1 - w.2.1.1, w.2.1.1 - w.2.1.2.1, w.2.1.2.1 - w.2.1.2.2, w.2.1.2.2 - w.2.2)

/-- Pairs of difference `e`, related at level `4i`: `(x, x − e)` to `(y, y − e)`. -/
def shiftRel {G : Type*} [AddCommGroup G] (A : Finset G) (Q : Nat → G → G → G → G → Prop)
    (e : G) (i : Nat) (x y : G) : Prop :=
  x ∈ A ∧ x - e ∈ A ∧ y ∈ A ∧ y - e ∈ A ∧ Q (4 * i) x (x - e) y (y - e)

/-- Two edges with the same difference give one link of the shifted ladder. -/
theorem shiftRel_one_of_edges {G : Type*} [AddCommGroup G] {A : Finset G} {P : Finset (G × G)}
    (hPA : P ⊆ A ×ˢ A) (Q : Nat → G → G → G → G → Prop)
    (h20 : ∀ p ∈ P, ∀ q ∈ P, p.1 - p.2 = q.1 - q.2 → Q 4 p.1 p.2 q.1 q.2)
    (hS3 : ∀ i a₁ a₂ a₃ a₄, Q i a₁ a₂ a₃ a₄ → Q i a₁ a₃ a₂ a₄) {e x y : G}
    (hxy : (x, y) ∈ P) (hxy' : (x - e, y - e) ∈ P) : shiftRel A Q e 1 x y := by
  have h1 := Finset.mem_product.mp (hPA hxy)
  have h2 := Finset.mem_product.mp (hPA hxy')
  have hq := h20 _ hxy _ hxy' (by simp only; abel)
  exact ⟨h1.1, h2.1, h1.2, h2.2, by simpa using hS3 4 _ _ _ _ hq⟩

/-- **Claim 4.4, four-walk form.** -/
theorem claim_4_4 {G : Type*} [AddCommGroup G] {A X B B₁ B₂ : Finset G}
    (hAX : A ⊆ X) (hBA : B ⊆ A) (hB₁ : B₁ ⊆ B) (hB₂ : B₂ ⊆ B) (hX : X.Nonempty)
    {P : Finset (G × G)} (hPA : P ⊆ A ×ˢ A) (Q : Nat → G → G → G → G → Prop)
    (h20 : ∀ p ∈ P, ∀ q ∈ P, p.1 - p.2 = q.1 - q.2 → Q 4 p.1 p.2 q.1 q.2)
    (hS3 : ∀ i a₁ a₂ a₃ a₄, Q i a₁ a₂ a₃ a₄ → Q i a₁ a₃ a₂ a₄)
    {c' K η ε₁ ε₂ : Real} (hc'0 : 0 < c')
    (hWT : ∀ i j a₁ a₂ a₃ a₄, c' * X.card ≤ (((A ×ˢ A).filter fun p =>
        Q i a₁ a₂ p.1 p.2 ∧ Q j p.1 p.2 a₃ a₄).card : Real) → Q (i + j) a₁ a₂ a₃ a₄)
    (hK : 0 < K) (hdoub : ((X - X).card : Real) ≤ K * X.card)
    (hη : 0 ≤ η) (hwalk : ∀ u ∈ B, ∀ v ∈ B, η * (X.card : Real) ^ 3 ≤ (walkSet P X u v).card)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hB₁c : ε₁ * X.card ≤ (B₁.card : Real)) (hB₂c : ε₂ * X.card ≤ (B₂.card : Real))
    (hc' : 16 * c' ≤ (ε₁ * ε₂ * η) ^ 2 / K ^ 4) :
    (ε₁ * ε₂ * η) ^ 2 / K ^ 4 / 2 * (X.card : Real) ^ 3 ≤
      ((B₁ ×ˢ B₁ ×ˢ B₂ ×ˢ B₂).filter fun q =>
        q.1 - q.2.1 = q.2.2.1 - q.2.2.2 ∧ Q 16 q.1 q.2.1 q.2.2.1 q.2.2.2).card := by
  set κ : Real := (ε₁ * ε₂ * η) ^ 2 / K ^ 4 with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hXpos : (0 : Real) < X.card := by exact_mod_cast hX.card_pos
  have hBX : B ⊆ X := hBA.trans hAX
  -- the relation ladder at shift `e`
  let R : G → Nat → G → G → Prop := shiftRel A Q
  have hWTR : ∀ e i x y, c' * X.card ≤ ((X.filter fun z => R e i x z ∧ R e 1 z y).card : Real) →
      R e (i + 1) x y := by
    intro e i x y h
    have hpos : 0 < (X.filter fun z => R e i x z ∧ R e 1 z y).card := by
      have : (0 : Real) < c' * X.card := mul_pos hc'0 hXpos
      exact_mod_cast this.trans_le h
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨⟨hx1, hx2, -, -, -⟩, ⟨-, -, hy1, hy2, -⟩⟩ := (Finset.mem_filter.mp hz).2
    refine ⟨hx1, hx2, hy1, hy2, ?_⟩
    rw [show 4 * (i + 1) = 4 * i + 4 by ring]
    apply hWT (4 * i) 4
    refine h.trans ?_
    have := Finset.card_le_card_of_injOn (fun z : G => (z, z - e))
      (s := X.filter fun z => R e i x z ∧ R e 1 z y)
      (t := (A ×ˢ A).filter fun p => Q (4 * i) x (x - e) p.1 p.2 ∧ Q 4 p.1 p.2 y (y - e))
      (fun z hz => by
        obtain ⟨⟨-, -, hz1, hz2, hq1⟩, ⟨-, -, -, -, hq2⟩⟩ := (Finset.mem_filter.mp hz).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz1, hz2⟩, hq1, by
          simpa using hq2⟩)
      (fun z _ w _ h => by simpa using congrArg Prod.fst h)
    exact_mod_cast this
  -- Step 1: walk tuples
  let W := walkTuples P X B₁ B₂
  have hWge : (B₁.card : Real) * B₂.card * (η * (X.card : Real) ^ 3) ≤ W.card := by
    have h := walkTuples_card P X B₁ B₂
    have : (B₁.card : Real) * B₂.card * (η * (X.card : Real) ^ 3) ≤
        ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂, ((walkSet P X b₁ b₂).card : Real) := by
      calc (B₁.card : Real) * B₂.card * (η * (X.card : Real) ^ 3)
          = ∑ _b₁ ∈ B₁, ∑ _b₂ ∈ B₂, η * (X.card : Real) ^ 3 := by
            rw [Finset.sum_const, Finset.sum_const]; simp only [nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum fun b₁ hb₁ => Finset.sum_le_sum fun b₂ hb₂ =>
            hwalk b₁ (hB₁ hb₁) b₂ (hB₂ hb₂)
    calc _ ≤ _ := this
      _ = (W.card : Real) := by rw [show W.card = _ from h]; push_cast; rfl
  -- Step 2: Cauchy–Schwarz over difference sequences
  let D4 := (X - X) ×ˢ (X - X) ×ˢ (X - X) ×ˢ (X - X)
  have hmemD : ∀ w ∈ W, walkDiffs w ∈ D4 := by
    intro w hw
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hw
    simp only [Finset.mem_product] at hmem
    obtain ⟨hb₁, ⟨hz₁, hz₂, hz₃⟩, hb₂⟩ := hmem
    have hb₁X := hBX (hB₁ hb₁)
    have hb₂X := hBX (hB₂ hb₂)
    simp only [walkDiffs, D4, Finset.mem_product]
    exact ⟨Finset.sub_mem_sub hb₁X hz₁, Finset.sub_mem_sub hz₁ hz₂, Finset.sub_mem_sub hz₂ hz₃,
      Finset.sub_mem_sub hz₃ hb₂X⟩
  let C := (W ×ˢ W).filter fun p => walkDiffs p.1 = walkDiffs p.2
  have hCS : (W.card : Real) ^ 2 ≤ D4.card * C.card := by
    have := collisions_ge W walkDiffs D4 hmemD
    convert this using 4
    ext p; simp only [C, Finset.mem_filter]
  have hD4 : (D4.card : Real) ≤ (K * X.card) ^ 4 := by
    have : D4.card = (X - X).card ^ 4 := by
      simp only [D4, Finset.card_product]; ring
    rw [this]; push_cast
    exact pow_le_pow_left₀ (by positivity) hdoub 4
  have hCge : κ * (X.card : Real) ^ 6 ≤ C.card := by
    have hW2 : (ε₁ * ε₂ * η) ^ 2 * (X.card : Real) ^ 10 ≤ (W.card : Real) ^ 2 := by
      have h1 : ε₁ * ε₂ * η * (X.card : Real) ^ 5 ≤ W.card := by
        calc ε₁ * ε₂ * η * (X.card : Real) ^ 5
            = (ε₁ * X.card) * (ε₂ * X.card) * (η * (X.card : Real) ^ 3) := by ring
          _ ≤ (B₁.card : Real) * B₂.card * (η * (X.card : Real) ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul hB₁c hB₂c (by positivity) (by positivity)
          _ ≤ W.card := hWge
      have h0 : 0 ≤ ε₁ * ε₂ * η * (X.card : Real) ^ 5 := by positivity
      calc (ε₁ * ε₂ * η) ^ 2 * (X.card : Real) ^ 10 = (ε₁ * ε₂ * η * (X.card : Real) ^ 5) ^ 2 := by
            ring
        _ ≤ (W.card : Real) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have hKX : (0 : Real) < (K * X.card) ^ 4 := by positivity
    have hC0 : (0 : Real) ≤ C.card := by positivity
    have h3 : (ε₁ * ε₂ * η) ^ 2 * (X.card : Real) ^ 10 ≤ (K * X.card) ^ 4 * C.card :=
      hW2.trans (hCS.trans (mul_le_mul_of_nonneg_right hD4 hC0))
    rw [hκdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (K * (X.card : Real)) ^ 4 = K ^ 4 * (X.card : Real) ^ 4 := by ring
    rw [this] at h3
    have hX4 : (0 : Real) < (X.card : Real) ^ 4 := by positivity
    nlinarith
  -- Step 3: the geometry of a collision
  have hgeom : ∀ p ∈ C,
      p.2.2.1.1 = p.1.2.1.1 - (p.1.1 - p.2.1) ∧
      p.2.2.1.2.1 = p.1.2.1.2.1 - (p.1.1 - p.2.1) ∧
      p.2.2.1.2.2 = p.1.2.1.2.2 - (p.1.1 - p.2.1) ∧
      p.2.2.2 = p.1.2.2 - (p.1.1 - p.2.1) := by
    rintro ⟨⟨b₁, ⟨z₁, z₂, z₃⟩, b₂⟩, ⟨b₁', ⟨z₁', z₂', z₃'⟩, b₂'⟩⟩ hp
    have hd := (Finset.mem_filter.mp hp).2
    simp only [walkDiffs, Prod.mk.injEq] at hd
    obtain ⟨h1, h2, h3, h4⟩ := hd
    simp only
    have e1 : z₁' = z₁ - (b₁ - b₁') := by
      calc z₁' = b₁' - (b₁' - z₁') := by abel
        _ = b₁' - (b₁ - z₁) := by rw [h1]
        _ = z₁ - (b₁ - b₁') := by abel
    have e2 : z₂' = z₂ - (b₁ - b₁') := by
      calc z₂' = z₁' - (z₁' - z₂') := by abel
        _ = z₁' - (z₁ - z₂) := by rw [h2]
        _ = z₂ - (b₁ - b₁') := by rw [e1]; abel
    have e3 : z₃' = z₃ - (b₁ - b₁') := by
      calc z₃' = z₂' - (z₂' - z₃') := by abel
        _ = z₂' - (z₂ - z₃) := by rw [h3]
        _ = z₃ - (b₁ - b₁') := by rw [e2]; abel
    have e4 : b₂' = b₂ - (b₁ - b₁') := by
      calc b₂' = z₃' - (z₃' - b₂') := by abel
        _ = z₃' - (z₃ - b₂) := by rw [h4]
        _ = b₂ - (b₁ - b₁') := by rw [e3]; abel
    exact ⟨e1, e2, e3, e4⟩
  let quadOf : (G × (G × G × G) × G) × (G × (G × G × G) × G) → G × G × G × G :=
    fun p => (p.1.1, p.2.1, p.1.2.2, p.2.2.2)
  let Quads := (B₁ ×ˢ B₁ ×ˢ B₂ ×ˢ B₂).filter fun q => q.1 - q.2.1 = q.2.2.1 - q.2.2.2
  let chains : G × G × G × G → Nat := fun q =>
    chainCount (R (q.1 - q.2.1) 1) X 3 q.1 q.2.2.1
  have hquad : ∀ p ∈ C, quadOf p ∈ Quads := by
    intro p hp
    obtain ⟨-, -, -, e4⟩ := hgeom p hp
    have hW := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have m1 := Finset.mem_product.mp (Finset.mem_filter.mp hW.1).1
    have m2 := Finset.mem_product.mp (Finset.mem_filter.mp hW.2).1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [quadOf, Finset.mem_product]
      exact ⟨m1.1, m2.1, (Finset.mem_product.mp m1.2).2, (Finset.mem_product.mp m2.2).2⟩
    · simp only [quadOf]; rw [e4]; abel
  -- Step 4: each quadruple's fiber injects into its chains
  have hfiber : ∀ q ∈ Quads, ((C.filter fun p => quadOf p = q).card : Real) ≤ chains q := by
    intro q _
    have hinj := Finset.card_le_card_of_injOn
      (fun p : (G × (G × G × G) × G) × (G × (G × G × G) × G) =>
        (p.1.2.1.2.2, p.1.2.1.2.1, p.1.2.1.1))
      (s := C.filter fun p => quadOf p = q)
      (t := (X ×ˢ X ×ˢ X).filter fun t =>
        R (q.1 - q.2.1) 1 q.1 t.2.2 ∧ R (q.1 - q.2.1) 1 t.2.2 t.2.1 ∧
          R (q.1 - q.2.1) 1 t.2.1 t.1 ∧ R (q.1 - q.2.1) 1 t.1 q.2.2.1)
      (fun p hp => by
        obtain ⟨hpC, hq⟩ := Finset.mem_filter.mp hp
        obtain ⟨e1, e2, e3, e4⟩ := hgeom p hpC
        have hW := Finset.mem_product.mp (Finset.mem_filter.mp hpC).1
        obtain ⟨m1, k1, k2, k3, k4⟩ := Finset.mem_filter.mp hW.1
        obtain ⟨-, k1', k2', k3', k4'⟩ := Finset.mem_filter.mp hW.2
        have hz := Finset.mem_product.mp (Finset.mem_product.mp m1).2
        have hz' := Finset.mem_product.mp hz.1
        have hz'' := Finset.mem_product.mp hz'.2
        subst hq
        simp only [quadOf]
        rw [e1] at k1' k2'
        rw [e2] at k2' k3'
        rw [e3] at k3' k4'
        rw [e4] at k4'
        have hb : p.2.1 = p.1.1 - (p.1.1 - p.2.1) := by abel
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz''.2,
          Finset.mem_product.mpr ⟨hz''.1, hz'.1⟩⟩, ?_, ?_, ?_, ?_⟩
        · exact shiftRel_one_of_edges hPA Q h20 hS3 k1 (by rw [← hb]; exact k1')
        · exact shiftRel_one_of_edges hPA Q h20 hS3 k2 k2'
        · exact shiftRel_one_of_edges hPA Q h20 hS3 k3 k3'
        · exact shiftRel_one_of_edges hPA Q h20 hS3 k4 k4')
      (fun p hp p' hp' h => by
        obtain ⟨hpC, hq⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpC', hq'⟩ := Finset.mem_filter.mp hp'
        obtain ⟨e1, e2, e3, e4⟩ := hgeom p hpC
        obtain ⟨f1, f2, f3, f4⟩ := hgeom p' hpC'
        rw [← hq'] at hq
        obtain ⟨⟨b₁, ⟨z₁, z₂, z₃⟩, b₂⟩, ⟨b₁', ⟨z₁', z₂', z₃'⟩, b₂'⟩⟩ := p
        obtain ⟨⟨c₁, ⟨y₁, y₂, y₃⟩, c₂⟩, ⟨c₁', ⟨y₁', y₂', y₃'⟩, c₂'⟩⟩ := p'
        simp only [quadOf, Prod.mk.injEq] at hq h
        simp only at e1 e2 e3 e4 f1 f2 f3 f4
        obtain ⟨a1, a2, a3, a4⟩ := hq
        obtain ⟨t3, t2, t1⟩ := h
        subst a1 a2 a3 a4 t1 t2 t3
        rw [e1, e2, e3, f1, f2, f3])
    show _ ≤ ((chainCount (R (q.1 - q.2.1) 1) X 3 q.1 q.2.2.1 : Nat) : Real)
    rw [chainCount_three_eq_card]
    exact_mod_cast hinj
  -- Step 5: averaging over quadruples
  have hchains_le : ∀ q, (chains q : Real) ≤ (X.card : Real) ^ 3 := fun q => by
    exact_mod_cast chainCount_le _ X 3 _ _
  have hQuads_le : (Quads.card : Real) ≤ (X.card : Real) ^ 3 := by
    have := Finset.card_le_card_of_injOn (fun q : G × G × G × G => (q.1, q.2.1, q.2.2.1))
      (s := Quads) (t := X ×ˢ X ×ˢ X)
      (fun q hq => by
        have hm := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
        have hm' := Finset.mem_product.mp hm.2
        have hm'' := Finset.mem_product.mp hm'.2
        exact Finset.mem_product.mpr ⟨hBX (hB₁ hm.1), Finset.mem_product.mpr
          ⟨hBX (hB₁ hm'.1), hBX (hB₂ hm''.1)⟩⟩)
      (fun q hq q' hq' h => by
        have ha := (Finset.mem_filter.mp hq).2
        have ha' := (Finset.mem_filter.mp hq').2
        obtain ⟨q1, q2, q3, q4⟩ := q
        obtain ⟨r1, r2, r3, r4⟩ := q'
        simp only [Prod.mk.injEq] at h ha ha'
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 : q4 = q3 - (q1 - q2) := by rw [ha]; abel
        have h2 : r4 = q3 - (q1 - q2) := by rw [ha']; abel
        rw [h1, h2])
    have h3 : (X ×ˢ X ×ˢ X).card = X.card ^ 3 := by simp only [Finset.card_product]; ring
    rw [h3] at this
    exact_mod_cast this
  have hsumC : (C.card : Real) ≤ ∑ q ∈ Quads, (chains q : Real) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := quadOf) (t := Quads) hquad
    calc (C.card : Real) = ∑ q ∈ Quads, ((C.filter fun p => quadOf p = q).card : Real) := by
          exact_mod_cast h
      _ ≤ _ := Finset.sum_le_sum fun q hq => hfiber q hq
  let Good := Quads.filter fun q => κ / 2 * (X.card : Real) ^ 3 ≤ chains q
  have hGood : κ / 2 * (X.card : Real) ^ 3 ≤ Good.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Quads
      (fun q => κ / 2 * (X.card : Real) ^ 3 ≤ chains q) (fun q => (chains q : Real))
    have hin : ∑ q ∈ Good, (chains q : Real) ≤ Good.card * (X.card : Real) ^ 3 := by
      calc _ ≤ ∑ _q ∈ Good, (X.card : Real) ^ 3 := Finset.sum_le_sum fun q _ => hchains_le q
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hout : ∑ q ∈ Quads.filter (fun q => ¬ κ / 2 * (X.card : Real) ^ 3 ≤ chains q),
        (chains q : Real) ≤ (X.card : Real) ^ 3 * (κ / 2 * (X.card : Real) ^ 3) := by
      calc _ ≤ ∑ _q ∈ Quads.filter (fun q => ¬ κ / 2 * (X.card : Real) ^ 3 ≤ chains q),
            κ / 2 * (X.card : Real) ^ 3 :=
            Finset.sum_le_sum fun q hq => (not_le.mp (Finset.mem_filter.mp hq).2).le
        _ = ((Quads.filter fun q => ¬ κ / 2 * (X.card : Real) ^ 3 ≤ chains q).card : Real) *
              (κ / 2 * (X.card : Real) ^ 3) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (X.card : Real) ^ 3 * (κ / 2 * (X.card : Real) ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact (by exact_mod_cast Finset.card_filter_le _ _ :
              ((Quads.filter fun q => ¬ κ / 2 * (X.card : Real) ^ 3 ≤ chains q).card : Real) ≤
                Quads.card).trans hQuads_le
    have hX3 : (0 : Real) < (X.card : Real) ^ 3 := by positivity
    have hX6 : (X.card : Real) ^ 6 = (X.card : Real) ^ 3 * (X.card : Real) ^ 3 := by ring
    have : κ / 2 * (X.card : Real) ^ 3 * (X.card : Real) ^ 3 ≤ Good.card * (X.card : Real) ^ 3 := by
      rw [hX6] at hCge
      nlinarith [hCge, hsumC, hsplit, hin, hout]
    exact le_of_mul_le_mul_right this hX3
  -- Step 6: the ladder on each good quadruple
  rcases hκ0.lt_or_eq with hκpos | hκzero
  · have hsub : Good ⊆ ((B₁ ×ˢ B₁ ×ˢ B₂ ×ˢ B₂).filter fun q =>
        q.1 - q.2.1 = q.2.2.1 - q.2.2.2 ∧ Q 16 q.1 q.2.1 q.2.2.1 q.2.2.2) := ?_
    · exact hGood.trans (by exact_mod_cast Finset.card_le_card hsub)
    intro q hq
    obtain ⟨hqQ, hqc⟩ := Finset.mem_filter.mp hq
    obtain ⟨hmem, hadd⟩ := Finset.mem_filter.mp hqQ
    have hrel := rel_of_chainCount (R (q.1 - q.2.1)) X (hWTR (q.1 - q.2.1)) 3 q.1 q.2.2.1
      (η := κ / 2) (by positivity) (by norm_num; linarith) hqc
    obtain ⟨-, -, -, -, hQ⟩ := hrel
    have h1 : q.1 - (q.1 - q.2.1) = q.2.1 := by abel
    have h2 : q.2.2.1 - (q.1 - q.2.1) = q.2.2.2 := by rw [hadd]; abel
    rw [h1, h2] at hQ
    exact Finset.mem_filter.mpr ⟨hmem, hadd, by simpa using hQ⟩
  · rw [← hκzero]; simp

end LeanProofs.GowersSzemeredi
