import GowersSzemeredi.Proofs16AbstractBSGPruning

/-! The core of Milićević's abstract Balog–Szemerédi–Gowers theorem, assembled
(arXiv:2601.01682, Theorem 4.1, printed pp. 47–51, up to the bridging
statement).

* `walkSet_card_eq_fourWalks`: on the subtype of `X`, four-walks of the graph
  `P` are exactly `walkSet P X`.
* `exists_dense_rich_walk_set`: a symmetric graph `P ⊆ A × A` with
  `δ|X|²` edges has a set `B ⊆ A` of `3δ|X|/8` vertices, any two of which
  are joined by `δ^5|X|^3/16384` walks `walkSet P X`.
* `abstract_bsg_core`: this combines the popular differences, Claim 4.3, the
  antipodal-free union graph with property (20), the four-walk set,
  Claim 4.4 and the pruning step. It yields `B′ ⊆ A` of size at least
  `(3δ₂/16)|X|` in which every element lies in at least `θ|X|²` additive
  `Q 16`-quadruples with the rest in `B ⊆ A`. Here `δ = c/(2K)`,
  `δ₂ = 3cδ/64`, `η = δ₂⁵/16384`, `ε = 3δ₂/16`, `κ = (ε²η)²/K⁴`, and
  `θ < κ/2` is free. All are polynomial in `c/K`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- Four-walks of `P` on the subtype of `X` are `walkSet P X`. -/
theorem walkSet_card_eq_fourWalks {G : Type*} [AddCommGroup G] (X : Finset G)
    (P : Finset (G × G)) (u v : {x : G // x ∈ X}) :
    (graphFourWalks (fun a b : {x : G // x ∈ X} => ((a : G), (b : G)) ∈ P) u v).card =
      (walkSet P X u v).card := by
  refine Finset.card_bij (fun t _ => ((t.1 : G), (t.2.1 : G), (t.2.2 : G))) ?_ ?_ ?_
  · intro t ht
    simp only [graphFourWalks, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [walkSet, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨t.1.2, t.2.1.2, t.2.2.2⟩, ht⟩
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Prod.ext (Subtype.ext h.2.1) (Subtype.ext h.2.2))
  · intro s hs
    simp only [walkSet, Finset.mem_filter, Finset.mem_product] at hs
    obtain ⟨⟨m1, m2, m3⟩, h⟩ := hs
    refine ⟨(⟨s.1, m1⟩, ⟨s.2.1, m2⟩, ⟨s.2.2, m3⟩), ?_, rfl⟩
    simp only [graphFourWalks, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h

/-- **A robustly connected set for a dense symmetric graph inside `X`.** -/
theorem exists_dense_rich_walk_set {G : Type*} [AddCommGroup G] {A X : Finset G}
    (hAX : A ⊆ X) (hX : X.Nonempty) {P : Finset (G × G)} (hPA : P ⊆ A ×ˢ A)
    (hsym : ∀ p ∈ P, p.swap ∈ P) {δ : Real} (hδ : 0 < δ)
    (hP : δ * (X.card : Real) ^ 2 ≤ P.card) :
    ∃ B ⊆ A, 3 * δ * X.card / 8 ≤ (B.card : Real) ∧
      ∀ u ∈ B, ∀ v ∈ B, δ ^ 5 * (X.card : Real) ^ 3 / 16384 ≤ (walkSet P X u v).card := by
  let V := {x : G // x ∈ X}
  haveI : Nonempty V := ⟨⟨hX.choose, hX.choose_spec⟩⟩
  have hcardV : Fintype.card V = X.card := by simp only [V, Fintype.card_coe]
  let r : V → V → Prop := fun a b => ((a : G), (b : G)) ∈ P
  have hr : ∀ a b, r a b → r b a := fun a b h => hsym _ h
  have hedges : δ * (Fintype.card V : Real) ^ 2 ≤ ∑ x : V, ((graphNeighbours r x).card : Real) := by
    have hsum : (∑ x : V, (graphNeighbours r x).card) =
        (Finset.univ.filter fun p : V × V => r p.1 p.2).card := by
      simp only [graphNeighbours, Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by congr
    have hbij : (Finset.univ.filter fun p : V × V => r p.1 p.2).card = P.card := by
      refine Finset.card_bij (fun p _ => ((p.1 : G), (p.2 : G))) ?_ ?_ ?_
      · intro p hp; exact (Finset.mem_filter.mp hp).2
      · intro p _ q _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
      · intro q hq
        have hm := Finset.mem_product.mp (hPA hq)
        exact ⟨(⟨q.1, hAX hm.1⟩, ⟨q.2, hAX hm.2⟩),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
    rw [hcardV]
    calc δ * (X.card : Real) ^ 2 ≤ P.card := hP
      _ = ∑ x : V, ((graphNeighbours r x).card : Real) := by
          rw [← hbij, ← hsum]; push_cast; rfl
  obtain ⟨T, hT, hwalk⟩ := exists_dense_four_walk_set r hr hδ hedges
  have hXpos : (0 : Real) < X.card := by exact_mod_cast hX.card_pos
  have hwalkG : ∀ u ∈ T, ∀ v ∈ T,
      δ ^ 5 * (X.card : Real) ^ 3 / 16384 ≤ (walkSet P X u v).card := by
    intro u hu v hv
    rw [← walkSet_card_eq_fourWalks X P u v, ← hcardV]
    exact hwalk u hu v hv
  -- every vertex of `T` is in `A`: it has a walk to itself
  have hTA : ∀ u ∈ T, (u : G) ∈ A := by
    intro u hu
    have hpos : (0 : Real) < (walkSet P X u u).card :=
      (by positivity : (0 : Real) < δ ^ 5 * (X.card : Real) ^ 3 / 16384).trans_le (hwalkG u hu u hu)
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
    exact (Finset.mem_product.mp (hPA (Finset.mem_filter.mp ht).2.1)).1
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
    exact hTA x hx
  · rw [Finset.card_map, ← hcardV]; exact hT
  · intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
    exact hwalkG x hx y hy

/-- The popular-difference density `c/(2K)`. -/
def absBsgDelta (c K : Real) : Real := c / (2 * K)
/-- The union-graph edge density `3cδ/64`. -/
def absBsgDelta2 (c K : Real) : Real := 3 * c * absBsgDelta c K / 64
/-- The four-walk density `δ₂⁵/16384`. -/
def absBsgEta (c K : Real) : Real := absBsgDelta2 c K ^ 5 / 16384
/-- The pruning density `3δ₂/16`. -/
def absBsgEps (c K : Real) : Real := 3 * absBsgDelta2 c K / 16
/-- Claim 4.4's quadruple density `(ε²η)²/K⁴`. -/
def absBsgKappa (c K : Real) : Real := (absBsgEps c K * absBsgEps c K * absBsgEta c K) ^ 2 / K ^ 4

/-- **The core of the abstract Balog–Szemerédi–Gowers theorem.** -/
theorem abstract_bsg_core {G : Type*} [AddCommGroup G] [Fintype G]
    (h2 : ∀ d : G, d + d = 0 → d = 0) {A X : Finset G} (hAX : A ⊆ X) (hX : X.Nonempty)
    (Q : Nat → G → G → G → G → Prop)
    (hS1 : ∀ a₁ a₂ a₃ a₄, Q 1 a₁ a₂ a₃ a₄ → Q 1 a₃ a₄ a₁ a₂)
    (hS2 : ∀ a₁ a₂ a₃ a₄, Q 4 a₁ a₂ a₃ a₄ → Q 4 a₂ a₁ a₄ a₃)
    (hS3 : ∀ i a₁ a₂ a₃ a₄, Q i a₁ a₂ a₃ a₄ → Q i a₁ a₃ a₂ a₄)
    {c c' K θ : Real} (hc0 : 0 < c) (hc'0 : 0 < c')
    (hWT : ∀ i j, i + j ≤ 16 → ∀ a₁ a₂ a₃ a₄, c' * X.card ≤ (((A ×ˢ A).filter fun p =>
        Q i a₁ a₂ p.1 p.2 ∧ Q j p.1 p.2 a₃ a₄).card : Real) → Q (i + j) a₁ a₂ a₃ a₄)
    (hK : 0 < K) (hdoub : ((X - X).card : Real) ≤ K * X.card)
    (hgood : c * (X.card : Real) ^ 3 ≤ ∑ d ∈ X - X, (diffGoodCount A (Q 1) d : Real))
    (hcX : 4 ≤ c * X.card)
    (hc'1 : 8 * c' ≤ absBsgDelta c K ^ 5 / 16384) (hc'2 : 16 * c' ≤ absBsgKappa c K)
    (hθ : θ < absBsgKappa c K / 2) :
    ∃ B B' : Finset G, B' ⊆ B ∧ B ⊆ A ∧ absBsgEps c K * X.card ≤ (B'.card : Real) ∧
      ∀ a ∈ B', θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a := by
  have hXpos : (0 : Real) < X.card := by exact_mod_cast hX.card_pos
  have hδ : 0 < absBsgDelta c K := by unfold absBsgDelta; positivity
  have hδ₂ : 0 < absBsgDelta2 c K := by unfold absBsgDelta2; positivity
  have hη : 0 < absBsgEta c K := by unfold absBsgEta; positivity
  have hε : 0 < absBsgEps c K := by unfold absBsgEps; positivity
  -- popular differences
  let D := (X - X).filter fun d =>
    c / (2 * K) * (X.card : Real) ^ 2 ≤ diffGoodCount A (Q 1) d
  have hD : c / 2 * X.card ≤ (D.card : Real) :=
    exists_popular_differences hAX (Q 1) hK hdoub hgood
  -- Claim 4.3 for each popular difference
  have hTex : ∀ d : G, ∃ T : Finset G, d ∈ D → T ⊆ X ∧
      3 * absBsgDelta c K * X.card / 8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ∈ A ∧ u + d ∈ A ∧ Q 4 (u + d) u (v + d) v := by
    intro d
    by_cases hd : d ∈ D
    · have hcount : absBsgDelta c K * (X.card : Real) ^ 2 ≤ diffGoodCount A (Q 1) d :=
        (Finset.mem_filter.mp hd).2
      obtain ⟨T, hT⟩ := difference_ladder_rel_four hX hAX Q hS1 hc'0 hδ
        (fun i hi a₁ a₂ a₃ a₄ h => hWT i 1 (by omega) a₁ a₂ a₃ a₄ h) hc'1 hcount
      exact ⟨T, fun _ => hT⟩
    · exact ⟨∅, fun h => absurd h hd⟩
  choose T hT using hTex
  -- antipodal-free representatives and the union graph
  obtain ⟨D', hD'D, -, hanti, hD'card⟩ := exists_antipodal_free_subset h2 D
  let P := diffUnion D' T
  have hPA : P ⊆ A ×ˢ A := diffUnion_subset fun d hd u hu =>
    ⟨((hT d (hD'D hd)).2.2 u hu u hu).1, ((hT d (hD'D hd)).2.2 u hu u hu).2.1⟩
  have hsym : ∀ p ∈ P, p.swap ∈ P := fun p hp => diffUnion_swap hp
  have h20 : ∀ p ∈ P, ∀ q ∈ P, p.1 - p.2 = q.1 - q.2 → Q 4 p.1 p.2 q.1 q.2 :=
    fun p hp q hq hpq => diffUnion_same_difference (Q 4) hS2 hanti
      (fun d hd u hu v hv => ((hT d (hD'D hd)).2.2 u hu v hv).2.2) hp hq hpq
  have hPcard : absBsgDelta2 c K * (X.card : Real) ^ 2 ≤ P.card := by
    have hsum : (D'.card : Real) * (3 * absBsgDelta c K * X.card / 8) ≤
        ∑ d ∈ D', ((T d).card : Real) := by
      calc (D'.card : Real) * (3 * absBsgDelta c K * X.card / 8)
          = ∑ _d ∈ D', 3 * absBsgDelta c K * X.card / 8 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun d hd => (hT d (hD'D hd)).2.1
    have hunion : (∑ d ∈ D', ((T d).card : Real)) ≤ P.card := by
      exact_mod_cast diffUnion_card_ge D' T
    have hD' : c / 8 * X.card ≤ (D'.card : Real) := by
      have : (D.card : Real) ≤ 2 * D'.card + 1 := by exact_mod_cast hD'card
      linarith
    have hpos : 0 ≤ 3 * absBsgDelta c K * X.card / 8 := by positivity
    calc absBsgDelta2 c K * (X.card : Real) ^ 2
        = (c / 8 * X.card) * (3 * absBsgDelta c K * X.card / 8) := by unfold absBsgDelta2; ring
      _ ≤ (D'.card : Real) * (3 * absBsgDelta c K * X.card / 8) :=
          mul_le_mul_of_nonneg_right hD' hpos
      _ ≤ P.card := hsum.trans hunion
  -- the robustly connected set and pruning
  obtain ⟨B, hBA, hBcard, hwalk⟩ := exists_dense_rich_walk_set hAX hX hPA hsym hδ₂ hPcard
  have hwalk' : ∀ u ∈ B, ∀ v ∈ B,
      absBsgEta c K * (X.card : Real) ^ 3 ≤ (walkSet P X u v).card := by
    intro u hu v hv
    have := hwalk u hu v hv
    unfold absBsgEta
    linarith
  have hpoor := rich_pruning hAX hBA hX hPA Q h20 hS3 hc'0 hWT hK hdoub hη.le hwalk' hε
    (by simpa only [absBsgKappa] using hc'2) (by simpa only [absBsgKappa] using hθ)
  refine ⟨B, B.filter fun a => θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a,
    Finset.filter_subset _ _, hBA, ?_, fun a ha => (Finset.mem_filter.mp ha).2⟩
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := B)
    (fun a => θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a)
  have hsplitR : ((B.filter fun a => θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a).card : Real) +
      ((B.filter fun a => ¬ θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a).card : Real) =
      B.card := by exact_mod_cast hsplit
  have hB : 3 * absBsgDelta2 c K * X.card / 8 ≤ (B.card : Real) := hBcard
  unfold absBsgEps
  unfold absBsgEps at hpoor
  linarith

end LeanProofs.GowersSzemeredi
