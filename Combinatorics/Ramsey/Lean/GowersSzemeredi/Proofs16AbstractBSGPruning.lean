import GowersSzemeredi.Proofs16AbstractBSGClaim44

/-! The pruning step of Milićević's abstract Balog–Szemerédi–Gowers theorem
(arXiv:2601.01682, Theorem 4.1, printed p. 51): `B` is "arithmetically
rich everywhere", so all but few of its elements lie in many `Q 16`
quadruples.

* `richCount B R a`: the triples `(b, c, d) ∈ B³` with `a − b = c − d` and
  `R a b c d`.
* `rich_pruning`: under the hypotheses of `claim_4_4`, suppose
  `θ < κ/2` with `κ = (ε²η)²/K⁴` and `16c′ ≤ κ`. Then fewer than `ε|X|`
  elements `a ∈ B` have `richCount B (Q 16) a < θ|X|²`. Otherwise Claim 4.4,
  applied to those poor elements, gives `(κ/2)|X|³` quadruples among them,
  more than their total `θ|X|³`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- Additive quadruples starting at `a`, with the rest in `B`, satisfying `R`. -/
def richCount {G : Type*} [AddCommGroup G] (B : Finset G) (R : G → G → G → G → Prop)
    (a : G) : Nat :=
  ((B ×ˢ B ×ˢ B).filter fun t => a - t.1 = t.2.1 - t.2.2 ∧ R a t.1 t.2.1 t.2.2).card

/-- **Pruning.** -/
theorem rich_pruning {G : Type*} [AddCommGroup G] {A X B : Finset G}
    (hAX : A ⊆ X) (hBA : B ⊆ A) (hX : X.Nonempty)
    {P : Finset (G × G)} (hPA : P ⊆ A ×ˢ A) (Q : Nat → G → G → G → G → Prop)
    (h20 : ∀ p ∈ P, ∀ q ∈ P, p.1 - p.2 = q.1 - q.2 → Q 4 p.1 p.2 q.1 q.2)
    (hS3 : ∀ i a₁ a₂ a₃ a₄, Q i a₁ a₂ a₃ a₄ → Q i a₁ a₃ a₂ a₄)
    {c' K η ε θ : Real} (hc'0 : 0 < c')
    (hWT : ∀ i j a₁ a₂ a₃ a₄, c' * X.card ≤ (((A ×ˢ A).filter fun p =>
        Q i a₁ a₂ p.1 p.2 ∧ Q j p.1 p.2 a₃ a₄).card : Real) → Q (i + j) a₁ a₂ a₃ a₄)
    (hK : 0 < K) (hdoub : ((X - X).card : Real) ≤ K * X.card)
    (hη : 0 ≤ η) (hwalk : ∀ u ∈ B, ∀ v ∈ B, η * (X.card : Real) ^ 3 ≤ (walkSet P X u v).card)
    (hε : 0 < ε) (hc' : 16 * c' ≤ (ε * ε * η) ^ 2 / K ^ 4)
    (hθ : θ < (ε * ε * η) ^ 2 / K ^ 4 / 2) :
    ((B.filter fun a => ¬ θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a).card : Real) <
      ε * X.card := by
  let Poor := B.filter fun a => ¬ θ * (X.card : Real) ^ 2 ≤ richCount B (Q 16) a
  have hXpos : (0 : Real) < X.card := by exact_mod_cast hX.card_pos
  rcases le_or_gt θ 0 with hθ0 | hθ0
  · have hempty : Poor = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a _ h
      exact h ((mul_nonpos_of_nonpos_of_nonneg hθ0 (by positivity)).trans (by positivity))
    show ((Poor.card : Nat) : Real) < ε * X.card
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_pos hε hXpos
  by_contra hcon'
  have hcon : ε * X.card ≤ (Poor.card : Real) := not_lt.mp hcon'
  have hPB : Poor ⊆ B := Finset.filter_subset _ _
  have hPoor_ne : Poor.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : Real) < Poor.card := (mul_pos hε hXpos).trans_le hcon
    exact_mod_cast this
  -- Claim 4.4 on the poor elements
  have hmany := claim_4_4 hAX hBA hPB hPB hX hPA Q h20 hS3 hc'0 hWT hK hdoub hη hwalk
    hε.le hε.le hcon hcon hc'
  -- but the poor elements carry few quadruples
  let T := (Poor ×ˢ Poor ×ˢ Poor ×ˢ Poor).filter fun q =>
    q.1 - q.2.1 = q.2.2.1 - q.2.2.2 ∧ Q 16 q.1 q.2.1 q.2.2.1 q.2.2.2
  have hT : (T.card : Real) < θ * (X.card : Real) ^ 3 := by
    have hfib : T.card = ∑ a ∈ Poor, (T.filter fun q => q.1 = a).card :=
      Finset.card_eq_sum_card_fiberwise (fun q hq =>
        (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1)
    have hle : ∀ a ∈ Poor, (T.filter fun q => q.1 = a).card ≤ richCount B (Q 16) a := by
      intro a _
      unfold richCount
      apply Finset.card_le_card_of_injOn (fun q : G × G × G × G => q.2)
      · intro q hq
        obtain ⟨hqT, rfl⟩ := Finset.mem_filter.mp hq
        obtain ⟨hmem, hadd, hQ⟩ := Finset.mem_filter.mp hqT
        have hm := Finset.mem_product.mp hmem
        have hm' := Finset.mem_product.mp hm.2
        have hm'' := Finset.mem_product.mp hm'.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hPB hm'.1,
          Finset.mem_product.mpr ⟨hPB hm''.1, hPB hm''.2⟩⟩, hadd, hQ⟩
      · intro q hq q' hq' h
        have e1 := (Finset.mem_filter.mp hq).2
        have e2 := (Finset.mem_filter.mp hq').2
        exact Prod.ext (e1.trans e2.symm) h
    have hlt : ∀ a ∈ Poor, ((T.filter fun q => q.1 = a).card : Real) < θ * (X.card : Real) ^ 2 := by
      intro a ha
      have hpoor := (Finset.mem_filter.mp ha).2
      exact (by exact_mod_cast hle a ha : ((T.filter fun q => q.1 = a).card : Real) ≤
        richCount B (Q 16) a).trans_lt (not_le.mp hpoor)
    have hPX : (Poor.card : Real) ≤ X.card := by
      exact_mod_cast Finset.card_le_card (hPB.trans (hBA.trans hAX))
    calc (T.card : Real) = ∑ a ∈ Poor, ((T.filter fun q => q.1 = a).card : Real) := by
          exact_mod_cast hfib
      _ < ∑ _a ∈ Poor, θ * (X.card : Real) ^ 2 := Finset.sum_lt_sum_of_nonempty hPoor_ne hlt
      _ = Poor.card * (θ * (X.card : Real) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ X.card * (θ * (X.card : Real) ^ 2) :=
          mul_le_mul_of_nonneg_right hPX (by positivity)
      _ = θ * (X.card : Real) ^ 3 := by ring
  have hX3 : (0 : Real) < (X.card : Real) ^ 3 := by positivity
  have : θ * (X.card : Real) ^ 3 < (ε * ε * η) ^ 2 / K ^ 4 / 2 * (X.card : Real) ^ 3 :=
    mul_lt_mul_of_pos_right hθ hX3
  linarith

end LeanProofs.GowersSzemeredi
