import GowersSzemeredi.Proofs16Lemma92Pair

/-! The new map of Claim 9.4 is a Freiman homomorphism (Milićević
arXiv:2601.01682, printed p. 66, "the claim follows from Lemma 9.2").

Suppose `Θ(a) = ψ₀(x+a) − ψ₁(x)` on a set `P` of `cN²` pairs `(x, a)`.
Then the triples `(x+a, −x, ⋆)` separate `f = Θ` and `g = ψ₀`:
`Θ((x+a) + (−x)) − ψ₀(x+a) = −ψ₁(x)` depends only on `−x`.
1. Restrict to popular `a`, each carrying at least `(c/2)N` pairs. This
   keeps `(c/2)N²` pairs and at least `(c/2)N` values.
2. `milicevic_lemma_9_2_pair` gives a set `B` of values, of density
   `κ = 2^(−1882)·((c/2)^4)^1164` among them, on which `Θ` is a Freiman
   8-homomorphism.
3. Every value of `B` is popular, so `P` has at least
   `κ·(c/2)²·N²` pairs over `B`.

`freiman_common_value` states this. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **The common value is a Freiman homomorphism on a dense set.** -/
theorem freiman_common_value {N : Nat} [NeZero N] [Fact N.Prime]
    (Θ ψ₀ ψ₁ : ZMod N → ZMod N) (P : Finset (ZMod N × ZMod N))
    (hP : ∀ p ∈ P, Θ p.2 = ψ₀ (p.1 + p.2) - ψ₁ p.1)
    {c : Real} (hc : 0 < c) (hPc : c * (N : Real) ^ 2 ≤ P.card) :
    ∃ B : Finset (ZMod N), FreimanHom 8 B Θ ∧
      (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2 * (N : Real) ^ 2 ≤
        (P.filter fun p => p.2 ∈ B).card := by
  have hN : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- fibers over a value have at most `N` pairs
  let Pa : ZMod N → Finset (ZMod N × ZMod N) := fun a => P.filter fun p => p.2 = a
  have hPa_le : ∀ (S : Finset (ZMod N × ZMod N)) a,
      ((S.filter fun p => p.2 = a).card : Real) ≤ N := by
    intro S a
    have : (S.filter fun p => p.2 = a).card ≤ (Finset.univ : Finset (ZMod N)).card := by
      refine Finset.card_le_card_of_injOn (fun p => p.1) (fun _ _ => by simp) ?_
      intro p hp p' hp' h
      exact Prod.ext h ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm)
    rw [Finset.card_univ, ZMod.card] at this
    exact_mod_cast this
  -- popular values
  let pop : ZMod N → Prop := fun a => c / 2 * N ≤ ((Pa a).card : Real)
  let P' := P.filter fun p => pop p.2
  have hP'fiber : ∀ a, pop a → (P'.filter fun p => p.2 = a) = Pa a := by
    intro a ha
    ext p
    simp only [P', Pa, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ ha⟩, h3⟩
  have hP'card : c / 2 * (N : Real) ^ 2 ≤ P'.card := by
    let Pu := P.filter fun p => ¬ pop p.2
    have hsplit : (P'.card : Real) + Pu.card = P.card := by
      exact_mod_cast Finset.filter_card_add_filter_neg_card_eq_card _
    have hPu : (Pu.card : Real) ≤ c / 2 * (N : Real) ^ 2 := by
      have h := Finset.card_eq_sum_card_fiberwise (s := Pu) (t := Finset.univ)
        (f := fun p => p.2) (fun _ _ => Finset.mem_univ _)
      have hfib : ∀ a, ((Pu.filter fun p => p.2 = a).card : Real) ≤ c / 2 * N := by
        intro a
        by_cases ha : pop a
        · have : (Pu.filter fun p => p.2 = a) = ∅ := by
            refine Finset.filter_eq_empty_iff.mpr fun p hp hpa => ?_
            exact (Finset.mem_filter.mp hp).2 (hpa ▸ ha)
          rw [this, Finset.card_empty, Nat.cast_zero]
          positivity
        · have hsub : (Pu.filter fun p => p.2 = a) ⊆ Pa a := by
            intro p hp
            simp only [Pu, Pa, Finset.mem_filter] at hp ⊢
            exact ⟨hp.1.1, hp.2⟩
          have := Finset.card_le_card hsub
          have hlt : ((Pa a).card : Real) < c / 2 * N := lt_of_not_ge ha
          calc ((Pu.filter fun p => p.2 = a).card : Real) ≤ (Pa a).card := by exact_mod_cast this
            _ ≤ c / 2 * N := hlt.le
      calc (Pu.card : Real) = ∑ a : ZMod N, ((Pu.filter fun p => p.2 = a).card : Real) := by
            rw [h]; push_cast; rfl
        _ ≤ ∑ _a : ZMod N, c / 2 * (N : Real) := Finset.sum_le_sum fun a _ => hfib a
        _ = c / 2 * (N : Real) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
    linarith
  -- the separated family
  let Q : Finset (ZMod N × ZMod N × Unit) := P'.image fun p => (p.1 + p.2, -p.1, ())
  have hQcard : Q.card = P'.card := by
    apply Finset.card_image_of_injOn
    intro p _ p' _ h
    simp only [Prod.mk.injEq, neg_inj] at h
    obtain ⟨h1, h2, -⟩ := h
    refine Prod.ext h2 ?_
    have := h1
    rw [h2] at this
    exact add_left_cancel this
  have hval : ∀ q ∈ Q, ∃ p ∈ P', q.1 + q.2.1 = p.2 ∧ q.2.1 = -p.1 ∧ q.1 = p.1 + p.2 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨p, hp, (show p.1 + p.2 + -p.1 = p.2 by rw [add_comm p.1 p.2, add_neg_cancel_right]), rfl, rfl⟩
  have hsep : ∀ x x' a ω, (x, a, ω) ∈ Q → (x', a, ω) ∈ Q →
      Θ (x + a) - ψ₀ x = Θ (x' + a) - ψ₀ x' := by
    have key : ∀ x a ω, (x, a, ω) ∈ Q → Θ (x + a) - ψ₀ x = -ψ₁ (-a) := by
      intro x a ω h
      obtain ⟨p, hp, h1, h2, h3⟩ := hval _ h
      simp only at h1 h2 h3
      rw [h1, hP p (Finset.mem_filter.mp hp).1, h2, neg_neg, ← h3]
      abel
    intro x x' a ω h h'
    rw [key x a ω h, key x' a ω h']
  have hQc : c / 2 * (N : Real) ^ 2 * Fintype.card Unit ≤ Q.card := by
    rw [Fintype.card_unit, Nat.cast_one, mul_one, hQcard]
    exact hP'card
  obtain ⟨B, hBsub, -, hBcard, hF, -⟩ :=
    milicevic_lemma_9_2_pair Θ ψ₀ Q hsep (by positivity) hQc
  refine ⟨B, hF, ?_⟩
  -- every value of `B` is popular
  have hBpop : ∀ a ∈ B, pop a := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hBsub ha)
    obtain ⟨p, hp, h1, -, -⟩ := hval q hq
    rw [h1]
    exact (Finset.mem_filter.mp hp).2
  -- the value set is large
  let V := Q.image fun q => q.1 + q.2.1
  have hV : c / 2 * (N : Real) ≤ V.card := by
    have hsub : P'.image (fun p => p.2) ⊆ V := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨(p.1 + p.2, -p.1, ()), Finset.mem_image_of_mem _ hp,
        (show p.1 + p.2 + -p.1 = p.2 by rw [add_comm p.1 p.2, add_neg_cancel_right])⟩
    have h := Finset.card_eq_sum_card_fiberwise (s := P') (t := P'.image fun p => p.2)
      (f := fun p => p.2) (fun p hp => Finset.mem_image_of_mem _ hp)
    have hle : (P'.card : Real) ≤ ((P'.image fun p => p.2).card : Real) * N := by
      calc (P'.card : Real) = ∑ a ∈ P'.image (fun p => p.2),
            ((P'.filter fun p => p.2 = a).card : Real) := by rw [h]; push_cast; rfl
        _ ≤ ∑ _a ∈ P'.image (fun p => p.2), (N : Real) :=
            Finset.sum_le_sum fun a _ => hPa_le P' a
        _ = ((P'.image fun p => p.2).card : Real) * N := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := Finset.card_le_card hsub
    have h2 : c / 2 * (N : Real) * N ≤ ((P'.image fun p => p.2).card : Real) * N := by
      nlinarith
    have h3 : c / 2 * (N : Real) ≤ ((P'.image fun p => p.2).card : Real) :=
      le_of_mul_le_mul_right h2 hN
    calc c / 2 * (N : Real) ≤ ((P'.image fun p => p.2).card : Real) := h3
      _ ≤ V.card := by exact_mod_cast hcard
  -- count the pairs over `B`
  have hcount : (B.card : Real) * (c / 2 * N) ≤ (P.filter fun p => p.2 ∈ B).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := P.filter fun p => p.2 ∈ B) (t := B)
      (f := fun p => p.2) (fun p hp => (Finset.mem_filter.mp hp).2)
    have hfib : ∀ a ∈ B, c / 2 * (N : Real) ≤
        (((P.filter fun p => p.2 ∈ B).filter fun p => p.2 = a).card : Real) := by
      intro a ha
      have : ((P.filter fun p => p.2 ∈ B).filter fun p => p.2 = a) = Pa a := by
        ext p
        simp only [Pa, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ ha⟩, h3⟩
      rw [this]
      exact hBpop a ha
    calc (B.card : Real) * (c / 2 * N) = ∑ _a ∈ B, c / 2 * (N : Real) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ B, (((P.filter fun p => p.2 ∈ B).filter fun p => p.2 = a).card : Real) :=
          Finset.sum_le_sum hfib
      _ = (P.filter fun p => p.2 ∈ B).card := by rw [h]; push_cast; rfl
  have hκ : (0 : Real) ≤ (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 := by positivity
  calc (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2 * (N : Real) ^ 2
      = (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2 * N) * (c / 2 * N) := by
        ring
    _ ≤ (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * V.card * (c / 2 * N) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hV hκ
    _ ≤ (B.card : Real) * (c / 2 * N) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hBcard
    _ ≤ (P.filter fun p => p.2 ∈ B).card := hcount

end LeanProofs.GowersSzemeredi
