import GowersSzemeredi.Proofs16SeparatedFreiman

/-! The pairing step of Milićević's Lemma 9.2 (arXiv:2601.01682, printed
pp. 64–65): `φ₂ = ψ₁ + u` on a dense set.

Let `S` be a family of pairs `(x, a)` separating `f` and `g`: the value
`f(x + a) − g(x)` depends only on `a` within `S`. Let `ψ` respect additive
quadruples on `B` and agree with `f` there. For a fixed `a`, if `x` and
`x′` lie in the `a`-fiber with `x, x + a, x′, x′ + a ∈ B`, then
`ψ(x+a) − ψ(x) = ψ(x′+a) − ψ(x′)`. So `g − ψ` is constant on each fiber.
* `shift_agreement`: there are `u` and a set `Y ⊆ B` with
  `|S′| ≤ |G|·|Y|` and `g = ψ + u` on `Y`, where
  `S′ = {(x, a) ∈ S : x, x + a ∈ B}`. `Y` is the largest fiber.

Milićević reaches this through the rank of `ψ₁ − ψ₂` and a coset of its
kernel. Here the most popular fiber suffices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- One fiber: `g − ψ` is constant on it. -/
theorem shift_constant_on_fiber {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f g ψ : G → H) (B : Finset G) {x x₀ a : G}
    (hsep : f (x + a) - g x = f (x₀ + a) - g x₀)
    (hψ : ψ (x + a) + ψ x₀ = ψ (x₀ + a) + ψ x)
    (hf₁ : f (x + a) = ψ (x + a)) (hf₂ : f (x₀ + a) = ψ (x₀ + a)) :
    g x = ψ x + (g x₀ - ψ x₀) := by
  rw [hf₁, hf₂] at hsep
  calc g x = ψ (x + a) - (ψ (x + a) - g x) := by abel
    _ = ψ (x + a) - (ψ (x₀ + a) - g x₀) := by rw [hsep]
    _ = (ψ (x + a) + ψ x₀) - ψ x₀ - ψ (x₀ + a) + g x₀ := by abel
    _ = (ψ (x₀ + a) + ψ x) - ψ x₀ - ψ (x₀ + a) + g x₀ := by rw [hψ]
    _ = ψ x + (g x₀ - ψ x₀) := by abel

/-- **Agreement up to a shift.** -/
theorem shift_agreement {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [Nonempty G] (f g ψ : G → H) (B : Finset G) (S : Finset (G × G))
    (hsep : ∀ x x' a, (x, a) ∈ S → (x', a) ∈ S → f (x + a) - g x = f (x' + a) - g x')
    (hψ : ∀ y₁ ∈ B, ∀ y₂ ∈ B, ∀ y₃ ∈ B, ∀ y₄ ∈ B, y₁ + y₂ = y₃ + y₄ → ψ y₁ + ψ y₂ = ψ y₃ + ψ y₄)
    (hfψ : ∀ y ∈ B, f y = ψ y) :
    ∃ u : H, ∃ Y ⊆ B,
      (S.filter fun p => p.1 ∈ B ∧ p.1 + p.2 ∈ B).card ≤ Fintype.card G * Y.card ∧
      ∀ x ∈ Y, g x = ψ x + u := by
  set S' := S.filter fun p => p.1 ∈ B ∧ p.1 + p.2 ∈ B with hS'
  let F : G → Finset (G × G) := fun a => S'.filter fun p => p.2 = a
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun a => (F a).card)
    Finset.univ_nonempty
  have hsum : S'.card = ∑ b : G, (F b).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hbound : S'.card ≤ Fintype.card G * (F a).card := by
    rw [hsum]
    calc ∑ b : G, (F b).card ≤ ∑ _b : G, (F a).card :=
          Finset.sum_le_sum fun b _ => hmax b (Finset.mem_univ _)
      _ = Fintype.card G * (F a).card := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hYcard : (F a).card ≤ ((F a).image Prod.fst).card := by
    apply le_of_eq; symm
    apply Finset.card_image_of_injOn
    intro p hp q hq h
    have e1 := (Finset.mem_filter.mp hp).2
    have e2 := (Finset.mem_filter.mp hq).2
    exact Prod.ext h (e1.trans e2.symm)
  have hYB : (F a).image Prod.fst ⊆ B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
  by_cases hF : (F a).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hF
    obtain ⟨hp₀S', hp₀a⟩ := Finset.mem_filter.mp hp₀
    obtain ⟨hp₀S, hx₀, hxa₀⟩ := Finset.mem_filter.mp hp₀S'
    refine ⟨g p₀.1 - ψ p₀.1, (F a).image Prod.fst, hYB,
      hbound.trans (Nat.mul_le_mul_left _ hYcard), ?_⟩
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hpS', hpa⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpS, hx1, hxa1⟩ := Finset.mem_filter.mp hpS'
    have e₁ : p = (p.1, a) := Prod.ext rfl hpa
    have e₀ : p₀ = (p₀.1, a) := Prod.ext rfl hp₀a
    rw [hpa] at hxa1
    rw [hp₀a] at hxa₀
    exact shift_constant_on_fiber f g ψ B
      (hsep p.1 p₀.1 a (e₁ ▸ hpS) (e₀ ▸ hp₀S))
      (hψ _ hxa1 _ hx₀ _ hxa₀ _ hx1 (by abel)) (hfψ _ hxa1) (hfψ _ hxa₀)
  · have hempty : F a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    refine ⟨0, ∅, Finset.empty_subset _, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [hempty, Finset.card_empty, mul_zero] at hbound
    rw [Finset.card_empty, mul_zero]
    exact hbound

/-- **Shared linear part.** If `f` is locally affine on `A` with linear part
`ψ` on the difference set `K` (Lemma 7.8's `IsBHomomorphism`), and `S`
separates `f` and `g`, then `g` has the same linear part on each fiber:
`g x − g x′ = ψ(x − x′)` when `x + a, x′ + a ∈ A` and `x − x′ ∈ K`. -/
theorem shared_linear_part {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f g ψ : G → H) (A K : Finset G)
    (hloc : ∀ y ∈ A, ∀ y' ∈ A, y - y' ∈ K → f y - f y' = ψ (y - y'))
    {x x' a : G} (hsep : f (x + a) - g x = f (x' + a) - g x')
    (hx : x + a ∈ A) (hx' : x' + a ∈ A) (hK : x - x' ∈ K) :
    g x - g x' = ψ (x - x') := by
  have hd : (x + a) - (x' + a) = x - x' := by abel
  have h1 := hloc _ hx _ hx' (by rw [hd]; exact hK)
  rw [hd] at h1
  rw [← h1]
  rw [sub_eq_sub_iff_sub_eq_sub] at hsep
  rw [hsep]

end LeanProofs.GowersSzemeredi
