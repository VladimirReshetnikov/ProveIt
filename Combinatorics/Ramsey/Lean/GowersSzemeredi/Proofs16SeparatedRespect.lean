import GowersSzemeredi.Proofs16AbstractBSGClaim44

/-! The double Cauchy–Schwarz step of Milićević's Lemma 9.2
(arXiv:2601.01682, printed p. 64).

Suppose a family `Q` of triples `(x, a, ω)` *separates* `f` and `g`: the
value `f(x + a) − g(x)` depends only on `(a, ω)` within `Q`. Then `f`
respects many additive quadruples:
* `separated_pairs_ge`: collisions over the `(a, ω)`-fibers give at least
  `|Q|²/(|G||Ω|)` pairs of triples sharing `(a, ω)`. Each has
  `f(x + a) − f(x′ + a) = g(x) − g(x′)`.
* `respected_quadruples_of_separated`: if `c|G|²|Ω| ≤ |Q|`, then at least
  `c⁴|G|⁴` tuples `(x, x′, a, b)` have
  `f(x + a) − f(x′ + a) = f(x + b) − f(x′ + b)`. These are additive
  quadruples `(x + a) + (x′ + b) = (x′ + a) + (x + b)` respected by `f`,
  the input of Gowers's Corollary 7.6 (Milićević's Theorem 2.26).

The second step forgets `ω` (at most `|Ω|` to one) and takes collisions
over the `(x, x′)`-fibers. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **Respected quadruples from a separated family.** -/
theorem respected_quadruples_of_separated {G H Ω : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype Ω] [Nonempty Ω] (f g : G → H) (Q : Finset (G × G × Ω))
    (hsep : ∀ x x' a ω, (x, a, ω) ∈ Q → (x', a, ω) ∈ Q → f (x + a) - g x = f (x' + a) - g x')
    {c : Real} (hc : 0 ≤ c)
    (hQ : c * (Fintype.card G : Real) ^ 2 * Fintype.card Ω ≤ Q.card) :
    c ^ 4 * (Fintype.card G : Real) ^ 4 ≤
      ((Finset.univ : Finset (G × G × G × G)).filter fun t =>
        f (t.1 + t.2.2.1) - f (t.2.1 + t.2.2.1) = f (t.1 + t.2.2.2) - f (t.2.1 + t.2.2.2)).card := by
  set n := (Fintype.card G : Real) with hn
  set m := (Fintype.card Ω : Real) with hm
  rcases Nat.eq_zero_or_pos (Fintype.card G) with hG0 | hGpos
  · have : n = 0 := by rw [hn, hG0]; simp
    rw [this]; simp
  have hOpos : 0 < Fintype.card Ω := Fintype.card_pos
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hGpos
  have hmpos : 0 < m := by rw [hm]; exact_mod_cast hOpos
  -- Step 1: collisions over `(a, ω)`
  let key1 : G × G × Ω → G × Ω := fun q => (q.2.1, q.2.2)
  have hC1 := collisions_ge Q key1 Finset.univ (fun _ _ => Finset.mem_univ _)
  let C1 := (Q ×ˢ Q).filter fun p => key1 p.1 = key1 p.2
  have hC1' : (Q.card : Real) ^ 2 ≤ (n * m) * C1.card := by
    have hu : ((Finset.univ : Finset (G × Ω)).card : Real) = n * m := by
      rw [Finset.card_univ, Fintype.card_prod]; push_cast; rfl
    rw [← hu]; convert hC1 using 3
    congr 1; ext p; simp only [C1, Finset.mem_filter]
  -- Step 2: forget `ω`
  let T2 := (Finset.univ : Finset (G × G × G)).filter fun t =>
    f (t.1 + t.2.2) - f (t.2.1 + t.2.2) = g t.1 - g t.2.1
  have hT2 : (C1.card : Real) ≤ m * T2.card := by
    have hmap : ∀ p ∈ C1, ((p.1.1, p.2.1, p.1.2.1) : G × G × G) ∈ T2 := by
      intro p hp
      obtain ⟨hpQ, hk⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpQ
      simp only [key1, Prod.mk.injEq] at hk
      obtain ⟨ha, hω⟩ := hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have := hsep p.1.1 p.2.1 p.1.2.1 p.1.2.2 h1 (by
        rw [show (p.2.1, p.1.2.1, p.1.2.2) = p.2 by rw [ha, hω]]; exact h2)
      rw [sub_eq_sub_iff_sub_eq_sub] at this
      exact this
    have hle : ∀ t, (C1.filter fun p => ((p.1.1, p.2.1, p.1.2.1) : G × G × G) = t).card ≤
        Fintype.card Ω := by
      intro t
      calc _ ≤ (Finset.univ : Finset Ω).card := by
            apply Finset.card_le_card_of_injOn (fun p => p.1.2.2)
            · intro _ _; exact Finset.mem_univ _
            · intro p hp p' hp' h
              obtain ⟨hpC, ht⟩ := Finset.mem_filter.mp hp
              obtain ⟨hpC', ht'⟩ := Finset.mem_filter.mp hp'
              have hk := (Finset.mem_filter.mp hpC).2
              have hk' := (Finset.mem_filter.mp hpC').2
              simp only [key1, Prod.mk.injEq] at hk hk'
              rw [← ht'] at ht
              simp only [Prod.mk.injEq] at ht
              obtain ⟨e1, e2, e3⟩ := ht
              have hω : p.1.2.2 = p'.1.2.2 := h
              apply Prod.ext
              · exact Prod.ext e1 (Prod.ext e3 hω)
              · exact Prod.ext e2 (Prod.ext (hk.1.symm.trans (e3.trans hk'.1)) (hk.2.symm.trans
                  (hω.trans hk'.2)))
        _ = Fintype.card Ω := Finset.card_univ
    have h1 := Finset.card_le_mul_card_image
      (f := fun p : (G × G × Ω) × (G × G × Ω) => ((p.1.1, p.2.1, p.1.2.1) : G × G × G)) C1
      (Fintype.card Ω) (fun t _ => hle t)
    have h2 : (C1.image fun p : (G × G × Ω) × (G × G × Ω) =>
        ((p.1.1, p.2.1, p.1.2.1) : G × G × G)).card ≤ T2.card := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      exact hmap p hp
    calc (C1.card : Real) ≤ (Fintype.card Ω : Real) * ((C1.image fun p : (G × G × Ω) × (G × G × Ω) =>
          ((p.1.1, p.2.1, p.1.2.1) : G × G × G)).card : Real) := by exact_mod_cast h1
      _ ≤ m * T2.card := mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (by positivity)
  -- Step 3: collisions over `(x, x')`
  let key3 : G × G × G → G × G := fun t => (t.1, t.2.1)
  have hC3 := collisions_ge T2 key3 Finset.univ (fun _ _ => Finset.mem_univ _)
  let C3 := (T2 ×ˢ T2).filter fun p => key3 p.1 = key3 p.2
  have hC3' : (T2.card : Real) ^ 2 ≤ n ^ 2 * C3.card := by
    have hu : ((Finset.univ : Finset (G × G)).card : Real) = n ^ 2 := by
      rw [Finset.card_univ, Fintype.card_prod]; push_cast; ring
    rw [← hu]; convert hC3 using 3
    congr 1; ext p; simp only [C3, Finset.mem_filter]
  have hfinal : C3.card ≤ ((Finset.univ : Finset (G × G × G × G)).filter fun t =>
      f (t.1 + t.2.2.1) - f (t.2.1 + t.2.2.1) = f (t.1 + t.2.2.2) - f (t.2.1 + t.2.2.2)).card := by
    apply Finset.card_le_card_of_injOn (fun p => ((p.1.1, p.1.2.1, p.1.2.2, p.2.2.2) :
      G × G × G × G))
    · intro p hp
      obtain ⟨hpT, hk⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpT
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      simp only [key3, Prod.mk.injEq] at hk
      obtain ⟨k1, k2⟩ := hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only
      rw [e1, k1, k2, ← e2]
    · intro p hp p' hp' h
      have hk := (Finset.mem_filter.mp hp).2
      have hk' := (Finset.mem_filter.mp hp').2
      simp only [key3, Prod.mk.injEq] at hk hk' h
      obtain ⟨a1, a2, a3, a4⟩ := h
      apply Prod.ext
      · exact Prod.ext a1 (Prod.ext a2 a3)
      · exact Prod.ext (hk.1.symm.trans (a1.trans hk'.1))
          (Prod.ext (hk.2.symm.trans (a2.trans hk'.2)) a4)
  -- assemble
  have hQ2 : (c * n ^ 2 * m) ^ 2 ≤ (Q.card : Real) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hQ 2
  have hC1ge : c ^ 2 * n ^ 3 * m ≤ C1.card := by
    have h := hQ2.trans hC1'
    have : (c * n ^ 2 * m) ^ 2 = (n * m) * (c ^ 2 * n ^ 3 * m) := by ring
    rw [this] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have hT2ge : c ^ 2 * n ^ 3 ≤ T2.card := by
    have h := hC1ge.trans hT2
    have : c ^ 2 * n ^ 3 * m = m * (c ^ 2 * n ^ 3) := by ring
    rw [this] at h
    exact le_of_mul_le_mul_left h hmpos
  have hC3ge : c ^ 4 * n ^ 4 ≤ C3.card := by
    have h := (pow_le_pow_left₀ (by positivity) hT2ge 2).trans hC3'
    have : (c ^ 2 * n ^ 3) ^ 2 = n ^ 2 * (c ^ 4 * n ^ 4) := by ring
    rw [this] at h
    exact le_of_mul_le_mul_left h (by positivity)
  exact hC3ge.trans (by exact_mod_cast hfinal)

end LeanProofs.GowersSzemeredi
