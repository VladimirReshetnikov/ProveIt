import GowersSzemeredi.Proofs16BohrAnnulus

/-! Spectral annihilation for Bohr sets in `ℤ/N`, `N` prime.

This is the Fourier half of [49]'s Theorem 27 (arXiv:2109.03093): a large
Fourier coefficient of a Bohr set's indicator is almost annihilated by a
smaller Bohr set.
* `fourier_translate`: translating `f` by `b` multiplies `f̂(ξ)` by
  `e(−bξ)`.
* `bohr_escape_card_le`: at most `|K|(4ρ′N + 2)` points `x ∈ B(K;ρ)` have
  `x + d ∉ B(K;ρ)` for a given `d ∈ B(K;ρ′)`. Such points lie in the annulus
  `B(K;ρ) ∖ B(K;ρ−ρ′)` (`bohr_annulus_card_le`).
* `bohr_fourier_annihilation`: for every `b ∈ B(K;ρ′)`,
  `|1̂_B(ξ)| · |1 − e(−bξ)| ≤ 2|K|(4ρ′N + 2)`.

So `|1̂_B(ξ)| ≥ η|B|` forces `e(bξ)` to be close to `1` on the whole of
`B(K;ρ′)`, once `ρ′ ≪ η|B|/(|K|N)`. The other half of Theorem 27, the
duality that turns such smallness into membership in a bounded span
`⟨K⟩_R`, is geometry of numbers and is not formalized here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Translation multiplies Fourier coefficients by a character value. -/
theorem fourier_translate {N : Nat} [NeZero N] (f : ZMod N → Complex) (b ξ : ZMod N) :
    fourier (fun x => f (x - b)) ξ = exponential (-(b * ξ)) * fourier f ξ := by
  unfold fourier exponential
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addRight b)
  intro y
  simp only [Equiv.coe_addRight, add_sub_cancel_right, smul_eq_mul]
  rw [show -((y + b) * ξ) = -(y * ξ) + -(b * ξ) by ring, AddChar.map_add_eq_mul]
  ring

/-- Adding a small element keeps the deep part of a Bohr set inside it. -/
theorem bohr_add_small {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ ρ' : Real} {y d : ZMod N}
    (hd : d ∈ bohr K ρ') (hy : y ∈ bohr K (ρ - ρ')) : y + d ∈ bohr K ρ := by
  unfold bohr at hd hy ⊢
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have h1 := (Finset.mem_filter.mp hy).2 r hr
  have h2 := (Finset.mem_filter.mp hd).2 r hr
  have h3 : (centeredAbs (r * (y + d)) : Real) ≤ centeredAbs (r * y) + centeredAbs (r * d) := by
    rw [mul_add]; exact_mod_cast centeredAbs_add_le _ _
  linarith

/-- **Escaping points.** Few points of `B(K;ρ)` leave it under a small shift. -/
theorem bohr_escape_card_le {N : Nat} [NeZero N] [Fact N.Prime] (K : Finset (ZMod N))
    {ρ ρ' : Real} (hρ' : 0 ≤ ρ') (hρρ' : 0 ≤ ρ - ρ') {d : ZMod N} (hd : d ∈ bohr K ρ') :
    (((bohr K ρ).filter fun x => x + d ∉ bohr K ρ).card : Real) ≤ K.card * (4 * ρ' * N + 2) := by
  have hsub : (bohr K ρ).filter (fun x => x + d ∉ bohr K ρ) ⊆
      bohr K (ρ + ρ') \ bohr K (ρ - ρ') := by
    intro x hx
    obtain ⟨hxB, hxd⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨bohr_mono_radius K (by linarith) hxB, fun h => hxd ?_⟩
    exact bohr_add_small K hd h
  calc (((bohr K ρ).filter fun x => x + d ∉ bohr K ρ).card : Real)
      ≤ ((bohr K (ρ + ρ') \ bohr K (ρ - ρ')).card : Real) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ K.card * (4 * ρ' * N + 2) := by
        have := bohr_annulus_card_le K (ρ := ρ) (η := ρ') hρ' hρρ'
        simpa using this

/-- Negation preserves Bohr sets. -/
theorem neg_mem_bohr {N : Nat} [NeZero N] {K : Finset (ZMod N)} {ρ : Real} {b : ZMod N}
    (hb : b ∈ bohr K ρ) : -b ∈ bohr K ρ := by
  unfold bohr at hb ⊢
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have := (Finset.mem_filter.mp hb).2 r hr
  rwa [mul_neg, centeredAbs_neg]

/-- **Spectral annihilation.** -/
theorem bohr_fourier_annihilation {N : Nat} [NeZero N] [Fact N.Prime] (K : Finset (ZMod N))
    {ρ ρ' : Real} (hρ' : 0 ≤ ρ') (hρρ' : 0 ≤ ρ - ρ') {b : ZMod N} (hb : b ∈ bohr K ρ')
    (ξ : ZMod N) :
    ‖fourier (indicator (bohr K ρ)) ξ‖ * ‖1 - exponential (-(b * ξ))‖ ≤
      2 * (K.card * (4 * ρ' * N + 2)) := by
  set B := bohr K ρ
  -- `(1 − e(−bξ)) 1̂_B(ξ) = 1̂_B(ξ) − (translate)^(ξ)`
  have hdiff : (1 - exponential (-(b * ξ))) * fourier (indicator B) ξ =
      fourier (fun x => indicator B x - indicator B (x - b)) ξ := by
    have hlin : fourier (fun x => indicator B x - indicator B (x - b)) ξ =
        fourier (indicator B) ξ - fourier (fun x => indicator B (x - b)) ξ := by
      unfold fourier
      rw [ZMod.dft_apply, ZMod.dft_apply, ZMod.dft_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      simp only [smul_eq_mul]
      ring
    rw [hlin, fourier_translate]
    ring
  have hbound : ‖fourier (fun x => indicator B x - indicator B (x - b)) ξ‖ ≤
      ∑ x : ZMod N, ‖indicator B x - indicator B (x - b)‖ := by
    unfold fourier
    rw [ZMod.dft_apply]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    rw [smul_eq_mul, norm_mul, (ZMod.stdAddChar (N := N)).norm_apply, one_mul]
  -- the pointwise difference is supported on two escape sets
  have hsum : ∑ x : ZMod N, ‖indicator B x - indicator B (x - b)‖ ≤
      (((B.filter fun x => x + -b ∉ B).card : Real) + ((B.filter fun x => x + b ∉ B).card : Real)) := by
    have hpt : ∀ x, ‖indicator B x - indicator B (x - b)‖ ≤
        (if x ∈ B ∧ x + -b ∉ B then 1 else 0) + (if x - b ∈ B ∧ (x - b) + b ∉ B then 1 else 0) := by
      intro x
      have hxb : x - b = x + -b := by ring
      unfold indicator
      by_cases hx : x ∈ B <;> by_cases hx' : x - b ∈ B <;>
        simp [hx, hx', hxb ▸ hx', sub_add_cancel]
    calc ∑ x, ‖indicator B x - indicator B (x - b)‖
        ≤ ∑ x : ZMod N, ((if x ∈ B ∧ x + -b ∉ B then (1 : Real) else 0) +
            (if x - b ∈ B ∧ (x - b) + b ∉ B then 1 else 0)) := Finset.sum_le_sum fun x _ => hpt x
      _ = _ := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.sum_boole]
            congr 2
            ext x; simp
          · rw [Finset.sum_boole]
            have : (Finset.univ.filter fun x : ZMod N => x - b ∈ B ∧ (x - b) + b ∉ B) =
                (B.filter fun y => y + b ∉ B).image (· + b) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · rintro ⟨h1, h2⟩
                exact ⟨x - b, ⟨h1, h2⟩, sub_add_cancel x b⟩
              · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
                simpa using And.intro h1 h2
            rw [this, Finset.card_image_of_injective _ (add_left_injective b)]
  have hesc₁ := bohr_escape_card_le K hρ' hρρ' (neg_mem_bohr hb)
  have hesc₂ := bohr_escape_card_le K hρ' hρρ' hb
  calc ‖fourier (indicator B) ξ‖ * ‖1 - exponential (-(b * ξ))‖
      = ‖(1 - exponential (-(b * ξ))) * fourier (indicator B) ξ‖ := by rw [norm_mul, mul_comm]
    _ = ‖fourier (fun x => indicator B x - indicator B (x - b)) ξ‖ := by rw [hdiff]
    _ ≤ _ := hbound.trans hsum
    _ ≤ 2 * (K.card * (4 * ρ' * N + 2)) := by linarith

end LeanProofs.GowersSzemeredi
