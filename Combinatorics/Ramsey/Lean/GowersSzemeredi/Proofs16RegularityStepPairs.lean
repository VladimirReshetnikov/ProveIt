import GowersSzemeredi.Proofs16RegularityStep

/-! One step of the algebraic regularity iteration for pairs ([49] proof of
Theorem 33, p. 28), in prime `ℤ/N` on a centred Bohr domain.

Bad pairs `(t, u)` of the class `C` carry a witness `(μ, μ′, v)` from a
finite list: `μ·ψ(t) + μ′·ψ(u) = v`, with `μ ∉ Λ` or `μ′ ∉ Λ`, where
`Λ = relationSubmodule C ψ`. If at least `θ|C|²` pairs are bad, then:
* one witness carries a `1/|R|` share (`exists_popular_witness`);
* in the case `μ ∉ Λ`, the relation `μ·ψ(t) = v − μ′·ψ(u)` holds for
  `θ′|C|²` pairs, so `μ·ψ(t₁) = μ·ψ(t₂)` for `θ′²|C|²` pairs
  (`collision_pairs_ge`);
* some `t₁` has a level set `F′` of `μ·ψ` with `|F′| ≥ θ′²|C|`
  (`exists_dense_collision_level_set`);
* `μ·ψ` is constant on `F′`, hence vanishes (relative to `0`) on
  `B(Spec F′; 1/(8π))` (`freiman_const_on_bohr_of_dense`).

The case `μ′ ∉ Λ` is symmetric. The common conclusion
(`regularity_step_pairs`) is a coefficient vector outside `Λ` that lies
in the relation subspace of `C ∩ B′`, with `|F′| ≥ (θ/|R|)²|C|`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **A dense level set from many collisions.** -/
theorem exists_dense_collision_level_set {Y Z : Type*} [Fintype Y] [Nonempty Y] [DecidableEq Z]
    (f : Y → Z) {θ : Real}
    (hcoll : θ * (Fintype.card Y : Real) ^ 2 ≤
      ((Finset.univ.filter fun p : Y × Y => f p.1 = f p.2).card : Real)) :
    ∃ y₁ : Y, θ * Fintype.card Y ≤ ((Finset.univ.filter fun y₂ => f y₁ = f y₂).card : Real) := by
  by_contra hno
  push Not at hno
  have hsum : ((Finset.univ.filter fun p : Y × Y => f p.1 = f p.2).card : Real) =
      ∑ y₁ : Y, ((Finset.univ.filter fun y₂ => f y₁ = f y₂).card : Real) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    apply Finset.sum_congr rfl; intro y₁ _
    rw [Finset.card_filter]; push_cast; rfl
  have hlt : ∑ y₁ : Y, ((Finset.univ.filter fun y₂ => f y₁ = f y₂).card : Real) <
      ∑ _y₁ : Y, θ * Fintype.card Y :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun y₁ _ => hno y₁
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  rw [hsum] at hcoll
  nlinarith

/-- **A Bohr set on which a combination vanishes, from many matchings.** -/
theorem relation_of_matching {N : Nat} [NeZero N] [Fact N.Prime] {κ : Type*} [Fintype κ]
    (Ψ : Finset (ZMod N)) {σ : Real} (hσ : 0 ≤ σ) (ψ : κ → ZMod N → ZMod N)
    (hψ : ∀ j, IsFreimanLinearOn (bohr Ψ σ) (ψ j)) (C : Finset (ZMod N))
    (hC : C ⊆ bohr Ψ (σ / 4)) (hCne : C.Nonempty) (μ : κ → ZMod N) (h : ↥C → ZMod N)
    {θ : Real} (hθ : 0 < θ)
    (hmatch : θ * (C.card : Real) ^ 2 ≤
      ((Finset.univ.filter fun p : ↥C × ↥C =>
        ∑ j, μ j * ψ j (p.1 : ZMod N) = h p.2).card : Real)) :
    ∃ F' : Finset (ZMod N), F' ⊆ C ∧ θ ^ 2 * C.card ≤ F'.card ∧
      ((section7Spectrum F' (F'.card / N)).card : Real) ≤
        16 * ((F'.card : Real) / N) ^ (-(2 : Real)) ∧
      μ ∈ relationSubmodule
        (C ∩ bohr (section7Spectrum F' (F'.card / N)) (1 / (8 * Real.pi))) ψ := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  haveI : Nonempty ↥C := ⟨⟨_, hCne.choose_spec⟩⟩
  have hcardC : Fintype.card ↥C = C.card := Fintype.card_coe C
  let f : ↥C → ZMod N := fun t => ∑ j, μ j * ψ j (t : ZMod N)
  have hcoll := collision_pairs_ge f h hθ.le (by rw [hcardC]; exact hmatch)
  obtain ⟨t₁, ht₁⟩ := exists_dense_collision_level_set f (θ := θ ^ 2) hcoll
  rw [hcardC] at ht₁
  -- the level set in the ambient group
  set F' := (Finset.univ.filter fun t₂ : ↥C => f t₁ = f t₂).map (Function.Embedding.subtype _)
    with hF'
  have hF'card : F'.card = (Finset.univ.filter fun t₂ : ↥C => f t₁ = f t₂).card :=
    Finset.card_map _
  have hF'sub : F' ⊆ C := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hx
    exact t.property
  have hconst : ∀ z ∈ F', (fun y => ∑ j, μ j * ψ j y) z = f t₁ := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hz
    exact ((Finset.mem_filter.mp ht).2).symm
  have hpos : (0 : Real) < F'.card := by
    rw [hF'card]
    have : (0 : Real) < θ ^ 2 * C.card := by
      have : (0 : Real) < C.card := by exact_mod_cast hCne.card_pos
      positivity
    linarith
  have hα : (0 : Real) < F'.card / N := div_pos hpos hNR
  have hcard : (F'.card : Real) = (F'.card / N) * N := (div_mul_cancel₀ _ hNR.ne').symm
  obtain ⟨hspec, hker⟩ := freiman_const_on_bohr_of_dense Ψ hσ
    (IsFreimanLinearOn.linear_combination hψ μ) F' (fun z hz => hC (hF'sub hz)) hconst hα hcard
  refine ⟨F', hF'sub, by rw [hF'card]; exact ht₁, hspec, ?_⟩
  rw [mem_relationSubmodule]
  intro y hy
  have hy' := (hker y (Finset.mem_inter.mp hy).2).2
  rw [← sub_eq_zero] at hy'
  have hsum : ∑ j, μ j * (ψ j y - ψ j 0) = ∑ j, μ j * ψ j y - ∑ j, μ j * ψ j 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  exact hy'

/-- **One step of the regularity iteration, pairs.** -/
theorem regularity_step_pairs {N : Nat} [NeZero N] [Fact N.Prime] {κ : Type*} [Fintype κ]
    (Ψ : Finset (ZMod N)) {σ : Real} (hσ : 0 ≤ σ) (ψ : κ → ZMod N → ZMod N)
    (hψ : ∀ j, IsFreimanLinearOn (bohr Ψ σ) (ψ j)) (C : Finset (ZMod N))
    (hC : C ⊆ bohr Ψ (σ / 4)) (hCne : C.Nonempty)
    (R : Finset ((κ → ZMod N) × (κ → ZMod N) × ZMod N)) (hR : R.Nonempty)
    (Bad : Finset (↥C × ↥C)) {θ : Real} (hθ : 0 < θ)
    (hBad : θ * (C.card : Real) ^ 2 ≤ Bad.card)
    (hwit : ∀ p ∈ Bad, ∃ w ∈ R,
      (w.1 ∉ relationSubmodule C ψ ∨ w.2.1 ∉ relationSubmodule C ψ) ∧
        ∑ j, w.1 j * ψ j (p.1 : ZMod N) + ∑ j, w.2.1 j * ψ j (p.2 : ZMod N) = w.2.2) :
    ∃ μ : κ → ZMod N, μ ∉ relationSubmodule C ψ ∧
      ∃ F' : Finset (ZMod N), F' ⊆ C ∧ (θ / R.card) ^ 2 * C.card ≤ F'.card ∧
        ((section7Spectrum F' (F'.card / N)).card : Real) ≤
          16 * ((F'.card : Real) / N) ^ (-(2 : Real)) ∧
        μ ∈ relationSubmodule
          (C ∩ bohr (section7Spectrum F' (F'.card / N)) (1 / (8 * Real.pi))) ψ := by
  have hRpos : (0 : Real) < R.card := by exact_mod_cast hR.card_pos
  obtain ⟨w, hwR, hpop⟩ := exists_popular_witness Bad R
    (fun p w => (w.1 ∉ relationSubmodule C ψ ∨ w.2.1 ∉ relationSubmodule C ψ) ∧
      ∑ j, w.1 j * ψ j (p.1 : ZMod N) + ∑ j, w.2.1 j * ψ j (p.2 : ZMod N) = w.2.2) hR hwit
  set P' := Bad.filter fun p => (w.1 ∉ relationSubmodule C ψ ∨ w.2.1 ∉ relationSubmodule C ψ) ∧
    ∑ j, w.1 j * ψ j (p.1 : ZMod N) + ∑ j, w.2.1 j * ψ j (p.2 : ZMod N) = w.2.2 with hP'
  have hθ' : 0 < θ / R.card := by positivity
  have hP'card : θ / R.card * (C.card : Real) ^ 2 ≤ P'.card := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    nlinarith
  -- `P′` is nonempty, so the disjunction is fixed by `w`
  have hP'ne : P'.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : Real) < θ / R.card * (C.card : Real) ^ 2 := by
      have : (0 : Real) < C.card := by exact_mod_cast hCne.card_pos
      positivity
    exact_mod_cast this.trans_le hP'card
  obtain ⟨p₀, hp₀⟩ := hP'ne
  rcases (Finset.mem_filter.mp hp₀).2.1 with hμ | hμ'
  · -- `μ ∉ Λ`: match `μ·ψ(t)` against `v − μ′·ψ(u)`
    obtain ⟨F', hsub, hcard, hspec, hmem⟩ := relation_of_matching Ψ hσ ψ hψ C hC hCne w.1
      (fun u => w.2.2 - ∑ j, w.2.1 j * ψ j (u : ZMod N)) hθ' (by
        refine hP'card.trans ?_
        exact_mod_cast Finset.card_le_card (fun p hp => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by
            have := (Finset.mem_filter.mp hp).2.2
            rw [← this]; ring⟩))
    exact ⟨w.1, hμ, F', hsub, hcard, hspec, hmem⟩
  · -- `μ′ ∉ Λ`: match `μ′·ψ(u)` against `v − μ·ψ(t)`, with the pair swapped
    obtain ⟨F', hsub, hcard, hspec, hmem⟩ := relation_of_matching Ψ hσ ψ hψ C hC hCne w.2.1
      (fun t => w.2.2 - ∑ j, w.1 j * ψ j (t : ZMod N)) hθ' (by
        refine hP'card.trans ?_
        rw [← Finset.card_map (Equiv.prodComm ↥C ↥C).toEmbedding]
        exact_mod_cast Finset.card_le_card (fun q hq => by
          obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have := (Finset.mem_filter.mp hp).2.2
          simp only [Equiv.toEmbedding_apply, Equiv.prodComm_apply, Prod.fst_swap,
            Prod.snd_swap]
          rw [← this]; ring))
    exact ⟨w.2.1, hμ', F', hsub, hcard, hspec, hmem⟩

end LeanProofs.GowersSzemeredi
