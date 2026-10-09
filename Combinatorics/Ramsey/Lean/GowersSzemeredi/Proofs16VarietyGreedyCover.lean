import GowersSzemeredi.Proofs16DeepAgreement
import GowersSzemeredi.Proofs05Lemma9Induction

/-! Greedy covering by variety pieces.

Milićević's structure (`MilicevicDeepVarietyStructure`) captures only an
`exp(−B)` fraction of a Freiman bihomomorphism's domain. Iterating captures
almost all of it. While at least `θN²` points remain uncovered, apply the
structure at density `θ` to the remainder, which is still a Freiman
bihomomorphism domain (`IsEBihomomorphism.mono`). Then remove the shifted
deep agreement set, which has at least `δN²` points, `δ = exp(−B(θ))`.

`greedy_variety_cover`: the domain is covered, except for fewer than `θN²`
points, by at most `exp(B(θ))` pieces (disjoint by construction, though
the statement does not record it). Each piece `G` is a *variety piece*
(`IsVarietyPiece`). That means there are variety data with Milićević's
bounds at density `θ`, and a Freiman bihomomorphism `Φ` on `V(ρ)`, such that
every `q ∈ G` satisfies `q − (s,t) ∈ V(ρ/2)` and `φ q = Φ(q − (s,t))`. So
`φ`'s graph over `G`, shifted back by `(s,t)`, is part of `Φ`'s graph over
`V(ρ/2)`. The peer's `exists_freiman_variety_cover` covers that graph with
count 9, and `MultiplyLinearWith.translate` moves the cover back.

`greedy_variety_cover_family` does the same for several bihomomorphisms
`φ_j` on domains `A_j`. It runs the greedy cover at `θ/n` for each, leaving
one exceptional set of size `< θN²` and at most `n·exp(B(θ/n))` pieces.
Each piece carries its owner `j`.

This is the structure side (S) of Part J for dimension two, from a Freiman
bihomomorphism on a dense set. The extraction of such bihomomorphisms from
a relation with the product property is a separate input, and is not
addressed here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Restricting a domain keeps the bihomomorphism property. -/
theorem IsEBihomomorphism.mono {N : Nat} {A A' : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} {E : Set (ZMod N)} (h : IsEBihomomorphism A Φ E)
    (hsub : A' ⊆ A) : IsEBihomomorphism A' Φ E :=
  ⟨fun x₁ x₂ x₃ x₄ y hs h1 h2 h3 h4 => h.1 x₁ x₂ x₃ x₄ y hs (hsub h1) (hsub h2) (hsub h3) (hsub h4),
   fun x y₁ y₂ y₃ y₄ hs h1 h2 h3 h4 => h.2 x y₁ y₂ y₃ y₄ hs (hsub h1) (hsub h2) (hsub h3) (hsub h4)⟩

/-- A variety piece of `φ` with Milićević's bounds at density `c`. -/
def IsVarietyPiece {N : Nat} [NeZero N] (D : Nat) (c : Real) (φ : ZMod N × ZMod N → ZMod N)
    (G : Finset (ZMod N × ZMod N)) : Prop :=
  ∃ (Γ Ψ : Finset (ZMod N)) (r : Nat) (L : Fin r → ZMod N → ZMod N) (ρ : Real)
    (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
    (Γ.card : Real) ≤ milicevicBound D c ∧ (Ψ.card : Real) ≤ milicevicBound D c ∧
    (r : Real) ≤ milicevicBound D c ∧ Real.exp (-milicevicBound D c) ≤ ρ ∧
    (∀ i, IsFreimanLinearOn (bohr Ψ ρ) (L i)) ∧
    IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0} ∧
    ∀ q ∈ G, (q.1 - s, q.2 - t) ∈ bilinearBohrVariety Γ Ψ L (ρ / 2) ∧
      φ q = Φ (q.1 - s, q.2 - t)

/-- **One greedy step.** A domain of size at least `θN²` contains a variety
piece with at least `exp(−B(θ)) N²` points. -/
theorem exists_variety_piece {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    {N : Nat} [NeZero N] {θ : Real} (hθ : 0 < θ) {φ : ZMod N × ZMod N → ZMod N}
    {A : Finset (ZMod N × ZMod N)} (hA : IsEBihomomorphism A φ {0})
    (hsize : θ * (N : Real) ^ 2 ≤ A.card) :
    ∃ G : Finset (ZMod N × ZMod N), G ⊆ A ∧ IsVarietyPiece D θ φ G ∧
      Real.exp (-milicevicBound D θ) * (N : Real) ^ 2 ≤ G.card := by
  obtain ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hagree⟩ := hM N A φ θ hθ hsize hA
  let G := (varietyAgreement Γ Ψ L (ρ / 2) A φ Φ s t).image fun p => (p.1 + s, p.2 + t)
  have hinj : Function.Injective fun p : ZMod N × ZMod N => (p.1 + s, p.2 + t) := by
    intro p p' h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.1) (add_right_cancel h.2)
  refine ⟨G, ?_, ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, ?_⟩, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hp).2.1
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hpV, _, hpΦ⟩ := Finset.mem_filter.mp hp
    simp only [add_sub_cancel_right]
    exact ⟨hpV, hpΦ.symm⟩
  · rw [Finset.card_image_of_injective _ hinj]
    exact hagree

/-- **Greedy covering by variety pieces.** -/
theorem greedy_variety_cover {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    {N : Nat} [NeZero N] {θ : Real} (hθ : 0 < θ) {φ : ZMod N × ZMod N → ZMod N}
    {A₀ : Finset (ZMod N × ZMod N)} (hA₀ : IsEBihomomorphism A₀ φ {0}) :
    ∃ (n : Nat) (G : Fin n → Finset (ZMod N × ZMod N)),
      (n : Real) ≤ Real.exp (milicevicBound D θ) ∧
      ((A₀ \ Finset.univ.biUnion G).card : Real) < θ * (N : Real) ^ 2 ∧
      ∀ i, G i ⊆ A₀ ∧ IsVarietyPiece D θ φ (G i) := by
  set δ := Real.exp (-milicevicBound D θ) with hδ
  have hδpos : 0 < δ := Real.exp_pos _
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : (0 : Real) < (N : Real) ^ 2 := by positivity
  -- strengthened statement: count times `δN²` is at most the domain size
  have key : ∀ m : Nat, ∀ A : Finset (ZMod N × ZMod N), A ⊆ A₀ → A.card ≤ m →
      ∃ (n : Nat) (G : Fin n → Finset (ZMod N × ZMod N)),
        (n : Real) * (δ * (N : Real) ^ 2) ≤ A.card ∧
        ((A \ Finset.univ.biUnion G).card : Real) < θ * (N : Real) ^ 2 ∧
        ∀ i, G i ⊆ A ∧ IsVarietyPiece D θ φ (G i) := by
    intro m
    induction m with
    | zero =>
      intro A _ hA
      have hA0 : A = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hA)
      refine ⟨0, Fin.elim0, by simp, ?_, fun i => i.elim0⟩
      rw [hA0]
      simp only [Finset.empty_sdiff, Finset.card_empty, Nat.cast_zero]
      positivity
    | succ m ih =>
      intro A hAA₀ hAm
      by_cases hsmall : (A.card : Real) < θ * (N : Real) ^ 2
      · refine ⟨0, Fin.elim0, by simp, ?_, fun i => i.elim0⟩
        exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) hsmall
      · push Not at hsmall
        obtain ⟨G₀, hG₀A, hG₀piece, hG₀card⟩ :=
          exists_variety_piece hM hθ (hA₀.mono hAA₀) hsmall
        have hG₀pos : 0 < G₀.card := by
          have : (0 : Real) < G₀.card := lt_of_lt_of_le (mul_pos hδpos hN2) hG₀card
          exact_mod_cast this
        have hrest : (A \ G₀).card ≤ m := by
          have h1 : (A \ G₀).card = A.card - G₀.card := Finset.card_sdiff_of_subset hG₀A
          have h2 : G₀.card ≤ A.card := Finset.card_le_card hG₀A
          omega
        obtain ⟨n, G, hcount, hrem, hpieces⟩ :=
          ih (A \ G₀) (Finset.sdiff_subset.trans hAA₀) hrest
        refine ⟨n + 1, Fin.cons G₀ G, ?_, ?_, ?_⟩
        · have hsd : ((A \ G₀).card : Real) = A.card - G₀.card := by
            rw [Finset.card_sdiff_of_subset hG₀A, Nat.cast_sub (Finset.card_le_card hG₀A)]
          push_cast
          nlinarith
        · refine lt_of_le_of_lt ?_ hrem
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hxA, hxU⟩ := Finset.mem_sdiff.mp hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxA, fun hx0 => hxU ?_⟩, fun hxG => hxU ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, by simpa using hx0⟩
          · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxG
            exact Finset.mem_biUnion.mpr ⟨i.succ, Finset.mem_univ _, by simpa using hi⟩
        · intro i
          refine Fin.cases ⟨hG₀A, hG₀piece⟩ (fun j => ?_) i
          obtain ⟨hj, hjp⟩ := hpieces j
          exact ⟨by simpa using hj.trans Finset.sdiff_subset, by simpa using hjp⟩
  obtain ⟨n, G, hcount, hrem, hpieces⟩ := key A₀.card A₀ subset_rfl le_rfl
  refine ⟨n, G, ?_, hrem, hpieces⟩
  have hA₀N : (A₀.card : Real) ≤ (N : Real) ^ 2 := by
    have : A₀.card ≤ N * N := by
      calc A₀.card ≤ (Finset.univ : Finset (ZMod N × ZMod N)).card := Finset.card_le_univ _
        _ = N * N := by simp [ZMod.card]
    have : (A₀.card : Real) ≤ ((N * N : Nat) : Real) := by exact_mod_cast this
    simpa [sq] using this
  have hprod : (n : Real) * (δ * (N : Real) ^ 2) ≤ (N : Real) ^ 2 := hcount.trans hA₀N
  have hnδ : (n : Real) * δ ≤ 1 := by
    have h := hprod
    rw [← mul_assoc] at h
    have := (mul_le_iff_le_one_left hN2).mp h
    exact this
  have hexp : Real.exp (milicevicBound D θ) * δ = 1 := by
    rw [hδ, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hEpos : 0 < Real.exp (milicevicBound D θ) := Real.exp_pos _
  nlinarith

/-- **Greedy covering of several bihomomorphisms.** Given Freiman
bihomomorphisms `φ_j` on domains `A_j` (`j < n`), at most `n·exp(B(θ/n))`
variety pieces, each inside the domain of its owner `j`, cover every
`A_j` outside a common exceptional set `U` with `|U| < θN²`. -/
theorem greedy_variety_cover_family {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    {N : Nat} [NeZero N] {θ : Real} (hθ : 0 < θ) {n : Nat} (hn : 0 < n)
    (φ : Fin n → ZMod N × ZMod N → ZMod N) (A : Fin n → Finset (ZMod N × ZMod N))
    (hA : ∀ j, IsEBihomomorphism (A j) (φ j) {0}) :
    ∃ (K : Nat) (piece : Fin K → Finset (ZMod N × ZMod N)) (owner : Fin K → Fin n)
      (U : Finset (ZMod N × ZMod N)),
      (K : Real) ≤ n * Real.exp (milicevicBound D (θ / n)) ∧
      (U.card : Real) < θ * (N : Real) ^ 2 ∧
      (∀ k, piece k ⊆ A (owner k) ∧ IsVarietyPiece D (θ / n) (φ (owner k)) (piece k)) ∧
      ∀ j, ∀ x ∈ A j, x ∉ U → ∃ k, owner k = j ∧ x ∈ piece k := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hθn : 0 < θ / n := div_pos hθ hnR
  choose m G hm hrem hpieces using fun j => greedy_variety_cover hM hθn (hA j)
  let e := section5NatFlattenEquiv m
  refine ⟨∑ j, m j, fun k => G (e.symm k).1 (e.symm k).2, fun k => (e.symm k).1,
    Finset.univ.biUnion (fun j => A j \ Finset.univ.biUnion (G j)), ?_, ?_, ?_, ?_⟩
  · push_cast
    calc (∑ j, (m j : Real)) ≤ ∑ _j : Fin n, Real.exp (milicevicBound D (θ / n)) :=
          Finset.sum_le_sum fun j _ => hm j
      _ = n * Real.exp (milicevicBound D (θ / n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · calc ((Finset.univ.biUnion (fun j => A j \ Finset.univ.biUnion (G j))).card : Real)
        ≤ ∑ j, ((A j \ Finset.univ.biUnion (G j)).card : Real) := by
          exact_mod_cast Finset.card_biUnion_le
      _ < ∑ _j : Fin n, θ / n * (N : Real) ^ 2 :=
          Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun j _ => hrem j
      _ = θ * (N : Real) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  · intro k
    exact hpieces (e.symm k).1 (e.symm k).2
  · intro j x hx hxU
    have hxG : x ∈ Finset.univ.biUnion (G j) := by
      by_contra hcon
      exact hxU (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_sdiff.mpr ⟨hx, hcon⟩⟩)
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxG
    refine ⟨e ⟨j, i⟩, ?_, ?_⟩
    · simp
    · show x ∈ G (e.symm (e ⟨j, i⟩)).1 (e.symm (e ⟨j, i⟩)).2
      rw [Equiv.symm_apply_apply]
      exact hi

end LeanProofs.GowersSzemeredi
