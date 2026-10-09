import GowersSzemeredi.Proofs16LineExtractor
import GowersSzemeredi.Proofs16SharperVarietyStructure

/-! The structure side from a deep structure theorem with any bound, in prime
moduli only.

`MilicevicDeepVarietyStructure D` fixes three things that its consumers do
not need:
* **Every modulus.** The structure side concludes only for prime
  `N ≥ N₀`, and the greedy cover applies the hypothesis at one density
  `θ`. The concurrent formalization of Milićević's proof ([49], J.91–J.99)
  produces exactly such prime, large-modulus statements.
* **The quasi-polynomial bound** `milicevicBound D c = (2 + 2 log c⁻¹)^D`.
  The pipeline in this corpus loses `13^d` with `d = poly(1/c)`, which is
  a polynomial bound `B(c) = poly(1/c)` that no fixed `D` dominates. Yet
  `Theorem162At 3` allows counts up to `exp(Θ(r log r))`, with `r`
  polynomial in `1/(γθ)` of degree `2⁵¹²` (J.5). So polynomial bounds of
  modest degree still fit the budget.

This module makes the chain parametric in a bound function
`Bnd : ℝ → ℝ` and in the moduli.
* `IsVarietyPieceB Bnd c φ G`: a variety piece with bound `Bnd c`.
  `IsVarietyPiece D` is the case `Bnd = milicevicBound D`.
* `DeepStructureAt Bnd N c`: the deep structure conclusion at one modulus
  and one density.
* `MilicevicDeepEventuallyPrime Bnd`: for every density `c > 0`, the deep
  structure holds in every prime modulus above some threshold `N₁(c)`. It
  is implied by the all-moduli contract
  (`MilicevicDeepVarietyStructure.eventuallyPrime`).
* `exists_variety_piece_at`, `greedy_variety_cover_at` and
  `greedy_variety_cover_family_at` need the hypothesis only at the one
  density they use.
* `variety_structure_side_eventually`, `structure_side_of_milicevic_eventually`
  and `structure_side_of_milicevic_sharper_eventually` are the structure
  side from the eventual prime contract, for any bound. The modulus
  threshold becomes `max N₀ N₁` at the single density `θ/2/m(γ, θ/2)`.
* `structure_side_of_milicevic_of_eventually` is the original statement,
  with `IsVarietyPiece D`, from the weaker hypothesis.

The proofs are those of `Proofs16VarietyGreedyCover`,
`Proofs16VarietyStructureSide`, `Proofs16LineExtractor` and
`Proofs16SharperVarietyStructure`, with the hypothesis weakened. The
original statements are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical
open BaseCase

/-- A variety piece of `φ` with bound `Bnd c`. -/
def IsVarietyPieceB {N : Nat} [NeZero N] (Bnd : Real → Real) (c : Real)
    (φ : ZMod N × ZMod N → ZMod N) (G : Finset (ZMod N × ZMod N)) : Prop :=
  ∃ (Γ Ψ : Finset (ZMod N)) (r : Nat) (L : Fin r → ZMod N → ZMod N) (ρ : Real)
    (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
    (Γ.card : Real) ≤ Bnd c ∧ (Ψ.card : Real) ≤ Bnd c ∧
    (r : Real) ≤ Bnd c ∧ Real.exp (-Bnd c) ≤ ρ ∧
    (∀ i, IsFreimanLinearOn (bohr Ψ ρ) (L i)) ∧
    IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0} ∧
    ∀ q ∈ G, (q.1 - s, q.2 - t) ∈ bilinearBohrVariety Γ Ψ L (ρ / 2) ∧
      φ q = Φ (q.1 - s, q.2 - t)

/-- The deep structure conclusion at one modulus and one density. -/
def DeepStructureAt (Bnd : Real → Real) (N : Nat) [NeZero N] (c : Real) : Prop :=
  ∀ (A : Finset (ZMod N × ZMod N)) (φ : ZMod N × ZMod N → ZMod N),
    c * (N : Real) ^ 2 ≤ A.card → IsEBihomomorphism A φ {0} →
    ∃ (Γ Ψ : Finset (ZMod N)) (r : Nat) (L : Fin r → ZMod N → ZMod N) (ρ : Real)
      (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
      (Γ.card : Real) ≤ Bnd c ∧ (Ψ.card : Real) ≤ Bnd c ∧
      (r : Real) ≤ Bnd c ∧ Real.exp (-Bnd c) ≤ ρ ∧
      (∀ i, IsFreimanLinearOn (bohr Ψ ρ) (L i)) ∧
      IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0} ∧
      Real.exp (-Bnd c) * (N : Real) ^ 2 ≤
        ((varietyAgreement Γ Ψ L (ρ / 2) A φ Φ s t).card : Real)

/-- The deep structure contract with bound `Bnd`, for each density,
eventually in prime moduli. -/
def MilicevicDeepEventuallyPrime (Bnd : Real → Real) : Prop :=
  ∀ c : Real, 0 < c → ∃ N₁ : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₁ ≤ N →
    DeepStructureAt Bnd N c

theorem MilicevicDeepVarietyStructure.at {D : Nat} (h : MilicevicDeepVarietyStructure D)
    {N : Nat} [NeZero N] {c : Real} (hc : 0 < c) : DeepStructureAt (milicevicBound D) N c :=
  fun A φ hA hφ => h N A φ c hc hA hφ

/-- The all-moduli contract implies the prime, eventual one. -/
theorem MilicevicDeepVarietyStructure.eventuallyPrime {D : Nat}
    (h : MilicevicDeepVarietyStructure D) : MilicevicDeepEventuallyPrime (milicevicBound D) :=
  fun _ hc => ⟨0, fun _ _ _ _ => h.at hc⟩

/-- **One greedy step.** A domain of size at least `θN²` contains a variety
piece with at least `exp(−B(θ)) N²` points. -/
theorem exists_variety_piece_at {Bnd : Real → Real}
    {N : Nat} [NeZero N] {θ : Real} (hM : DeepStructureAt Bnd N θ) {φ : ZMod N × ZMod N → ZMod N}
    {A : Finset (ZMod N × ZMod N)} (hA : IsEBihomomorphism A φ {0})
    (hsize : θ * (N : Real) ^ 2 ≤ A.card) :
    ∃ G : Finset (ZMod N × ZMod N), G ⊆ A ∧ IsVarietyPieceB Bnd θ φ G ∧
      Real.exp (-Bnd θ) * (N : Real) ^ 2 ≤ G.card := by
  obtain ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hagree⟩ := hM A φ hsize hA
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
theorem greedy_variety_cover_at {Bnd : Real → Real}
    {N : Nat} [NeZero N] {θ : Real} (hM : DeepStructureAt Bnd N θ) (hθ : 0 < θ) {φ : ZMod N × ZMod N → ZMod N}
    {A₀ : Finset (ZMod N × ZMod N)} (hA₀ : IsEBihomomorphism A₀ φ {0}) :
    ∃ (n : Nat) (G : Fin n → Finset (ZMod N × ZMod N)),
      (n : Real) ≤ Real.exp (Bnd θ) ∧
      ((A₀ \ Finset.univ.biUnion G).card : Real) < θ * (N : Real) ^ 2 ∧
      ∀ i, G i ⊆ A₀ ∧ IsVarietyPieceB Bnd θ φ (G i) := by
  set δ := Real.exp (-Bnd θ) with hδ
  have hδpos : 0 < δ := Real.exp_pos _
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : (0 : Real) < (N : Real) ^ 2 := by positivity
  -- strengthened statement: count times `δN²` is at most the domain size
  have key : ∀ m : Nat, ∀ A : Finset (ZMod N × ZMod N), A ⊆ A₀ → A.card ≤ m →
      ∃ (n : Nat) (G : Fin n → Finset (ZMod N × ZMod N)),
        (n : Real) * (δ * (N : Real) ^ 2) ≤ A.card ∧
        ((A \ Finset.univ.biUnion G).card : Real) < θ * (N : Real) ^ 2 ∧
        ∀ i, G i ⊆ A ∧ IsVarietyPieceB Bnd θ φ (G i) := by
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
          exists_variety_piece_at hM (hA₀.mono hAA₀) hsmall
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
  have hexp : Real.exp (Bnd θ) * δ = 1 := by
    rw [hδ, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hEpos : 0 < Real.exp (Bnd θ) := Real.exp_pos _
  nlinarith

/-- **Greedy covering of several bihomomorphisms.** Given Freiman
bihomomorphisms `φ_j` on domains `A_j` (`j < n`), at most `n·exp(B(θ/n))`
variety pieces, each inside the domain of its owner `j`, cover every
`A_j` outside a common exceptional set `U` with `|U| < θN²`. -/
theorem greedy_variety_cover_family_at {Bnd : Real → Real}
    {N : Nat} [NeZero N] {θ : Real} (hθ : 0 < θ) {n : Nat} (hn : 0 < n)
    (hM : DeepStructureAt Bnd N (θ / n))
    (φ : Fin n → ZMod N × ZMod N → ZMod N) (A : Fin n → Finset (ZMod N × ZMod N))
    (hA : ∀ j, IsEBihomomorphism (A j) (φ j) {0}) :
    ∃ (K : Nat) (piece : Fin K → Finset (ZMod N × ZMod N)) (owner : Fin K → Fin n)
      (U : Finset (ZMod N × ZMod N)),
      (K : Real) ≤ n * Real.exp (Bnd (θ / n)) ∧
      (U.card : Real) < θ * (N : Real) ^ 2 ∧
      (∀ k, piece k ⊆ A (owner k) ∧ IsVarietyPieceB Bnd (θ / n) (φ (owner k)) (piece k)) ∧
      ∀ j, ∀ x ∈ A j, x ∉ U → ∃ k, owner k = j ∧ x ∈ piece k := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hθn : 0 < θ / n := div_pos hθ hnR
  choose m G hm hrem hpieces using fun j => greedy_variety_cover_at hM hθn (hA j)
  let e := section5NatFlattenEquiv m
  refine ⟨∑ j, m j, fun k => G (e.symm k).1 (e.symm k).2, fun k => (e.symm k).1,
    Finset.univ.biUnion (fun j => A j \ Finset.univ.biUnion (G j)), ?_, ?_, ?_, ?_⟩
  · push_cast
    calc (∑ j, (m j : Real)) ≤ ∑ _j : Fin n, Real.exp (Bnd (θ / n)) :=
          Finset.sum_le_sum fun j _ => hm j
      _ = n * Real.exp (Bnd (θ / n)) := by
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

/-- **The covering clause of `StackableStructureAt 2`, by variety pieces.** -/
theorem variety_structure_side_eventually {Bnd : Real → Real} (hM : MilicevicDeepEventuallyPrime Bnd)
    {m : Real → Real → Nat} (hX : BihomExtraction m)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤ m gamma (theta / 2) *
              Real.exp (Bnd (theta / 2 / m gamma (theta / 2))) ∧
            (∀ k, IsVarietyPieceB Bnd (theta / 2 / m gamma (theta / 2)) (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) := by
  have ht2 : 0 < theta / 2 := by positivity
  obtain ⟨hmpos, N0, hN0⟩ := hX gamma (theta / 2) hg hg1 ht2 (by linarith)
  have hmR : (0 : Real) < m gamma (theta / 2) := by exact_mod_cast hmpos
  obtain ⟨N1, hN1⟩ := hM (theta / 2 / m gamma (theta / 2)) (div_pos ht2 hmR)
  refine ⟨max N0 N1, fun N _ _ hN Gamma hcard hprod => ?_⟩
  obtain ⟨J₀, hJ₀, φ, A, hA, hcover⟩ := hN0 N (le_of_max_le_left hN) Gamma hcard hprod
  obtain ⟨K, piece, owner, U, hK, hU, hpieces, hcov⟩ :=
    greedy_variety_cover_family_at ht2 hmpos (hN1 N (le_of_max_le_right hN)) φ A hA
  refine ⟨J₀ \ U.image pairPoint, ?_, K, piece, fun k => φ (owner k), hK,
    fun k => (hpieces k).2, ?_⟩
  · have h1 : J₀.card ≤ (J₀ \ U.image pairPoint).card + (U.image pairPoint).card :=
      Finset.card_le_card_sdiff_add_card
    have h2 : (U.image pairPoint).card ≤ U.card := Finset.card_image_le
    have h3 : (J₀.card : Real) ≤ (J₀ \ U.image pairPoint).card + U.card := by
      exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
    linarith
  · intro z hz
    obtain ⟨hzΓ, hzJ⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzJ₀, hzU⟩ := Finset.mem_sdiff.mp hzJ
    obtain ⟨j, hjA, hjφ⟩ := hcover z (Finset.mem_filter.mpr ⟨hzΓ, hzJ₀⟩)
    have hnotU : (z.1 0, z.1 1) ∉ U := by
      intro hU'
      apply hzU
      rw [← pairPoint_coords z.1]
      exact Finset.mem_image_of_mem _ hU'
    obtain ⟨k, hk, hkp⟩ := hcov j _ hjA hnotU
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨z.1, ?_, ?_⟩⟩
    · rw [← pairPoint_coords z.1]
      exact Finset.mem_image_of_mem _ hkp
    · show (z.1, φ (owner k) (z.1 0, z.1 1)) = z
      rw [hk, ← hjφ]

/-- **The covering half of `StackableStructureAt 2` from Milićević's
structure theorem alone.** -/
theorem structure_side_of_milicevic_eventually {Bnd : Real → Real} (hM : MilicevicDeepEventuallyPrime Bnd)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤
              bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2) *
              Real.exp (Bnd (theta / 2 /
                bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2))) ∧
            (∀ k, IsVarietyPieceB Bnd (theta / 2 /
              bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2))
              (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) :=
  variety_structure_side_eventually hM (bihomExtraction_of_densePiece densePiece_polynomial)
    gamma theta hg hg1 ht ht1

theorem structure_side_of_milicevic_sharper_eventually {Bnd : Real → Real}
    (hM : MilicevicDeepEventuallyPrime Bnd)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤
              bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2) *
              Real.exp (Bnd (theta / 2 /
                bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2))) ∧
            (∀ k, IsVarietyPieceB Bnd (theta / 2 /
              bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2))
              (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) :=
  variety_structure_side_eventually hM (bihomExtraction_of_densePiece densePiece_sharper)
    gamma theta hg hg1 ht ht1

/-- **The original statement from the prime, eventual contract.** -/
theorem structure_side_of_milicevic_of_eventually {D : Nat}
    (hM : MilicevicDeepEventuallyPrime (milicevicBound D))
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤
              bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2) *
              Real.exp (milicevicBound D (theta / 2 /
                bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2))) ∧
            (∀ k, IsVarietyPiece D (theta / 2 /
              bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2))
              (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) :=
  structure_side_of_milicevic_eventually hM gamma theta hg hg1 ht ht1

end LeanProofs.GowersSzemeredi
