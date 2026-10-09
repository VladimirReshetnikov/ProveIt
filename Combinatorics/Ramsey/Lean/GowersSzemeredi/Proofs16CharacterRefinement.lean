import GowersSzemeredi.Proofs16SeparatingFrequencies
import GowersSzemeredi.Proofs16BoundedSpanPhase

/-! Deterministic character refinement: the combinatorial core of
Milićević's Proposition 8.1 (arXiv:2601.01682, printed pp. 61–62).

Milićević makes alternating sums of Freiman-linear maps vanish *without
shrinking the index set*. When every sum takes at most `K` values, he
refines each domain by `m = O(log K)` random characters. Here the random
choice is replaced by averaging over all `N^m` character tuples.
* `nonseparating_tuples_card_le`: for `h ≠ 0` and prime `N ≥ 7`, at most
  `(N/2)^m` tuples `χ : Fin m → ZMod N` have no entry separating `h`
  (`Separates`, from `Proofs16SeparatingFrequencies`).
* `exists_characters_few_survivors`: given finite value sets `A q` of size
  at most `K`, some tuple leaves a nonzero value unseparated in at most a
  `K/2^m` fraction of the indices `q`.
* `characterRefinement χ n B f`: the points of `B` where every `χ i`
  sees `f` within `N/(5n)` of zero.
* `not_separates_signed_sum`: on the common refinement, a signed sum of
  `n` such values is not separated by any `χ i`.
* `exists_character_refinement`: if each signed sum
  `∑ j, s j * f q j y` (signs `±1`) takes at most `K` values on the common
  domain `⋂ j, B q j`, then some `m` characters make it vanish identically
  on the refined domains for all but a `K/2^m` fraction of `q`.

The containment of large Bohr sets in the refined domains (Milićević's
Proposition 2.37) is a separate step and is not proved here.

In `ℤ/N` with `N` prime neither step is needed: `freiman_small_image_zero`
makes a normalized Freiman-linear map with at most `K < N` values vanish on
`B(T;ρ/K)` directly. This module is the group-agnostic version of the
argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **Few character tuples miss a nonzero value.** -/
theorem nonseparating_tuples_card_le {N : Nat} [NeZero N] [Fact N.Prime] (h7 : 7 ≤ N)
    {h : ZMod N} (hh : h ≠ 0) (m : Nat) :
    2 ^ m * (Finset.univ.filter fun χ : Fin m → ZMod N => ∀ i, ¬ Separates (χ i) h).card ≤
      N ^ m := by
  have heq : (Finset.univ.filter fun χ : Fin m → ZMod N => ∀ i, ¬ Separates (χ i) h) =
      Fintype.piFinset fun _ : Fin m => Finset.univ.filter fun γ : ZMod N => ¬ Separates γ h := by
    ext χ
    simp [Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← mul_pow]
  exact Nat.pow_le_pow_left (small_multiples_card_le h7 hh) m

/-- **A character tuple with few survivors.** -/
theorem exists_characters_few_survivors {N : Nat} [NeZero N] [Fact N.Prime] (h7 : 7 ≤ N)
    {ι : Type*} (Q : Finset ι) (A : ι → Finset (ZMod N)) {K : Nat}
    (hK : ∀ q ∈ Q, (A q).card ≤ K) (m : Nat) :
    ∃ χ : Fin m → ZMod N, 2 ^ m * (Q.filter fun q =>
      ∃ h ∈ A q, h ≠ 0 ∧ ∀ i, ¬ Separates (χ i) h).card ≤ K * Q.card := by
  let bad : (Fin m → ZMod N) → ι → Prop := fun χ q =>
    ∃ h ∈ A q, h ≠ 0 ∧ ∀ i, ¬ Separates (χ i) h
  have h1 : ∑ χ : Fin m → ZMod N, (Q.filter (bad χ)).card =
      ∑ q ∈ Q, (Finset.univ.filter fun χ => bad χ q).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∀ q ∈ Q, 2 ^ m * (Finset.univ.filter fun χ => bad χ q).card ≤ K * N ^ m := by
    intro q hq
    have hsub : (Finset.univ.filter fun χ => bad χ q) ⊆
        ((A q).filter (· ≠ 0)).biUnion fun h =>
          Finset.univ.filter fun χ : Fin m → ZMod N => ∀ i, ¬ Separates (χ i) h := by
      intro χ hχ
      obtain ⟨h, hA, hne, hall⟩ := (Finset.mem_filter.mp hχ).2
      exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr ⟨hA, hne⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩
    calc 2 ^ m * (Finset.univ.filter fun χ => bad χ q).card
        ≤ 2 ^ m * ∑ h ∈ (A q).filter (· ≠ 0),
            (Finset.univ.filter fun χ : Fin m → ZMod N => ∀ i, ¬ Separates (χ i) h).card :=
          Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ h ∈ (A q).filter (· ≠ 0),
            2 ^ m * (Finset.univ.filter fun χ : Fin m → ZMod N =>
              ∀ i, ¬ Separates (χ i) h).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _h ∈ (A q).filter (· ≠ 0), N ^ m :=
          Finset.sum_le_sum fun h hh => nonseparating_tuples_card_le h7 (Finset.mem_filter.mp hh).2 m
      _ = ((A q).filter (· ≠ 0)).card * N ^ m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ K * N ^ m := Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (hK q hq))
  have hsum : ∑ χ : Fin m → ZMod N, 2 ^ m * (Q.filter (bad χ)).card ≤
      ∑ _χ : Fin m → ZMod N, K * Q.card := by
    calc ∑ χ : Fin m → ZMod N, 2 ^ m * (Q.filter (bad χ)).card
        = 2 ^ m * ∑ χ : Fin m → ZMod N, (Q.filter (bad χ)).card := (Finset.mul_sum _ _ _).symm
      _ = 2 ^ m * ∑ q ∈ Q, (Finset.univ.filter fun χ => bad χ q).card := by rw [h1]
      _ = ∑ q ∈ Q, 2 ^ m * (Finset.univ.filter fun χ => bad χ q).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _q ∈ Q, K * N ^ m := Finset.sum_le_sum h2
      _ = ∑ _χ : Fin m → ZMod N, K * Q.card := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
          Fintype.card_fin, smul_eq_mul, smul_eq_mul]
        ring
  obtain ⟨χ, -, hχ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨χ, hχ⟩

/-- The points of `B` at which every `χ i` sees `f` within `N/(5n)` of zero. -/
def characterRefinement {N : Nat} [NeZero N] {m : Nat} (χ : Fin m → ZMod N) (n : Nat)
    (B : Finset (ZMod N)) (f : ZMod N → ZMod N) : Finset (ZMod N) :=
  B.filter fun y => ∀ i, 5 * n * centeredAbs (χ i * f y) < N

theorem characterRefinement_subset {N : Nat} [NeZero N] {m : Nat} (χ : Fin m → ZMod N)
    (n : Nat) (B : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    characterRefinement χ n B f ⊆ B :=
  Finset.filter_subset _ _

theorem centeredAbs_mul_sign {N : Nat} {s : ZMod N} (hs : s = 1 ∨ s = -1) (x : ZMod N) :
    centeredAbs (s * x) = centeredAbs x := by
  rcases hs with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul]
    exact ZMod.natAbs_valMinAbs_neg x

/-- **On the common refinement, no chosen character separates a signed sum.** -/
theorem not_separates_signed_sum {N : Nat} [NeZero N] {m n : Nat} (χ : Fin m → ZMod N)
    (s : Fin n → ZMod N) (hs : ∀ j, s j = 1 ∨ s j = -1)
    (B : Fin n → Finset (ZMod N)) (f : Fin n → ZMod N → ZMod N) {y : ZMod N}
    (hy : ∀ j, y ∈ characterRefinement χ n (B j) (f j)) (i : Fin m) :
    ¬ Separates (χ i) (∑ j, s j * f j y) := by
  have hc : ∀ j, 5 * n * centeredAbs (χ i * f j y) < N := fun j =>
    (Finset.mem_filter.mp (hy j)).2 i
  have hsum : centeredAbs (χ i * ∑ j, s j * f j y) ≤ ∑ j, centeredAbs (χ i * f j y) := by
    rw [Finset.mul_sum]
    refine (centeredAbs_sum_le_sum _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [show χ i * (s j * f j y) = s j * (χ i * f j y) by ring]
    exact centeredAbs_mul_sign (hs j) _
  have hbound : n * (5 * ∑ j, centeredAbs (χ i * f j y)) ≤ n * N := by
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ j, n * (5 * centeredAbs (χ i * f j y)) ≤ ∑ _j : Fin n, N :=
          Finset.sum_le_sum fun j _ => by
            rw [show n * (5 * centeredAbs (χ i * f j y)) = 5 * n * centeredAbs (χ i * f j y) by
              ring]
            exact (hc j).le
      _ = n * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold Separates
  rw [not_lt]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [centeredAbs]
  · have h5 : 5 * ∑ j, centeredAbs (χ i * f j y) ≤ N := Nat.le_of_mul_le_mul_left hbound hn
    calc 5 * centeredAbs (χ i * ∑ j, s j * f j y) ≤ 5 * ∑ j, centeredAbs (χ i * f j y) :=
          Nat.mul_le_mul_left _ hsum
      _ ≤ N := h5

/-- **Deterministic character refinement (Milićević, Proposition 8.1, core).**
If each signed sum takes at most `K` values on its common domain, some `m`
characters make it vanish identically on the refined domains for all but a
`K/2^m` fraction of the indices. The index set `Q` itself is not shrunk. -/
theorem exists_character_refinement {N : Nat} [NeZero N] [Fact N.Prime] (h7 : 7 ≤ N)
    {ι : Type*} (Q : Finset ι) {n : Nat} (s : Fin n → ZMod N) (hs : ∀ j, s j = 1 ∨ s j = -1)
    (B : ι → Fin n → Finset (ZMod N)) (f : ι → Fin n → ZMod N → ZMod N) {K : Nat}
    (hK : ∀ q ∈ Q, ((Finset.univ.filter fun y => ∀ j, y ∈ B q j).image
        fun y => ∑ j, s j * f q j y).card ≤ K) (m : Nat) :
    ∃ χ : Fin m → ZMod N, 2 ^ m * (Q.filter fun q => ∃ y,
      (∀ j, y ∈ characterRefinement χ n (B q j) (f q j)) ∧ ∑ j, s j * f q j y ≠ 0).card ≤
        K * Q.card := by
  obtain ⟨χ, hχ⟩ := exists_characters_few_survivors h7 Q
    (fun q => (Finset.univ.filter fun y => ∀ j, y ∈ B q j).image fun y => ∑ j, s j * f q j y)
    hK m
  refine ⟨χ, le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_)) hχ⟩
  intro q hq
  obtain ⟨hqQ, y, hy, hne⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hqQ, ∑ j, s j * f q j y, ?_, hne, fun i =>
    not_separates_signed_sum χ s hs (B q) (f q) hy i⟩
  exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j =>
    characterRefinement_subset χ n (B q j) (f q j) (hy j)⟩, rfl⟩

end LeanProofs.GowersSzemeredi
