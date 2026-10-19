import GowersSzemeredi.Proofs16WithLift

/-! The affine lift of Lemma 16.10 for a family of functions, on one
partition.

Step (B) of Notes L.3, the third stage. `Proofs16FamilyLemma6` makes the
line covers of all pieces share one partition. Here the lift from line
covers to multilinear covers is done for all members at once:
* every member `a` samples its own slices (`sample a`), but one cover of a
  relation containing all sampled slices of all members serves every
  member (in dimension one such a relation is a stacked Freiman family);
* the per-member sampling losses are `τ/|ι|`, so the common good set loses
  `2τ` in total;
* every member's candidate maps are interpolated on the same cells, and
  the candidate family of a cell is indexed by `ι × (candidates)`.

The synchronized retiling, compressed-cover, local, all-scale and global
producers are reexported from their earlier shared owners. Single-function
covers specialize those family producers; this module supplies family
line-count padding and the rounded global lift. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Line counts may be padded. -/
theorem Section16LineCoverFamily.mono_count {N k q q' : Nat} [NeZero N] {ι : Type}
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ}
    (hline : Section16LineCoverFamily P B phi σ l q) (hqq' : q ≤ q') :
    Section16LineCoverFamily P B phi σ l q' := by
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hpart, hproper, hproduct, hw, hell, hc⟩ := hline
  let ell' := fun a u h (i : Fin q') =>
    if hi : i.val < q then ell a u h ⟨i.val, hi⟩ else fun _ => 0
  refine ⟨E, M, S, T, J, ell', hE, hEm, hpart, hproper, hproduct, hw, ?_, ?_⟩
  · intro a u h i
    dsimp only [ell']
    split_ifs
    · exact hell _ _ _ _
    · exact ⟨0, 0, by simp⟩
  · intro a u h x hh hxB hxE hxS
    obtain ⟨i, hi⟩ := hc a u h x hh hxB hxE hxS
    refine ⟨⟨i.val, i.isLt.trans_le hqq'⟩, ?_⟩
    simpa only [ell', dif_pos i.isLt] using hi

/-- The rounded family lift: sample size `r = ⌈6·max(1,q)·max(1,|ι|)/τ⌉`. -/
theorem Section16LineCoverFamily.global_affine_lift_rounded_family {N k q : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Nat → Real → Real}
    (hline : Section16LineCoverFamily P B phi σ l q)
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Eb r) (Gs r sample))
    (hGs : ∀ r sample a h i, appendCoordinate h (sample a i) ∈ B a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Eb)
    (hk : 0 < k) (hl : 0 ≤ l) (τ ε : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let r := ⌈6 * (max 1 q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) / τ⌉₊
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ (Fintype.card ι : ℝ) * max (Pb r ε) ((r.choose 2 : ℝ) * Pb r ε * Pb r ε) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((⌊l⌋₊ : ℝ) / 8) ^ (Eb r ε)) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ a j z, z ∈ (Q j).carrier → z ∈ B a → z ∈ H → ∃ i, phi a z = mu j i z := by
  intro r
  have hr : 6 * ((max 1 q : Nat) : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) ≤ (r : ℝ) * τ := by
    rw [Nat.cast_max 1 q, Nat.cast_one, ← div_le_iff₀ hτ]
    exact Nat.le_ceil _
  obtain ⟨hPb, hEb, hEb1⟩ := hranges r ε (Nat.ceil_pos.mpr (by positivity)) hε hε1
  exact (hline.mono_count (le_max_right 1 q)).global_affine_lift_family (Gs r) (hslice r)
    (hGs r) hk (Nat.floor_le hl) τ ε (by omega) hτ hτ1 hε hε1 hPb hEb hEb1 hr

end LeanProofs.GowersSzemeredi
