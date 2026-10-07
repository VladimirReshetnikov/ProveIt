import GowersSzemeredi.Proofs16GlobalAffineLift

/-! # Canonical integer parameters for the global affine lift -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Padding affine fibre covers preserves the entire line-cover witness,
including its partition, exceptional set, and width. -/
theorem Section16LineCover.mono_count {N k q q' : Nat} [NeZero N]
    {P : Box N (k + 1)} {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {σ l : ℝ}
    (hline : Section16LineCover P B phi σ l q) (hqq' : q ≤ q') :
    Section16LineCover P B phi σ l q' := by
  classical
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hpart, hproper, hproduct, hw, hell, hc⟩ := hline
  let ell' := fun u h (i : Fin q') =>
    if hi : i.val < q then ell u h ⟨i.val, hi⟩ else fun _ => 0
  refine ⟨E, M, S, T, J, ell', hE, hEm, hpart, hproper, hproduct, hw, ?_, ?_⟩
  · intro u h i
    dsimp only [ell']
    split_ifs
    · exact hell _ _ _
    · exact ⟨0, 0, by simp⟩
  · intro u h x hh hxB hxE hxS
    obtain ⟨i, hi⟩ := hc u h x hh hxB hxE hxS
    refine ⟨⟨i.val, i.isLt.trans_le hqq'⟩, ?_⟩
    simpa only [ell', dif_pos i.isLt] using hi

/-- Choose a positive padded fibre count, the natural ceiling sample
budget, and the natural floor of the cell-width lower bound. This removes
all auxiliary integer choices from the global lifting construction. -/
theorem Section16LineCover.global_affine_lift_rounded {N k q : Nat} [Fact N.Prime]
    {P : Box N (k + 1)} {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {σ l gamma s : ℝ}
    (hline : Section16LineCover P B phi σ l q)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hk : 0 < k) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s)
    (hl : 0 ≤ l) (τ ε : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let r := ⌈6 * (max 1 q : ℝ) / τ⌉₊
    let b := (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s)
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ max b ((r.choose 2 : ℝ) * b * b) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((⌊l⌋₊ : ℝ) / 8) ^
        ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  let q' := max 1 q
  let r := ⌈6 * (q' : ℝ) / τ⌉₊
  have hq' : 0 < q' := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hr : 6 * (q' : ℝ) ≤ (r : ℝ) * τ :=
    (div_le_iff₀ hτ).mp (Nat.le_ceil _)
  have hpad := hline.mono_count (le_max_right 1 q)
  simpa only [q', r, Nat.cast_max, Nat.cast_one] using
    hpad.global_affine_lift hsections hk hg hg1 hs (Nat.floor_le hl)
      τ ε hq' hτ hτ1 hε hε1 hr

end LeanProofs.GowersSzemeredi
