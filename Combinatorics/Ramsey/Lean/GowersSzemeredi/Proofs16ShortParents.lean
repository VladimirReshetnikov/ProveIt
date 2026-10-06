import GowersSzemeredi.Proofs16BoundedChunks

/-! # Short parent boxes for final-axis compatibility

Localizing at floor(m/4) bounds every base axis by half the length of the
original final progression, and hence by half the modulus. The width loss
is at most a factor eight, including all rounding.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Integer rounding at a quarter scale loses at most a factor eight. -/
theorem quarter_scale_width {m : Nat} (hm : 4 ≤ m) :
    0 < m / 4 ∧ m ≤ 8 * (m / 4) ∧ 4 * (m / 4) ≤ m := by
  have hpos : 0 < m / 4 := Nat.div_pos hm (by norm_num)
  have hmod := Nat.mod_lt m (by norm_num : 0 < 4)
  have hdiv := Nat.div_add_mod m 4
  omega

/-- Preliminary localization provides the short containing progressions
needed for the signed final-axis tiling, at only a constant width cost. -/
theorem Box.short_parent_partition {N k m : Nat} [NeZero N]
    (P : Box N k) (I : ModAP N) (hP : P.IsProper) (hI : I.IsProper)
    (hk : 0 < k) (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧
      (∀ j, (Q j).IsProper ∧ (m : Real) / 8 ≤ (Q j).width) ∧
      (∀ j i, 0 < ((Q j).axis i).length ∧
        2 * ((Q j).axis i).length ≤ N ∧ ((Q j).axis i).length ≤ I.length) ∧
      ∀ j, (Q j).commonDiff = P.commonDiff := by
  obtain ⟨hr, hlower, hupper⟩ := quarter_scale_width hm
  obtain ⟨M, Q, hpart, hproper, haxes, hstep⟩ :=
    P.bounded_partition hP hk (m / 4) hr ((Nat.div_le_self _ _).trans hmP)
  have hIN : I.length ≤ N := by
    rw [← hI]
    simpa using Finset.card_le_univ I.carrier
  refine ⟨M, Q, hpart, ?_, ?_, hstep⟩
  · intro j
    refine ⟨(hproper j).1, ?_⟩
    have h : m ≤ 8 * (Q j).width := hlower.trans (Nat.mul_le_mul_left 8 (hproper j).2)
    have h' : (m : Real) ≤ 8 * ((Q j).width : Real) := by exact_mod_cast h
    linarith
  · intro j i
    have h := haxes j i
    omega

end LeanProofs.GowersSzemeredi
