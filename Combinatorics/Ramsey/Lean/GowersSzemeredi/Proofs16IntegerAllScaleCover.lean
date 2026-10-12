import GowersSzemeredi.Proofs16AllScaleCoverTransfer
import GowersSzemeredi.Proofs16IntegerBaseCover

/-! Genuine sufficiently-wide box covers extend to all integer boxes.
The same capped exponent and exact coarse graph budget are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def IntegerLargeBoxMultilinearCover {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (rho C e T : Real) : Prop :=
  ∀ P : Box N k, P.HasIntegerRepresentatives → T ≤ (P.width : Real) →
    ∃ M q : Nat, ∃ H : Finset (Point N k), ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin q → Point N k → ZMod N,
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧ (q : Real) ≤ C ∧
        (∀ j, (P.width : Real) ^ e ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
          (x, y) ∈ Gamma → ∃ i, y = mu j i x

theorem integerMultiplyLinearWith_of_large_box_covers {N k : Nat} [NeZero N]
    (hk : 0 < k) {Gamma : Finset (Point N k × ZMod N)}
    (M : Nat) (hfib : ∀ x : Point N k, (Gamma.filter fun z => z.1 = x).card ≤ M)
    (Q E T : Real → Real)
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s)
    (hcover : ∀ s, 0 < s → s ≤ 1 → IntegerLargeBoxMultilinearCover Gamma s (Q s) (E s) (T s)) :
    IntegerMultiplyLinearWith
      (fun s => max (Q s) ((3 ^ k * M : Nat) : Real))
      (fun s => section16CappedWidthExponent (E s) (T s)) Gamma := by
  apply IntegerMultiplyLinearWith.of_ascending
  intro s hs hs1 P hP
  have he := hE s hs hs1
  have hc := section16CappedWidthExponent_pos (T := T s) he
  by_cases hlarge : T s ≤ (P.width : Real)
  · obtain ⟨L, q, H, R, mu, hH, hmass, hpart, hproper, hq, hw, hmu, hcov⟩ :=
      hcover s hs hs1 P hP.toGenuine hlarge
    refine ⟨L, q, H, R, mu, hH, hmass, hpart, hproper,
      hq.trans (le_max_left _ _), ?_, hmu, hcov⟩
    intro j
    by_cases hz : P.width = 0
    · simp only [hz, Nat.cast_zero, Real.zero_rpow hc.ne']
      exact Nat.cast_nonneg _
    · have hW : (1 : Real) ≤ P.width := by exact_mod_cast (show 1 ≤ P.width by omega)
      exact (Real.rpow_le_rpow_of_exponent_le hW (min_le_left _ _)).trans (hw j)
  · have hsmall := section16CappedWidthExponent_small (W := P.width) he (lt_of_not_ge hlarge).le
    obtain ⟨L, R, mu, hpart, hproper, hw, hmu, hcov⟩ :=
      section16_integer_coarse_relation_cover hk Gamma M hfib P hP
    refine ⟨L, 3 ^ k * M, P.carrier, R, mu, Finset.Subset.refl _, ?_,
      hpart, hproper, le_max_right _ _, ?_, hmu, fun j x hx _ y hy => hcov j x hx y hy⟩
    · nlinarith [mul_nonneg hs.le (Nat.cast_nonneg P.carrier.card : (0 : Real) ≤ P.carrier.card)]
    · intro j
      have hmin : (P.width : Real) ^ section16CappedWidthExponent (E s) (T s) ≤
          ((min 2 P.width : Nat) : Real) := by
        rcases Nat.lt_or_ge P.width 2 with hlt | hge
        · rw [min_eq_right hlt.le]
          interval_cases h : P.width
          · simp [Real.zero_rpow hc.ne']
          · simp
        · rw [min_eq_left hge]
          exact_mod_cast hsmall
      exact hmin.trans (by exact_mod_cast hw j)

end LeanProofs.GowersSzemeredi
