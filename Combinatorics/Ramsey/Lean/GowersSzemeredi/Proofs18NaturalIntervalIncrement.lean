import GowersSzemeredi.Proofs18AffineTransfer
import GowersSzemeredi.Proofs18IntervalBoundarySelection

/-! Exact transport of a proper modular progression in a short interval to
a natural-number progression, preserving both its carrier and density.

`natural_interval_quadratic_density_increment` is in
`Proofs18NaturalIntervalIncrementSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Positive step already implies properness over the natural numbers. -/
theorem NatAP.isProper_of_step_pos (P : NatAP) (hstep : 0 < P.step) : P.IsProper := by
  refine ⟨hstep, ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext ((Nat.mul_right_cancel hstep) (Nat.add_left_cancel hij))

/-- A proper progression contained in a short interval lifts, after possibly
reversing its orientation, to exactly the same set of natural representatives. -/
theorem ModAP.exists_natAP_of_short_interval {N L : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hsize : 2 * L < N)
    (hsub : P.carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L))) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.length = P.length ∧
      Q.carrier = P.carrier.image ZMod.val ∧ Q.carrier ⊆ Finset.range L := by
  let S := P.carrier.image ZMod.val
  have hS : S.card = P.length := by
    rw [Finset.card_image_of_injective _ (ZMod.val_injective N)]
    exact hP
  have hindex (i : Nat) (hi : i < P.length) : P.index i ∈ P.carrier :=
    Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hAP : HasNatAP S P.length := by
    by_cases htwo : 2 ≤ P.length
    · have hd : P.step ≠ 0 := by
        intro hd
        have heq : P.index 0 = P.index 1 := by simp [ModAP.index, hd]
        have := P.index_injOn hP (by simp; omega) (by simp; omega) heq
        omega
      apply hasNatAP_of_short_modular_sequence S (fun i => (P.index i).val)
        P.start P.step hd hsize
      intro i hi
      refine ⟨Finset.mem_image.mpr ⟨P.index i, hindex i hi, rfl⟩, ?_, ?_⟩
      · have := (mem_finiteIntervalSupport (by omega : L ≤ N) _).mp (hsub (hindex i hi))
        omega
      · exact ZMod.natCast_zmod_val _
    · by_cases hzero : P.length = 0
      · exact ⟨0, 1, by omega, by omega⟩
      · refine ⟨(P.index 0).val, 1, by omega, ?_⟩
        intro i hi
        have : i = 0 := by omega
        subst i
        simpa only [Nat.zero_mul, Nat.add_zero] using (Finset.mem_image.mpr ⟨P.index 0, hindex 0 (by omega), rfl⟩ :
          (P.index 0).val ∈ S)
  obtain ⟨a, d, hd, hAP⟩ := hAP
  let Q : NatAP := ⟨a, d, P.length⟩
  have hQ : Q.IsProper := Q.isProper_of_step_pos hd
  have hQS : Q.carrier ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hAP i i.isLt
  have heq : Q.carrier = S := Finset.eq_of_subset_of_card_le hQS (by rw [hS, hQ.2])
  refine ⟨Q, hQ, rfl, heq, ?_⟩
  rw [heq]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr ((mem_finiteIntervalSupport (by omega : L ≤ N) y).mp (hsub hy))

/-- Natural representatives recover the original finite interval set. -/
theorem finiteIntervalImage_val {N L : Nat} [NeZero N] (hL : L ≤ N)
    (B : Finset (Fin L)) :
    (finiteIntervalImage N B).image ZMod.val = B.image Fin.val := by
  unfold finiteIntervalImage
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact ZMod.val_natCast_of_lt (i.isLt.trans_le hL)

/-- Replacing a modular progression by its exact natural representative set
preserves every intersection cardinality. -/
theorem card_inter_natAP_of_carrier_eq {N : Nat} [NeZero N]
    (P : ModAP N) (Q : NatAP) (hQ : Q.carrier = P.carrier.image ZMod.val)
    (A : Finset (ZMod N)) :
    (A.image ZMod.val ∩ Q.carrier).card = (A ∩ P.carrier).card := by
  rw [hQ, ← Finset.image_inter _ _ (ZMod.val_injective N),
    Finset.card_image_of_injective _ (ZMod.val_injective N)]

end LeanProofs.GowersSzemeredi
