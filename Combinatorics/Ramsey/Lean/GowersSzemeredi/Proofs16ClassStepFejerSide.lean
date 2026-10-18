import GowersSzemeredi.Proofs16ClassStepFejer
import GowersSzemeredi.Proofs16ClassPieceCoverSide

/-! Declarations of `Proofs16ClassStepFejer` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase
variable {k : Nat} {Thr : Real → Real → Real} {Cnt Exp : Real → Real → Nat → Real → Real}

/-- **Any `n` relations covered by step pieces have one cover.** -/
theorem class_step_cover_fejer {V : Real} {dC dE dT : Nat} (C : PowerUniformClass k V dC dE dT)
    (hk : 1 ≤ k) (hV : 1 ≤ V)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n : Nat}
    (Gamma : Fin n → Finset (Point N (k + 1) × ZMod N))
    (P : Fin n → Fin (classPiecesFejer gamma theta k) → StepPieceFejer C N theta gamma)
    (hP : ∀ i, Gamma i ⊆ stepPieceFejerGraphs C (P i)) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (classQr V dC k M tS gamma) (classPb V dC M tS gamma) M rho)
        ((3 ^ (k + 1) * M : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (classQb V dC M tS gS) (classEb V dE M tS gS)
            (classEr V dE k M tS gamma) rho *
          famPieceSliceExponent (classQr V dC k M tS gamma) (classEs V dE M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale A (classQb V dC M tS gS) (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent Bq (classQb V dC M tS gS) (classEb V dE M tS gS)
            (classEr V dE k M tS gamma) rho)
          (famPieceSliceExponent (classQr V dC k M tS gamma) (classEs V dE M tS gamma) M rho)))
      (Finset.univ.biUnion Gamma) := by
  intro M tS gS
  obtain ⟨htS, htS1⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨-, -, hgS, hgS1⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨hz, hzHalf⟩ := tightZeta_pos_le_half (fejerThetaOne_bounds k ht ht1 hg hg1).1 (by linarith [(fejerThetaOne_bounds k ht ht1 hg hg1).2])
  let R : Fin M → StepPieceFejer C N theta gamma := fun c =>
    P (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2
  have hfam := class_piece_family_cover hk hV C hA hB hlemma6 hz hzHalf htS htS1 hgS hgS1
    htS htS1 hg hg1 R
  refine MultiplyLinearWith.subset hfam ?_
  intro z hz'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz'
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hP i hi)
  refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.symm_apply_apply]
  exact hc

end

end LeanProofs.GowersSzemeredi
