import GowersSzemeredi.Proofs16ClassStep
import GowersSzemeredi.Proofs16IntegerClassPieceCover
import GowersSzemeredi.Proofs16ClassPiecesSide

/-! Uniform families of step pieces admit genuine integer covers.
The original controls and membership/decomposition records are preserved. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

variable {k : Nat} {Thr : Real → Real → Real} {Cnt Exp : Real → Real → Nat → Real → Real}

theorem integer_class_step_cover_gen (C : UniformClassWith k Thr Cnt Exp) (hC : C.IntegerCover) (hk : 1 ≤ k)
    (hCnt : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      1 ≤ Cnt theta gamma n s)
    (hExp : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      0 < Exp theta gamma n s ∧ Exp theta gamma n s ≤ 1)
    (hCntMono : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 ≤ s →
      Monotone fun n => Cnt theta gamma n s)
    (hExpAnti : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s →
      Antitone fun n => Exp theta gamma n s)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : IntegerAbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n : Nat}
    (Gamma : Fin n → Finset (Point N (k + 1) × ZMod N))
    (P : Fin n → Fin (classPieces gamma theta k) → StepPiece C N theta gamma)
    (hP : ∀ i, Gamma i ⊆ stepPieceGraphs C (P i)) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    IntegerMultiplyLinearWith
      (fun rho => max (famPieceGraphBound (clsQr Cnt k M tS gamma) (clsPb Cnt M tS gamma) M rho)
        ((3 ^ (k + 1) * M : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (Cnt tS gS M) (Exp tS gS M) (clsEr Exp k M tS gamma) rho *
          famPieceSliceExponent (clsQr Cnt k M tS gamma) (clsEs Exp M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale A (Cnt tS gS M) (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq (Cnt tS gS M) (Exp tS gS M) (clsEr Exp k M tS gamma) rho)
          (famPieceSliceExponent (clsQr Cnt k M tS gamma) (clsEs Exp M tS gamma) M rho)))
      (Finset.univ.biUnion Gamma) := by
  intro M tS gS
  classical
  obtain ⟨htS, htS1⟩ := classBudget_pos_le k ht ht1 hg hg1
  obtain ⟨-, -, hgS, hgS1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  let R : Fin M → StepPiece C N theta gamma := fun c =>
    P (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2
  have hfam := integer_class_piece_family_cover_gen hk C hC hCnt hExp hCntMono hExpAnti hA hB hlemma6 hz
    hzHalf htS htS1 hgS hgS1 htS htS1 hg hg1 R
  refine IntegerMultiplyLinearWith.mono hfam ?_
  intro z hz'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz'
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hP i hi)
  refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.symm_apply_apply]
  exact hc

theorem integer_class_step_cover {V : Real} {dC dE dT : Nat} (C : PowerUniformClass k V dC dE dT) (hC : C.IntegerCover)
    (hk : 1 ≤ k) (hV : 1 ≤ V)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : IntegerAbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n : Nat}
    (Gamma : Fin n → Finset (Point N (k + 1) × ZMod N))
    (P : Fin n → Fin (classPieces gamma theta k) → StepPiece C N theta gamma)
    (hP : ∀ i, Gamma i ⊆ stepPieceGraphs C (P i)) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    IntegerMultiplyLinearWith
      (fun rho => max (famPieceGraphBound (classQr V dC k M tS gamma) (classPb V dC M tS gamma) M rho)
        ((3 ^ (k + 1) * M : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (classQb V dC M tS gS) (classEb V dE M tS gS)
            (classEr V dE k M tS gamma) rho *
          famPieceSliceExponent (classQr V dC k M tS gamma) (classEs V dE M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale A (classQb V dC M tS gS) (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq (classQb V dC M tS gS) (classEb V dE M tS gS)
            (classEr V dE k M tS gamma) rho)
          (famPieceSliceExponent (classQr V dC k M tS gamma) (classEs V dE M tS gamma) M rho)))
      (Finset.univ.biUnion Gamma) := by
  intro M tS gS
  classical
  obtain ⟨htS, htS1⟩ := classBudget_pos_le k ht ht1 hg hg1
  obtain ⟨-, -, hgS, hgS1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  let R : Fin M → StepPiece C N theta gamma := fun c =>
    P (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2
  have hfam := integer_class_piece_family_cover hk hV C hC hA hB hlemma6 hz hzHalf htS htS1 hgS hgS1
    htS htS1 hg hg1 R
  refine IntegerMultiplyLinearWith.mono hfam ?_
  intro z hz'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz'
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hP i hi)
  refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.symm_apply_apply]
  exact hc

end LeanProofs.GowersSzemeredi
