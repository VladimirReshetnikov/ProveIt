import GowersSzemeredi.Proofs16SinglePieceCoverGlobal
import GowersSzemeredi.Proofs16SinglePieceGlobalSide

/-! Declarations of `Proofs16SinglePieceCoverGlobal` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Classical

/-- **The single-piece lift from global-to-local covers, with the remainder
from the jointly composed vertex covers.** -/
theorem single_piece_lift_global_cover_with {k : Nat} (hk : 1 ≤ k) {t1 zeta gamma : Real}
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hz0 : 0 < zeta) (hz2 : zeta ≤ 1 / 2) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    (hEb1 : ∀ l g t s, 0 < s → s ≤ 1 → Eb l g t s ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma)
    (hL4 : 4 ≤ coverRemWidthW Eb t1 gamma k N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ coverWidth (Eb k (section16Delta (t1))
        (globalBudgetW t1 k))
      (coverRho1W Qb t1 gamma k / 2)
      ⌈(coverRemWidthW Eb t1 gamma k N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qb k (section16Delta (t1))
        (globalBudgetW t1 k)
        (coverRho1W Qb t1 gamma k / 2 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth (zeta) m (eps q) ∧
      2 ≤ spectrumPieceRho (fun t => t / 2)
          (coverRho1W Qb t1 gamma k) ^ 3 *
        spectrumCellWidth (zeta) m (eps q) ∧
      2 ≤ coverWidth (Eb k gamma (globalBudgetW t1 k))
          ((fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (coverRho1W Qb t1 gamma k)) 1))
        (coverWidth (Eb k gamma (globalBudgetW t1 k))
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (coverRho1W Qb t1 gamma k)) 1)
          ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qb k (section16Delta (t1))
        (globalBudgetW t1 k)
        (coverRho1W Qb t1 gamma k / 2 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (coverWidth (Eb k gamma (globalBudgetW t1 k))
          ((fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (coverRho1W Qb t1 gamma k)) 1))
          (coverWidth (Eb k gamma (globalBudgetW t1 k))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (coverRho1W Qb t1 gamma k)) 1)
            ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊) - 1) - 1 ≤
          S.width ∧
        singlePieceDensity (fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))
            (spectrumPieceRho (fun t => t / 2)
              (coverRho1W Qb t1 gamma k)) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  have hc : ∀ s : Real, 0 < s → s ≤ 1 → 0 < s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2) ∧
      s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2) ≤ 1 := by
    intro s hs hs1
    have hq := hQb k gamma (globalBudgetW t1 k) (s / 2) (by positivity) (by linarith)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  exact single_piece_lift_global_cover_scheme hk ha0 haS hzeta hz0 hz2 hg hg1 hcov hQb hEb hEb1 eps thr hretile
    (localPieceScheme (fun s => s / 2 / Qb k gamma (globalBudgetW t1 k) (s / 2))
      (coverWidth (Eb k gamma (globalBudgetW t1 k))) hc (coverWidth_mono _))
    (fun _ _ _ t h => (h.localPieceFor (hQb k gamma _) (hEb k gamma _)).translate t) B phi hB hprodB hL4 m hm1 hm hpar

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open Classical

theorem globalTheta2_pos_le (theta gamma : Real) (k : Nat) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < globalTheta2 theta gamma k ∧ globalTheta2 theta gamma k ≤ 1 := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le k ht ht1 hg hg1
  exact ⟨by rw [globalTheta2]; positivity, by rw [globalTheta2]; linarith⟩

theorem coverPrec_pos_le (theta gamma : Real) (k : Nat) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < coverPrec theta gamma k ∧ coverPrec theta gamma k ≤ 1 := by
  obtain ⟨h0, h1⟩ := globalTheta2_pos_le theta gamma k ht ht1 hg hg1
  have h2 : (1 : Real) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  refine ⟨by unfold coverPrec; positivity, ?_⟩
  unfold coverPrec
  rw [div_le_one (by positivity)]
  linarith

theorem coverRho1_pos_le (Qb : Nat → Real → Real → Real → Real)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (theta gamma : Real) (k : Nat) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < coverRho1 Qb theta gamma k ∧ coverRho1 Qb theta gamma k ≤ 1 := by
  obtain ⟨h0, h1⟩ := globalTheta2_pos_le theta gamma k ht ht1 hg hg1
  have hc := one_le_coverCount Qb theta gamma k
  have hc0 := coverCount_pos Qb hQb theta gamma k
  unfold coverRho1
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hc0]
  linarith

/-- **The single-piece lift from global-to-local covers, with the remainder
from the jointly composed vertex covers.** -/
theorem single_piece_lift_global_cover {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    (hEb1 : ∀ l g t s, 0 < s → s ≤ 1 → Eb l g t s ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma)
    (hL4 : 4 ≤ coverRemWidth Eb theta gamma k N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ coverWidth (Eb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k))
      (coverRho1 Qb theta gamma k / 2)
      ⌈(coverRemWidth Eb theta gamma k N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k)
        (coverRho1 Qb theta gamma k / 2 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ spectrumPieceRho (fun t => t / 2)
          (coverRho1 Qb theta gamma k) ^ 3 *
        spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ coverWidth (Eb k gamma (globalBudget theta gamma k))
          ((fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (coverRho1 Qb theta gamma k)) 1))
        (coverWidth (Eb k gamma (globalBudget theta gamma k))
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (coverRho1 Qb theta gamma k)) 1)
          ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k)
        (coverRho1 Qb theta gamma k / 2 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (coverWidth (Eb k gamma (globalBudget theta gamma k))
          ((fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (coverRho1 Qb theta gamma k)) 1))
          (coverWidth (Eb k gamma (globalBudget theta gamma k))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (coverRho1 Qb theta gamma k)) 1)
            ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊) - 1) - 1 ≤
          S.width ∧
        singlePieceDensity (fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (spectrumPieceRho (fun t => t / 2)
              (coverRho1 Qb theta gamma k)) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card :=
  have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1
  have hz := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1
  single_piece_lift_global_cover_with hk hp.1 hp.2.1 hp.2.2 hz.1 (by linarith [hz.2]) hg hg1
    hcov hQb hEb hEb1 eps thr hretile B phi hB hprodB hL4 m hm1 hm hpar

end

end LeanProofs.GowersSzemeredi
