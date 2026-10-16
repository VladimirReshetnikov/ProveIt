import GowersSzemeredi.Proofs16JointSliceCell
import GowersSzemeredi.Proofs16SinglePieceCoverGlobal
import GowersSzemeredi.Proofs16TightRadius

/-! **The single-piece lift with joint vertex covers and joint slices**
(Notes L.16q).

`single_piece_lift_global_cover_with_joint` is the lift
`single_piece_lift_global_cover_scheme` at `jointSliceScheme`: the two anchor
slices are covered jointly, and the slice covers are translated as covers
(`MultiplyLinearWith.translate_graph`) instead of being turned into providers.
Density `jointSliceDensity (Qb k γ θ′) ρ 1` (one class degree) in place of
`θ₁·c(c(θ₁))` (two); width `jointSliceWidth (Eb k γ θ′) ρ 1 L`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **The single-piece lift from global-to-local covers, with the remainder
from the jointly composed vertex covers.** -/
theorem single_piece_lift_global_cover_with_joint {k : Nat} (hk : 1 ≤ k) {t1 zeta gamma : Real}
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
      2 ≤ jointSliceWidth (Eb k gamma (globalBudgetW t1 k)) (spectrumPieceRho (fun t => t / 2) (coverRho1W Qb t1 gamma k)) 1 ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊) :
    ∃ q : Nat, (q : Real) ≤ Qb k (section16Delta (t1))
        (globalBudgetW t1 k)
        (coverRho1W Qb t1 gamma k / 2 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (jointSliceWidth (Eb k gamma (globalBudgetW t1 k)) (spectrumPieceRho (fun t => t / 2) (coverRho1W Qb t1 gamma k)) 1 ⌈spectrumCellWidth (zeta) m (eps q) / 8⌉₊ - 1) - 1 ≤
          S.width ∧
        jointSliceDensity (Qb k gamma (globalBudgetW t1 k))
            (spectrumPieceRho (fun t => t / 2)
              (coverRho1W Qb t1 gamma k)) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card :=
  single_piece_lift_global_cover_scheme hk ha0 haS hzeta hz0 hz2 hg hg1 hcov hQb hEb hEb1 eps thr hretile
    (jointSliceScheme (Qb k gamma (globalBudgetW t1 k)) (Eb k gamma (globalBudgetW t1 k))
      (hQb k gamma _) fun t ht ht1 => (hEb k gamma _ t ht ht1).le)
    (fun _ _ _ t h => by rw [restrictRelation_partialGraph] at h; exact h.translate_graph t) B phi hB hprodB hL4 m hm1 hm hpar

end LeanProofs.GowersSzemeredi
