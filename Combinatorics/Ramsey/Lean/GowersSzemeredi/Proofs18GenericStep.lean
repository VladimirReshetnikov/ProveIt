import GowersSzemeredi.Proofs18GenericModulus
import GowersSzemeredi.Proofs18UniformCoversSide

/-! The single-piece inverse step in any dimension (Notes L.7a, F3b).

`GenParams.inverse_step` is `single_piece_inverse_step_global` at
dimension `k`, with every input supplied except the lower-degree bound and
the lift inequality `hlift`:
* the covers from `UniformCovers k V D`;
* the lift controls `GenParams.C`, `GenParams.W` (`genC`, `genW`);
* the retiled linearity bound in dimension `k`, from the recurrence profile;
* the scale conditions above `GenParams.Tloc` (`GenParams.modulus_conditions`).

A degree-`(k+1)` discrepancy bound at parameter `GenParams.yIn` gives a
degree-`(k+2)` bound at parameter `α`. The lift inequality `hlift` follows
from `genC_le` once the base density is a reciprocal power. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

namespace GenParams

variable (P : GenParams) (alpha : Real)

/-- The localization parameter `η` of the step. -/
def eta : Real := singlePieceEta (fun _ => uCount P.V P.D) (P.C alpha) alpha P.k

/-- The parameter of the lower-degree bound. -/
def yIn : Real := (P.eta alpha / 2) / (2 * (P.k + 1 + 2 : Nat) : Real) ^ (P.k + 1 + 2)

/-- **The single-piece inverse step in dimension `k`.** -/
theorem inverse_step (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) (hk : 1 ≤ P.k)
    (hcov : UniformCovers P.k P.V P.D)
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (hlift : ∀ j, 1 ≤ j → j ≤ P.k → ∀ t, P.C alpha t ≤ (liftLastC^[j] (P.baseC alpha)) t)
    {beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound (P.k + 1) (P.yIn alpha) beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16) :
    FunctionDiscrepancyBound (P.k + 2) alpha (P.eta alpha * beta / 4)
      (inverseStepExponent (P.k + 1) (P.Eloc alpha) sigma)
      (max (shortLocalizationThreshold (P.k + 1) (P.Eloc alpha) (6 * ((P.k + 1 : Nat) : Real)) T
          (P.Tloc alpha))
        (inverseStepThreshold (P.k + 1) (P.eta alpha) beta (P.Eloc alpha)
          (6 * ((P.k + 1 : Nat) : Real)) sigma)) := by
  obtain ⟨⟨hB0, hB1⟩, -, -, -, -, -, -, -, -, -, -, -, -, hEw, hC⟩ := P.ranges hV hp ha haHalf
  obtain ⟨he0, he, -⟩ := P.Eloc_pos_le hV hp ha haHalf
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => (hrec.retiled_family (fun q => familyRecThr_pos (by omega) q) q).single
  refine single_piece_inverse_step_global (Qb := fun _ => uCount P.V P.D)
    (Eb := fun _ => uExp P.V P.D) (C := P.C alpha) (W := P.W alpha) hk ha haHalf
    (fun l hl1 hlk => hcov l hl1 hlk)
    (fun _ g t s _ _ => one_le_uCount P.V P.D g t s)
    (fun _ g t s _ _ => (uExp_pos_le P.V P.D g t s).1)
    hC (genW_mono hEw P.k) ?_ ?_ (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p) hretile
    he0 he hbound hb hs hs16 (fun N _ _ hN => P.modulus_conditions hV hK hp ha haHalf N hN)
  · intro l hl1 hlk t
    exact hlift (P.k + 1 - l) (by omega) (by omega) t
  · intro l _ _ t L
    exact genW_le hEw (uExp_mono_rho hV P.D hg hg1 hB0 hB1) (P.k + 1 - l) (by omega) t L

end GenParams

end LeanProofs.GowersSzemeredi
