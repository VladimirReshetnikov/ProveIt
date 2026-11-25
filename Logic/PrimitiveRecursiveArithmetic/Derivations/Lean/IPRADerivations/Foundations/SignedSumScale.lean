import IPRADerivations.Foundations.SignedSums
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.CertificateTactics

/-!
# Pulling a signed scalar out of a finite sum

The signed body and the scalar each have a positive and a negative part.
Use the ordinary constant-scaled sums for the four products in the
difference representation, and compare signed values below the bound.
-/

namespace LeanProofs.IPRA.Foundations.SignedSumScale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def scaled (b : ZB) : ZB :=
  ⟨mixB (cmB b.pos) (cmB b.neg), mixB (cmB b.neg) (cmB b.pos)⟩

private abbrev inputs (K : ZT n) (x : PTm n) : PTm n :=
  pairT (pairT K.pos x) (pairT K.neg x)

private theorem val_at (b : ZB) (i x : PTm n) (K : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((scaled b).val i (inputs K x)) (K * b.val i x) := by
  have term (p q : PTm 2) : Γ ⊢[PRAAx]
      inst2 (mixB (cmB p) (cmB q)) i (inputs K x) ≐ K.pos * inst2 p i x + K.neg * inst2 q i x :=
    (mix_at _ _ _ _ _).eqTrans (congrAdd (cm_pt _ _ _ _) (cm_pt _ _ _ _))
  have scalar : ZT.toZ Γ K = Groth.ι (Q.mk Γ K.pos) - Groth.ι (Q.mk Γ K.neg) := rfl
  apply ZT.derive
  rw [ZT.toZ_mul, scalar]
  simp only [ZB.toZ_val, scaled]
  linear_combination (norm := ipra_close) natEq (term b.pos b.neg) - natEq (term b.neg b.pos)

private theorem sum_at (b : ZB) (N x : PTm n) (K : ZT n) :
    ZT.toZ Γ ((scaled b).sum N (inputs K x)) = ZT.toZ Γ K * ZT.toZ Γ (b.sum N x) := by
  have total (p q : PTm 2) : Γ ⊢[PRAAx] ap2 (sumF (mixB (cmB p) (cmB q))) N (inputs K x) ≐
      K.pos * ap2 (sumF p) N x + K.neg * ap2 (sumF q) N x :=
    (sum_mix _ _ _ _ _).eqTrans (congrAdd (sum_const_mul _ _ _ _) (sum_const_mul _ _ _ _))
  ipra_lc [scaled, ZT.toZ, ZB.sum] natEq (total b.pos b.neg) - natEq (total b.neg b.pos)

/-- A pointwise signed scaling equation gives the same scalar times the signed sum. -/
theorem sum_scale (a b : ZB) (N x y : PTm n) (K : ZT n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      ZT.eq (a.val (var 0) (Syn.shift y)) ((K.subst fun i => var i.succ) * b.val (var 0) (Syn.shift x)))) :
    ZT.toZ Γ (a.sum N y) = ZT.toZ Γ K * ZT.toZ Γ (b.sum N x) := by
  refine (ZB.toZ_sum_congr a (scaled b) y (inputs K x) N (.allI (.impI ?_))).trans (sum_at b N x K)
  have shiftInputs : Syn.shift (inputs K x) = inputs (K.subst fun i => var i.succ) (Syn.shift x) := by
    simp only [inputs, shift_pairT]
    rfl
  rw [shiftInputs]
  exact ZT.derive ((ZT.toZ_eq (.impE h.allOpen.wk Prf.hyp0)).trans (ZT.toZ_eq (val_at _ _ _ _)).symm)

end LeanProofs.IPRA.Foundations.SignedSumScale
