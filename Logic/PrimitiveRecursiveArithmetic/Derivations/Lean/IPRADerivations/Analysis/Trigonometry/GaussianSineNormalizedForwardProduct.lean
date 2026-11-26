import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductReverse
import IPRADerivations.Analysis.Trigonometry.GaussianSineNormalizedSampleProduct

/-!
# Forward rows of the normalized sine product

This product reads the actual normalized sine factors at k=1 through
J in ascending order. The checked reversal identifies it with the
backwards product that is paired with polynomial reconstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineNormalizedForwardProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentDivisionAngleResidual (sineSample)
open GaussianRationalFiniteProduct (qprod product_congr_bounded)
open GaussianRationalProductReverse (reverseBody reversed reverse_at reverse_product)
open GaussianSineNormalizedSampleProduct (data normalizedProduct)
open GaussianSineRootNormalization (normalizedFactor)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBody : PTm 2 := normalizedFactor (sndT (sndT (sndT (var 1))))
  (sineSample (fstT (var 1)) (succ (var 0)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))))
def forwardProduct (p J z s : PTm n) : PTm n := qprod rowBody J (data p J z s)
def forwardF : PR 4 := PTm.toPR (forwardProduct (var 0) (var 1) (var 2) (var 3) : PTm 4)
def run (p J z s : PTm n) : PTm n := ConciseIPRA.PTm.app forwardF ![p,J,z,s]

@[simp] theorem subst_forwardProduct {l : ℕ} (σ : Fin n → PTm l) (p J z s : PTm n) :
    Syn.subst σ (forwardProduct p J z s) =
      forwardProduct (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) (Syn.subst σ s) := by
  simp [forwardProduct,GaussianSineNormalizedSampleProduct.data]

theorem program_at (p J z s : PTm n) : Γ ⊢[PRAAx] run p J z s ≐ forwardProduct p J z s := by
  simpa [run,forwardF] using toPR_eq (Γ := Γ) (forwardProduct (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,J,z,s]

theorem row_at (p J z s i : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody i (data p J z s) ≐ normalizedFactor s (sineSample p (succ i) J z) := by
  have tail1 := snd_pair (Γ := Γ) p (pairT J (pairT z s))
  have tail2 := (congrSnd tail1).eqTrans (snd_pair _ _)
  simpa [rowBody,LeanProofs.IPRA.inst2] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (normalizedFactor (var 3) (sineSample (var 0) (succ (var 4)) (var 1) (var 2)) : PTm 5)
      (σ := ![fstT (data p J z s),fstT (sndT (data p J z s)),fstT (sndT (sndT (data p J z s))),
        sndT (sndT (sndT (data p J z s))),i])
      (σ' := ![p,J,z,s,i]) (fun j => by
        fin_cases j
        · exact fst_pair _ _
        · exact (congrFst tail1).eqTrans (fst_pair _ _)
        · exact (congrFst tail2).eqTrans (fst_pair _ _)
        · exact (congrSnd tail2).eqTrans (snd_pair _ _)
        · exact .eqRefl _)

private theorem backward_body_at (p J z s i : PTm n) :
    Γ ⊢[PRAAx] inst2 GaussianSineNormalizedSampleProduct.body i (data p J z s) ≐
      inst2 (reverseBody rowBody) i (pairT J (data p J z s)) := by
  let d := data p J z s
  have field : Γ ⊢[PRAAx] fstT (sndT d) ≐ J := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have a : inst2 GaussianSineNormalizedSampleProduct.body i d =
      inst2 rowBody (monus (fstT (sndT d)) (succ i)) d := by
    simp [GaussianSineNormalizedSampleProduct.body,rowBody,LeanProofs.IPRA.inst2]
  rw [a]
  exact (congrInst2 rowBody (congrMonus field (.eqRefl _)) (.eqRefl _)).eqTrans
    (reverse_at rowBody J d i).eqSymm

theorem agrees_with_backward (p J z s : PTm n) :
    Γ ⊢[PRAAx] normalizedProduct p J z s ≐ forwardProduct p J z s := by
  have same : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianSineNormalizedSampleProduct.body (reverseBody rowBody)
      J (data p J z s) (pairT J (data p J z s)) := by
    refine .allI (.impI ?_)
    simpa [GaussianRationalFiniteSum.termsEqual,GaussianSineNormalizedSampleProduct.data,Syn.shift] using
      (backward_body_at (Syn.shift p) (Syn.shift J) (Syn.shift z) (Syn.shift s) (var 0)).wk
  exact (product_congr_bounded _ _ J _ _ same).eqTrans (reverse_product rowBody J (data p J z s))

theorem actual_forward_normalized_sine_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ normalizedProduct (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 ((program_at _ _ _ _).eqTrans (agrees_with_backward _ _ _ _).eqSymm)

end LeanProofs.IPRA.Analysis.GaussianSineNormalizedForwardProduct
