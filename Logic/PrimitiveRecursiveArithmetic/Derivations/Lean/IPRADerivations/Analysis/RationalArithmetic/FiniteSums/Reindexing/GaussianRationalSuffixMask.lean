import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalBlockSums
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# A contiguous suffix as a zero-masked Gaussian sum

Keep the original evaluator and total count. A zero mask excludes the
initial cells, so an existing pointwise majorant on the full grid can
also bound the actual offset sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSuffixMask

open_ipra
open GaussianRationalBlockSums (maskBody mask_zero mask_kept)
open GaussianRationalFiniteSum (sum termsEqual sum_canonical)
open GaussianRationalHorner (qzero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gate : PTm 2 := LeanProofs.IPRA.PTm.monus (succ (var 0)) (var 1)
abbrev body (f : PTm 2) : PTm 2 := maskBody gate f

theorem omitted (f : PTm 2) (S i x : PTm n) (hi : Γ ⊢[PRAAx] lt i S) : Γ ⊢[PRAAx] inst2 (body f) i (pairT S x) ≐ qzero := by
  have e : Γ ⊢[PRAAx] LeanProofs.IPRA.PTm.monus (succ i) S ≐ zero :=
    (congrMonus (.eqRefl _) (eq_add_of_le hi)).eqTrans (monus_add _ _)
  exact mask_zero gate f S x i (by simpa [gate,inst2] using e)

theorem retained (f : PTm 2) (S i x : PTm n) (hi : Γ ⊢[PRAAx] le S i) : Γ ⊢[PRAAx] inst2 (body f) i (pairT S x) ≐ inst2 f i x := by
  let r := LeanProofs.IPRA.PTm.monus i S
  have e : Γ ⊢[PRAAx] succ i ≐ succ r+S := (congrSucc (eq_add_of_le hi)).eqTrans (by ipra_ring)
  have read : Γ ⊢[PRAAx] inst2 gate i S ≐ succ r := by
    simpa [gate,inst2] using (congrMonus e (.eqRefl S)).eqTrans (add_monus (succ r) S)
  exact mask_kept gate f S x i (.impI (succ_ne_zero (read.eqSymm.wk.eqTrans Prf.hyp0)))

theorem suffix (f : PTm 2) (S L x : PTm n) : Γ ⊢[PRAAx]
    sum (body f) (S+L) (pairT S x) ≐ sum (offB f) L (pairT S x) := by
  let g := body f
  let y := pairT S x
  have zeros : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.zeroTerms g S y := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalMatrixFiniteSums.zeroTerms,g,y,Syn.shift,subst_pairT] using
      omitted f (Syn.shift S) (var 0) (Syn.shift x) Prf.hyp0
  have rest : Γ ⊢[PRAAx] termsEqual (offB g) (offB f) L (pairT S y) y := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s L)::Γ.map Fm.shift
    have first := GaussianRationalFiniteProduct.offset_at (Γ := Δ) g (s S) i (pairT (s S) (s x))
    have second := GaussianRationalFiniteProduct.offset_at (Γ := Δ) f (s S) i (s x)
    have same := retained (Γ := Δ) f (s S) (s S+i) (s x) (le_add_right (s S) i)
    simpa only [termsEqual,g,y,Δ,s,i,Syn.shift,subst_pairT] using first.eqTrans (same.eqTrans second.eqSymm)
  have left := GaussianRationalMatrixFiniteSums.sum_zero_of_terms g S y zeros
  have right := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rest
  exact (GaussianRationalMatrixFiniteSums.sum_split g S L y).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr left right).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianReciprocalHorner.qadd_zero_right _ (sum_canonical _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianRationalSuffixMask
