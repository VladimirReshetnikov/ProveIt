import IPRADerivations.Analysis.Polynomials.GaussianRationalGridCoefficientEquality
import IPRADerivations.Analysis.Polynomials.GaussianRationalLowCoefficientConvolution

/-!
# Padding one actual product factor preserves every original coefficient

The actual product of a zero-padded left factor has the same evaluation
as the padded original product. The existing proved finite grid theorem
then identifies their actual normalized coefficient codes. Original
padding lookup recovers every original exponent reader. No formal
polynomial identity, coefficient law or input canonicality is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialProductLeftPadding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalPolynomialProduct (product product_length product_evaluation product_canonical)
open GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open GaussianRationalSyntheticDivision (qmul_congr canonical_coefficient_at)
open GaussianRationalHorner (evaluate)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalGridCoefficientEquality (gridEqual)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianTranslatedNonconstant (recode_eq recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem factor_length (P N t : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N) : Γ ⊢[PRAAx]
    length (leftPad P t) ≐ succ (t+N) :=
  (pad_length P t).eqTrans ((congrAdd (.eqRefl t) hP).eqTrans (by ipra_ring))

theorem original_padding_length (P Q N M t : PTm n) : Γ ⊢[PRAAx]
    length (leftPad (product P Q N M) t) ≐ succ ((t+N)+M) :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl t) (product_length P Q N M)).eqTrans (by ipra_ring))

theorem evaluation_identity (P Q N M t z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (product (leftPad P t) Q (t+N) M) z ≐ evaluate (leftPad (product P Q N M) t) z :=
  (product_evaluation _ _ _ _ _ (factor_length P N t hP) hQ).eqTrans
    ((qmul_congr (pad_evaluation P t z) (.eqRefl _)).eqTrans
      ((product_evaluation P Q N M z hP hQ).eqSymm.eqTrans (pad_evaluation _ _ _).eqSymm))

theorem grid_identity (P Q N M t : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    gridEqual (product (leftPad P t) Q (t+N) M) (leftPad (product P Q N M) t) ((t+N)+M) := by
  have hp : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hP.shift
  have hq : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hQ.shift
  refine .allI (.impI ?_)
  simpa only [gridEqual,Syn.shift,GaussianRationalPolynomialProduct.subst_product,GaussianRationalPolynomialBuffers.subst_leftPad,PTm.subst_add] using
    evaluation_identity (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift t) (gridPoint (var 0)) hp.wk hq.wk

theorem original_entry (P Q N M t e : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (he : Γ ⊢[PRAAx] le e (N+M)) : Γ ⊢[PRAAx]
    entry (product (leftPad P t) Q (t+N) M) (monus ((t+N)+M) e) ≐ entry (product P Q N M) (monus (N+M) e) := by
  have nextRange : Γ ⊢[PRAAx] le (monus ((t+N)+M) e) ((t+N)+M) := GaussianRationalMonicReconstruction.monus_le_left _ _
  have oldRange : Γ ⊢[PRAAx] le (monus (N+M) e) (N+M) := GaussianRationalMonicReconstruction.monus_le_left _ _
  have newCan := canonical_coefficient_at (Γ := Γ) _ _ (product_canonical (leftPad P t) Q (t+N) M)
    (lt_congr (.eqRefl _) (product_length (leftPad P t) Q (t+N) M).eqSymm ((succ_monus_succ _ _).eqTrans nextRange))
  have oldCan := canonical_coefficient_at (Γ := Γ) _ _ (product_canonical P Q N M)
    (lt_congr (.eqRefl _) (product_length _ _ _ _).eqSymm ((succ_monus_succ _ _).eqTrans oldRange))
  have indices : Γ ⊢[PRAAx] monus ((t+N)+M) e ≐ t+monus (N+M) e :=
    (congrMonus (by ipra_ring) (.eqRefl e)).eqTrans (GaussianRationalLowCoefficientConvolution.index_decompose t (N+M) e he)
  have padded : Γ ⊢[PRAAx] entry (leftPad (product P Q N M) t) (monus ((t+N)+M) e) ≐ entry (product P Q N M) (monus (N+M) e) :=
    (entry_congr (.eqRefl _) indices).eqTrans (GaussianRationalPolynomialBuffers.pad_tail _ _ _
      (lt_congr (.eqRefl _) (product_length _ _ _ _).eqSymm ((succ_monus_succ _ _).eqTrans oldRange)))
  exact (recode_eq _ newCan).eqSymm.eqTrans
    ((GaussianRationalGridCoefficientEquality.coefficient_recode_equal _ _ _ _ (product_length _ _ _ _)
      (original_padding_length P Q N M t) (grid_identity P Q N M t hP hQ) nextRange).eqTrans
        ((recode_congr padded).eqTrans (recode_eq _ oldCan)))

theorem original_reader (P Q N M t e : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (he : Γ ⊢[PRAAx] le e (N+M)) : Γ ⊢[PRAAx]
    exponentCoefficient (product (leftPad P t) Q (t+N) M) ((t+N)+M) e ≐
      exponentCoefficient (product P Q N M) (N+M) e := by
  have next : Γ ⊢[PRAAx] le e ((t+N)+M) := le_trans he (le_of_eq_add (d := t) (by ipra_ring))
  exact (exponent_inside _ _ _ next).eqTrans ((original_entry P Q N M t e hP hQ he).eqTrans
    (exponent_inside _ _ _ he).eqSymm)

theorem actual_product_left_padding_preserves_original_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶ le (var 5) (var 2+var 3) ⟶
      exponentCoefficient (product (leftPad (var 0) (var 4)) (var 1) (var 4+var 2) (var 3)) ((var 4+var 2)+var 3) (var 5) ≐
        exponentCoefficient (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (original_reader _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialProductLeftPadding
