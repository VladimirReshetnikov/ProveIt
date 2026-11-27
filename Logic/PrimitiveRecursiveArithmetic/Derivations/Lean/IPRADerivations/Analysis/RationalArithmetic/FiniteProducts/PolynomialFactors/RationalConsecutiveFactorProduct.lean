import IPRADerivations.Analysis.Polynomials.Products.RationalPolynomialProductGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProductDegree
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormOrder
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct

/-!
# The actual rational polynomial with roots 1 through m

The primitive recursive coefficient fold multiplies the original rational
polynomials X-(j+1) in order. Every prefix has exactly the expected length,
has leading coefficient 1, and vanishes at each previously included integer.
This is the consecutive product in the sharpness construction for rational
superelliptic sections.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConsecutiveFactorProduct

open_ipra
open RationalGaussianEmbedding (embed embed_add embed_multiply embed_negative embed_one embed_zero scalarOne scalarZero)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup embed_congr evaluate horner hornerF horner_zero horner_succ)
open RationalPolynomialProductGaussianEmbedding (product product_length product_evaluation product_embedding)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_left qmul_zero_right qone qzero_add)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open GaussianRationalSyntheticBounds (natCode)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (append append_length append_left append_right entry_congr length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def root (j : PTm n) : PTm n := natCode (succ j)

def linear (j : PTm n) : PTm n :=
  append (singleton scalarOne) (singleton (RationalArithmetic.negative (root j)))

def initial : PTm 0 := singleton scalarOne
def step : PTm 2 := product (var 1) (linear (var 0)) (var 0) one
def consecutiveF : PR 1 := rec1 initial step
def consecutive (m : PTm n) : PTm n := ap1 consecutiveF m

ipra_subst root
ipra_subst linear
ipra_subst consecutive

theorem linear_length (j : PTm n) : Γ ⊢[PRAAx] length (linear j) ≐ succ one :=
  (append_length _ _).eqTrans ((congrAdd (singleton_length _) (singleton_length _)).eqTrans
    ((add_succ one zero).eqTrans (congrSucc (add_zero one))))

theorem linear_head (j : PTm n) : Γ ⊢[PRAAx] entry (linear j) zero ≐ scalarOne := by
  exact (append_left (lt_congr (.eqRefl _) (singleton_length _).eqSymm (le_refl one))).eqTrans (singleton_lookup _)

theorem linear_tail (j : PTm n) : Γ ⊢[PRAAx] entry (linear j) one ≐ RationalArithmetic.negative (root j) := by
  let a := singleton (scalarOne : PTm n)
  let b := singleton (RationalArithmetic.negative (root j))
  have hi : Γ ⊢[PRAAx] lt zero (length b) := lt_congr (.eqRefl _) (singleton_length _).eqSymm (le_refl one)
  have e : Γ ⊢[PRAAx] length a + zero ≐ one := (add_zero _).eqTrans (singleton_length _)
  exact (entry_congr (Γ := Γ) (.eqRefl (append a b)) e.eqSymm).eqTrans
    ((append_right hi).eqTrans (singleton_lookup _))

private theorem embedded_horner_succ (C z j : PTm n) :
    Γ ⊢[PRAAx] embed (horner C z (succ j)) ≐ qadd (qmul (embed (horner C z j)) (embed z)) (embed (entry C j)) :=
  (embed_congr (horner_succ _ _ _)).eqTrans ((embed_add _ _).eqTrans (qadd_congr (embed_multiply _ _) (.eqRefl _)))

theorem linear_evaluation (j z : PTm n) :
    Γ ⊢[PRAAx] embed (evaluate (linear j) z) ≐ GaussianRationalMetric.qsub (embed z) (embed (root j)) := by
  let C := linear j
  have hz : Γ ⊢[PRAAx] embed (horner C z zero) ≐ qzero := (embed_congr (horner_zero _ _)).eqTrans embed_zero
  have h0 : Γ ⊢[PRAAx] embed (horner C z one) ≐ qone := (embedded_horner_succ _ _ zero).eqTrans
    ((qadd_congr ((qmul_congr hz (.eqRefl _)).eqTrans (qmul_zero_left _))
      ((embed_congr (linear_head j)).eqTrans embed_one)).eqTrans
      (qzero_add _ GaussianRationalSyntheticDivision.qone_canonical))
  have h1 := (embed_congr (linear_tail (Γ := Γ) j)).eqTrans (embed_negative (root j))
  have left := (GaussianRationalFiniteProduct.raw_one_left (Γ := Γ) (embed z)).eqTrans
    (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical z))
  exact (embed_congr (congrAp3 hornerF (linear_length j) (.eqRefl C) (.eqRefl z))).eqTrans
    ((embedded_horner_succ _ _ one).eqTrans (qadd_congr ((qmul_congr h0 (.eqRefl _)).eqTrans left) h1))

theorem consecutive_zero : Γ ⊢[PRAAx] consecutive (zero : PTm n) ≐ singleton scalarOne := by
  simpa [consecutive,consecutiveF,initial] using (rec1_zero (Γ := Γ) initial step)

theorem consecutive_succ (m : PTm n) : Γ ⊢[PRAAx] consecutive (succ m) ≐ product (consecutive m) (linear m) m one := by
  simpa [consecutive,consecutiveF,step] using rec1_succ (Γ := Γ) initial step m

theorem consecutive_length (m : PTm n) : Γ ⊢[PRAAx] length (consecutive m) ≐ succ m := by
  have all : Γ ⊢[PRAAx] .all (length (consecutive (var 0)) ≐ succ (var 0)) := by
    ipra_qfind [Foundations.SequenceComposition.subst_length, subst_consecutive]
    · exact (congrFst (consecutive_zero (Γ := Γ))).eqTrans (singleton_length scalarOne)
    · exact (congrFst (consecutive_succ _)).eqTrans ((product_length _ _ _ _).eqTrans
        (congrSucc ((add_succ _ zero).eqTrans (congrSucc (add_zero _)))))
  simpa using all.allE m

private theorem empty_zero_prefix (C : PTm n) : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.zeroPrefix C zero := by
  refine .allI (.impI ?_)
  simp only [Syn.shift,ConciseIPRA.PTm.subst_zero]
  exact lt_zero_absurd _ Prf.hyp0

private theorem product_head (P Q N M : PTm n) : Γ ⊢[PRAAx]
    embed (entry (product P Q N M) zero) ≐ qmul (embed (entry P zero)) (embed (entry Q zero)) := by
  let E := coefficients P (succ N)
  let F := coefficients Q (succ M)
  let G := GaussianRationalPolynomialProduct.product E F N M
  have left : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode (entry E zero) ≐ embed (entry P zero) :=
    (GaussianTranslatedNonconstant.recode_congr (coefficient_lookup P (succ N) zero (zero_lt_succ N))).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical _))
  have right : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode (entry F zero) ≐ embed (entry Q zero) :=
    (GaussianTranslatedNonconstant.recode_congr (coefficient_lookup Q (succ M) zero (zero_lt_succ M))).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical _))
  exact (product_embedding P Q N M zero (zero_le _)).eqTrans
    ((entry_congr (.eqRefl G) (zero_add zero).eqSymm).eqTrans
      ((GaussianRationalPolynomialProductDegree.product_entry_at E F N M zero zero (empty_zero_prefix E)
        (empty_zero_prefix F) (zero_le N) (zero_le M)).eqTrans (qmul_congr left right)))

theorem consecutive_head (m : PTm n) : Γ ⊢[PRAAx] embed (entry (consecutive m) zero) ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (embed (entry (consecutive (var 0)) zero) ≐ qone) := by
    ipra_qfind [RationalGaussianEmbedding.subst_embed, Foundations.MasterCertificate.subst_entry, subst_consecutive,
        GaussianRationalSyntheticDivision.subst_qone]
    · exact (embed_congr ((entry_congr (consecutive_zero (Γ := Γ)) (.eqRefl zero)).eqTrans
        (singleton_lookup scalarOne))).eqTrans embed_one
    · have right := (embed_congr (linear_head (Γ := Γ.map Fm.shift) (var 0))).eqTrans embed_one
      exact (embed_congr (entry_congr (consecutive_succ _) (.eqRefl zero))).eqTrans
        ((product_head _ _ _ _).eqTrans ((qmul_congr Prf.hyp0 right.wk).eqTrans
          ((GaussianRationalFiniteProduct.raw_one_left qone).eqTrans
            (GaussianTranslatedNonconstant.recode_eq _ GaussianRationalSyntheticDivision.qone_canonical))))
  simpa using all.allE m

theorem consecutive_evaluation_succ (m z : PTm n) : Γ ⊢[PRAAx]
    embed (evaluate (consecutive (succ m)) z) ≐ qmul (embed (evaluate (consecutive m) z))
      (GaussianRationalMetric.qsub (embed z) (embed (root m))) := by
  have h := consecutive_succ (Γ := Γ) m
  exact (embed_congr (congrAp3 hornerF (congrFst h) h (.eqRefl z))).eqTrans
    ((embed_congr (product_evaluation (consecutive m) (linear m) m one z (consecutive_length m) (linear_length m))).eqTrans
      ((embed_multiply _ _).eqTrans (qmul_congr (.eqRefl _) (linear_evaluation m z))))

def rootLaw (j m : PTm n) : Fm PTm n := lt j m ⟶ embed (evaluate (consecutive m) (root j)) ≐ qzero

ipra_subst rootLaw

private theorem root_step (j m : PTm n) (h : Γ ⊢[PRAAx] rootLaw j m) : Γ ⊢[PRAAx] rootLaw j (succ m) := by
  refine .impI (.orE (lt_or_le j m) ?_ ?_)
  · exact (consecutive_evaluation_succ m (root j)).eqTrans
      ((qmul_congr (.impE h.wk.wk Prf.hyp0) (.eqRefl _)).eqTrans (qmul_zero_left _))
  · have ej : le m j :: lt j (succ m) :: Γ ⊢[PRAAx] j ≐ m :=
      le_antisymm ((succ_monus_succ j m).eqSymm.eqTrans Prf.hyp1) Prf.hyp0
    have er : le m j :: lt j (succ m) :: Γ ⊢[PRAAx] root j ≐ root m := by
      ipra_congr (root (var 0) : PTm 1) with [ej]
    exact (consecutive_evaluation_succ m (root j)).eqTrans
      ((qmul_congr (.eqRefl _) ((GaussianRationalSyntheticDivision.qsub_congr (embed_congr er) (.eqRefl _)).eqTrans
        (GaussianCoefficientNormOrder.qsub_self _))).eqTrans (qmul_zero_right _))

theorem consecutive_root (j m : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    RationalArgmin.rationalEq (evaluate (consecutive m) (root j)) scalarZero := by
  have all : Γ ⊢[PRAAx] .all (rootLaw (Syn.shift j) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_rootLaw]
    · exact .impI (lt_zero_absurd _ Prf.hyp0)
    · exact root_step _ _ Prf.hyp0
  have atRoot : Γ ⊢[PRAAx] rootLaw j m := by simpa using all.allE m
  exact RationalGaussianEmbedding.rational_equal_of_embed _ _ ((Prf.impE atRoot hj).eqTrans embed_zero.eqSymm)

theorem actual_consecutive_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (evaluate (linear (var 0)) (var 1)) ≐ GaussianRationalMetric.qsub (embed (var 1)) (embed (root (var 0)))) :=
  closeUniv 2 (linear_evaluation (var 0) (var 1))

theorem actual_consecutive_product_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (consecutive (succ (var 0)) ≐ product (consecutive (var 0)) (linear (var 0)) (var 0) one) :=
  closeUniv 1 (consecutive_succ (var 0))

theorem actual_consecutive_product_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (consecutive (var 0)) ≐ succ (var 0) ⋏ embed (entry (consecutive (var 0)) zero) ≐ qone) :=
  closeUniv 1 (.andI (consecutive_length (var 0)) (consecutive_head (var 0)))

theorem actual_consecutive_product_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 0) (var 1) ⟶ RationalArgmin.rationalEq (evaluate (consecutive (var 1)) (root (var 0))) scalarZero) :=
  closeUniv 2 (.impI (consecutive_root (var 0) (var 1) Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalConsecutiveFactorProduct
