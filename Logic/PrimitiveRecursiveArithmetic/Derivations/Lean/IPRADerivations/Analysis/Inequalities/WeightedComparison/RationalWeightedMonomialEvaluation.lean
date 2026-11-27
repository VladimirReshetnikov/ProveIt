import IPRADerivations.Analysis.Inequalities.WeightedComparison.GaussianWeightedMonomialBasis
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalScalarPowerGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Representation.GaussianEmbedding.RationalPolynomialGaussianEmbedding
import IPRADerivations.Foundations.SequenceEquality

/-!
# Original rational evaluation of the weighted monomial list

Use the same numerical exponent list for both fields. The rational evaluator
maps its entries with the original rational power and multiplication programs.
Embedding those computed values gives the exact Gaussian evaluation vector.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalWeightedMonomialEvaluation

open_ipra
open GaussianWeightedMonomialBasis (basis count)
open RationalGaussianEmbedding (embed)
open RationalScalarPowerGaussianEmbedding (power powerF power_embedding)
open RationalPolynomialGaussianEmbedding (coefficients coefficientBody coefficient_lookup embed_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def monomial (x y p : PTm n) : PTm n := RationalArithmetic.multiply (power x (sndT p)) (power y (fstT p))

def body : PTm 2 := monomial (fstT (sndT (var 1))) (sndT (sndT (var 1)))
  (entry (fstT (var 1)) (var 0))

def vector (m d L x y : PTm n) : PTm n := sequence body (count m d L) (pairT (basis m d L) (pairT x y))

ipra_subst monomial

ipra_subst vector

theorem monomial_congr {x x' y y' p p' : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (hp : Γ ⊢[PRAAx] p ≐ p') : Γ ⊢[PRAAx] monomial x y p ≐ monomial x' y' p' :=
  RationalAlgebra.multiply_congr (congrAp2 powerF (congrSnd hp) hx) (congrAp2 powerF (congrFst hp) hy)

theorem monomial_embedding (x y p : PTm n) : Γ ⊢[PRAAx]
    embed (monomial x y p) ≐ GaussianWeightedMonomialBasis.monomial (embed x) (embed y) p :=
  (RationalGaussianEmbedding.embed_multiply _ _).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (power_embedding _ _) (power_embedding _ _))

theorem body_at (B x y r : PTm n) : Γ ⊢[PRAAx]
    inst2 body r (pairT B (pairT x y)) ≐ monomial x y (entry B r) := by
  have data := snd_pair (Γ := Γ) B (pairT x y)
  simp only [body,inst2,subst_monomial,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact monomial_congr data.fstE data.sndE
    (entry_congr (fst_pair _ _) (.eqRefl r))

theorem vector_length (m d L x y : PTm n) : Γ ⊢[PRAAx] length (vector m d L x y) ≐ count m d L :=
  sequence_length _ _ _

theorem vector_lookup (m d L x y r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    entry (vector m d L x y) r ≐ monomial x y (entry (basis m d L) r) :=
  (sequence_decode body hr).eqTrans (body_at _ _ _ _)

theorem embedded_lookup (m d L x y r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    entry (coefficients (vector m d L x y) (count m d L)) r ≐
      entry (GaussianWeightedMonomialBasis.evaluationVector m d L (embed x) (embed y)) r :=
  (coefficient_lookup _ _ _ hr).eqTrans ((embed_congr (vector_lookup _ _ _ _ _ _ hr)).eqTrans
    ((monomial_embedding _ _ _).eqTrans (GaussianWeightedMonomialBasis.evaluation_lookup _ _ _ _ _ _ hr).eqSymm))

theorem vector_embedding (m d L x y : PTm n) : Γ ⊢[PRAAx]
    coefficients (vector m d L x y) (count m d L) ≐
      GaussianWeightedMonomialBasis.evaluationVector m d L (embed x) (embed y) := by
  let G := GaussianWeightedMonomialBasis.evaluationBody
  let W := GaussianWeightedMonomialBasis.evaluationData m d L (embed x) (embed y)
  apply sequence_equal coefficientBody G (count m d L) (vector m d L x y) W
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) := Prf.hyp0
  have actual := embedded_lookup (Syn.shift m) (Syn.shift d) (Syn.shift L) (Syn.shift x) (Syn.shift y) (var 0) hr
  have left := sequence_decode coefficientBody (x := vector (Syn.shift m) (Syn.shift d) (Syn.shift L) (Syn.shift x) (Syn.shift y)) hr
  have right := sequence_decode G (x := GaussianWeightedMonomialBasis.evaluationData (Syn.shift m) (Syn.shift d)
    (Syn.shift L) (embed (Syn.shift x)) (embed (Syn.shift y))) hr
  simpa only [Δ,W,Syn.shift,subst_vector,GaussianWeightedMonomialBasis.subst_count,GaussianWeightedMonomialBasis.subst_evaluationData,
    RationalGaussianEmbedding.subst_embed] using left.eqSymm.eqTrans (actual.eqTrans right)

def vectorF : PR 5 := PTm.toPR (vector (var 0) (var 1) (var 2) (var 3) (var 4))

theorem vector_at (m d L x y : PTm n) : Γ ⊢[PRAAx] app vectorF ![m,d,L,x,y] ≐ vector m d L x y := by
  simpa [vectorF] using toPR_eq (Γ := Γ) (vector (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![m,d,L,x,y]

theorem actual_rational_monomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (count (var 0) (var 1) (var 2)) ⟶
      entry (vector (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
        monomial (var 3) (var 4) (entry (basis (var 0) (var 1) (var 2)) (var 5))) :=
  closeUniv 6 (.impI (vector_lookup _ _ _ _ _ _ Prf.hyp0))

theorem actual_rational_evaluation_vector_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coefficients (vector (var 0) (var 1) (var 2) (var 3) (var 4)) (count (var 0) (var 1) (var 2)) ≐
      GaussianWeightedMonomialBasis.evaluationVector (var 0) (var 1) (var 2) (embed (var 3)) (embed (var 4))) :=
  closeUniv 5 (vector_embedding _ _ _ _ _)

theorem actual_rational_evaluation_vector_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (app vectorF ![var 0,var 1,var 2,var 3,var 4] ≐ vector (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (vector_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalWeightedMonomialEvaluation
