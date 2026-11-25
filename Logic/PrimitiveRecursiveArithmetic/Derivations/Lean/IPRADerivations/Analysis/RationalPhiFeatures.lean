import IPRADerivations.Analysis.RationalAnnihilatorOnSpan
import IPRADerivations.Analysis.GaussianRationalPowerExpansion
import IPRADerivations.Core.CongruenceTactic

/-!
# The original (1,x,...,x^s,y) feature buffer and annihilator equation

The source feature coordinates are original rational powers and the recoded
original ordinate. Reversing the first s+1 annihilator coefficients produces
an actual descending polynomial P. Its original dot equation is exactly
P(x)+a*y=0. All sizes and data are numerical, and no coprimality, curve or
nonzero ordinate coefficient assumption enters this bridge.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiFeatures

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero scalarOne)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup embed_congr evaluate)
open RationalScalarPowerGaussianEmbedding (power powerF power_embedding)
open GaussianRationalHorner (qmul qadd qzero)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def dimension (s : PTm n) : PTm n := succ (succ s)
def coordinate (s x y i : PTm n) : PTm n := RationalArithmetic.select (eqb i (succ s))
  (power x i) (RationalArithmetic.recode y)
def data (s x y : PTm n) : PTm n := pairT s (pairT x y)
def featureBody : PTm 2 := coordinate (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def features (s x y : PTm n) : PTm n := sequence featureBody (dimension s) (data s x y)
def polynomialBody : PTm 2 := RationalArithmetic.recode (entry (fstT (var 1)) (monus (sndT (var 1)) (var 0)))
def polynomial (a s : PTm n) : PTm n := sequence polynomialBody (succ s) (pairT a s)
def dot (a s x y : PTm n) : PTm n := RationalOriginalAnnihilator.rowDot
  (GaussianRationalMonicReduction.singleton (features s x y)) (dimension s) a zero

def equation (a s x y : PTm n) : PTm n := RationalArithmetic.add (evaluate (polynomial a s) x)
  (RationalArithmetic.multiply (entry a (succ s)) y)

@[simp] theorem subst_dimension {q : ℕ} (σ : Fin n → PTm q) (s : PTm n) :
    Syn.subst σ (dimension s) = dimension (Syn.subst σ s) := by simp [dimension]
@[simp] theorem subst_coordinate {q : ℕ} (σ : Fin n → PTm q) (s x y i : PTm n) :
    Syn.subst σ (coordinate s x y i) = coordinate (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ i) := by simp [coordinate,RationalArithmetic.recode]
@[simp] theorem subst_data {q : ℕ} (σ : Fin n → PTm q) (s x y : PTm n) :
    Syn.subst σ (data s x y) = data (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by simp [data]
@[simp] theorem subst_features {q : ℕ} (σ : Fin n → PTm q) (s x y : PTm n) :
    Syn.subst σ (features s x y) = features (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by simp [features]
@[simp] theorem subst_polynomial {q : ℕ} (σ : Fin n → PTm q) (a s : PTm n) :
    Syn.subst σ (polynomial a s) = polynomial (Syn.subst σ a) (Syn.subst σ s) := by simp [polynomial]
@[simp] theorem subst_dot {q : ℕ} (σ : Fin n → PTm q) (a s x y : PTm n) :
    Syn.subst σ (dot a s x y) = dot (Syn.subst σ a) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by simp [dot]
@[simp] theorem subst_equation {q : ℕ} (σ : Fin n → PTm q) (a s x y : PTm n) :
    Syn.subst σ (equation a s x y) = equation (Syn.subst σ a) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by simp [equation]

private theorem coordinate_congr {s t x u y v i j : PTm n} (hs : Γ ⊢[PRAAx] s ≐ t)
    (hx : Γ ⊢[PRAAx] x ≐ u) (hy : Γ ⊢[PRAAx] y ≐ v) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    coordinate s x y i ≐ coordinate t u v j := by
  ipra_congr (coordinate (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hs, hx, hy, hi]
theorem feature_body_at (s x y i : PTm n) : Γ ⊢[PRAAx] inst2 featureBody i (data s x y) ≐ coordinate s x y i := by
  simp only [featureBody,inst2,subst_coordinate,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact coordinate_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem features_length (s x y : PTm n) : Γ ⊢[PRAAx] length (features s x y) ≐ dimension s := sequence_length _ _ _
theorem features_lookup (s x y i : PTm n) (hi : Γ ⊢[PRAAx] lt i (dimension s)) : Γ ⊢[PRAAx]
    entry (features s x y) i ≐ coordinate s x y i := (sequence_decode featureBody (x := data s x y) hi).eqTrans (feature_body_at _ _ _ _)
theorem coordinate_power (s x y i : PTm n) (hi : Γ ⊢[PRAAx] le i s) : Γ ⊢[PRAAx] coordinate s x y i ≐ power x i := by
  have ne : Γ ⊢[PRAAx] neg (i ≐ succ s) := .impI (not_succ_le_self s Fm.bot (le_congr Prf.hyp0 (.eqRefl _) hi.wk))
  exact RationalArithmetic.select_zero _ _ _ (eqb_of_ne ne)
theorem coordinate_last (s x y : PTm n) : Γ ⊢[PRAAx] coordinate s x y (succ s) ≐ RationalArithmetic.recode y :=
  RationalArithmetic.select_one _ _ _ (eqb_of_eq (.eqRefl _))
theorem features_power (s x y i : PTm n) (hi : Γ ⊢[PRAAx] le i s) : Γ ⊢[PRAAx]
    entry (features s x y) i ≐ power x i := by
  have hs : Γ ⊢[PRAAx] lt i (succ s) := (succ_monus_succ i s).eqTrans hi
  exact (features_lookup s x y i (le_trans hs (le_succ_self (succ s)))).eqTrans (coordinate_power _ _ _ _ hi)
theorem features_first (s x y : PTm n) : Γ ⊢[PRAAx] entry (features s x y) zero ≐ scalarOne :=
  (features_power s x y zero (zero_le _)).eqTrans (RationalScalarPowerGaussianEmbedding.power_zero x)
theorem features_last (s x y : PTm n) : Γ ⊢[PRAAx] entry (features s x y) (succ s) ≐ RationalArithmetic.recode y :=
  (features_lookup s x y (succ s) (le_refl _)).eqTrans (coordinate_last _ _ _)

private theorem recode_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] RationalArithmetic.recode a ≐ RationalArithmetic.recode b := by
  ipra_congr (RationalArithmetic.recode (var 0) : PTm 1) with [h]
theorem polynomial_body_at (a s i : PTm n) : Γ ⊢[PRAAx] inst2 polynomialBody i (pairT a s) ≐
    RationalArithmetic.recode (entry a (monus s i)) := by
  simp only [polynomialBody,inst2,RationalArithmetic.subst_recode,subst_fstT,subst_sndT,
    Foundations.MasterCertificate.subst_entry,LeanProofs.IPRA.PTm.subst_monus,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact recode_congr (entry_congr (fst_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))

theorem polynomial_length (a s : PTm n) : Γ ⊢[PRAAx] length (polynomial a s) ≐ succ s := sequence_length _ _ _

theorem polynomial_lookup (a s i : PTm n) (hi : Γ ⊢[PRAAx] le i s) : Γ ⊢[PRAAx]
    entry (polynomial a s) i ≐ RationalArithmetic.recode (entry a (monus s i)) :=
  (sequence_decode polynomialBody (x := pairT a s) ((succ_monus_succ i s).eqTrans hi)).eqTrans (polynomial_body_at _ _ _)
theorem polynomial_ascending (a s i : PTm n) (hi : Γ ⊢[PRAAx] le i s) : Γ ⊢[PRAAx]
    entry (polynomial a s) (monus s i) ≐ RationalArithmetic.recode (entry a i) :=
  (polynomial_lookup a s _ (GaussianRationalMonicReconstruction.monus_le_left s i)).eqTrans
    (recode_congr (entry_congr (.eqRefl a) (GaussianRationalMonicReconstruction.complement s i hi)))
theorem embedded_ascending (a s i : PTm n) (hi : Γ ⊢[PRAAx] le i s) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient (coefficients (polynomial a s) (succ s)) s i ≐ embed (entry a i) :=
  (coefficient_lookup (polynomial a s) (succ s) (monus s i)
    ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left s i))).eqTrans
      ((embed_congr (polynomial_ascending a s i hi)).eqTrans (RationalGaussianEmbedding.embed_recode _))

def dotData (a s x y : PTm n) : PTm n := GaussianRationalRowElimination.dotData
  (GaussianRationalMonicReduction.singleton (features s x y)) a zero
@[simp] theorem subst_dotData {q : ℕ} (σ : Fin n → PTm q) (a s x y : PTm n) :
    Syn.subst σ (dotData a s x y) = dotData (Syn.subst σ a) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by simp [dotData]

theorem dot_term_embedding (a s x y i : PTm n) (hi : Γ ⊢[PRAAx] lt i (dimension s)) : Γ ⊢[PRAAx]
    inst2 (RationalGaussianRealPart.embedBody RationalOriginalAnnihilator.dotBody) i (dotData a s x y) ≐
      qmul (embed (entry a i)) (embed (coordinate s x y i)) := by
  have row : Γ ⊢[PRAAx] GaussianPolynomialDeterminantTerms.cell
      (GaussianRationalMonicReduction.singleton (features s x y)) zero i ≐ coordinate s x y i :=
    (entry_congr (GaussianRationalMonicReduction.singleton_lookup (features s x y)) (.eqRefl i)).eqTrans (features_lookup s x y i hi)
  have term := (RationalOriginalAnnihilator.dot_body_at (Γ := Γ)
    (GaussianRationalMonicReduction.singleton (features s x y)) a zero i).eqTrans
      (RationalAlgebra.multiply_congr (.eqRefl _) row)
  simpa only [RationalGaussianRealPart.embedBody,inst2,RationalGaussianEmbedding.subst_embed,dotData] using
    (embed_congr term).eqTrans (RationalGaussianEmbedding.embed_multiply _ _)

theorem prefix_evaluation (a s x y : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (RationalGaussianRealPart.embedBody RationalOriginalAnnihilator.dotBody) (succ s) (dotData a s x y) ≐
      embed (evaluate (polynomial a s) x) := by
  let C := coefficients (polynomial a s) (succ s)
  let z := embed x
  have expansion : Γ ⊢[PRAAx] GaussianRationalHorner.evaluate C z ≐
      GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ s) (GaussianRationalPowerExpansion.data C s z) :=
    (GaussianRationalPowerExpansion.power_expansion C s z (RationalPolynomialGaussianEmbedding.coefficients_length _ _)).eqTrans
      (congrAp3 GaussianRationalHorner.hornerF (GaussianRationalPowerExpansion.terms_length C s z) (.eqRefl _) (.eqRefl _))
  have same : Γ ⊢[PRAAx]
      GaussianRationalFiniteSum.sum (RationalGaussianRealPart.embedBody RationalOriginalAnnihilator.dotBody) (succ s) (dotData a s x y) ≐
      GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ s) (GaussianRationalPowerExpansion.data C s z) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let Δ := lt (var 0) (succ (Syn.shift s)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift s) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have hb : Δ ⊢[PRAAx] lt (var 0) (dimension (Syn.shift s)) := le_trans Prf.hyp0 (le_succ_self (succ (Syn.shift s)))
    have low := (dot_term_embedding (Γ := Δ) (Syn.shift a) (Syn.shift s) (Syn.shift x) (Syn.shift y) (var 0) hb).eqTrans
      (qmul_congr (.eqRefl _) ((embed_congr (coordinate_power _ _ _ _ hi)).eqTrans (power_embedding _ _)))
    have high := (GaussianRationalPowerExpansion.term_body_at (Γ := Δ)
      (coefficients (polynomial (Syn.shift a) (Syn.shift s)) (succ (Syn.shift s))) (Syn.shift s) (embed (Syn.shift x)) (var 0)).eqTrans
        (qmul_congr (embedded_ascending _ _ _ hi) (.eqRefl _))
    simpa only [Δ,C,z,Syn.shift,subst_dotData,subst_polynomial,RationalPolynomialGaussianEmbedding.subst_coefficients,
      RationalGaussianEmbedding.subst_embed,GaussianRationalPowerExpansion.subst_data,ConciseIPRA.PTm.subst_succ] using low.eqTrans high.eqSymm
  exact same.eqTrans (expansion.eqSymm.eqTrans
    (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width (polynomial a s) (succ s) x (polynomial_length a s)).eqSymm)

theorem dot_embedding (a s x y : PTm n) : Γ ⊢[PRAAx]
    embed (dot a s x y) ≐ qadd (embed (evaluate (polynomial a s) x)) (qmul (embed (entry a (succ s))) (embed y)) := by
  have last := (dot_term_embedding (Γ := Γ) a s x y (succ s) (le_refl (dimension s))).eqTrans
    (qmul_congr (.eqRefl _) ((embed_congr (coordinate_last s x y)).eqTrans (RationalGaussianEmbedding.embed_recode y)))
  exact (RationalGaussianRealPart.embed_sum RationalOriginalAnnihilator.dotBody (dimension s) (dotData a s x y)).eqTrans
    ((GaussianRationalFiniteSum.sum_succ _ (succ s) _).eqTrans (qadd_congr (prefix_evaluation a s x y) last))

theorem dot_identity (a s x y : PTm n) : Γ ⊢[PRAAx] dot a s x y ≐ equation a s x y := by
  have rhs : Γ ⊢[PRAAx] embed (equation a s x y) ≐
      qadd (embed (evaluate (polynomial a s) x)) (qmul (embed (entry a (succ s))) (embed y)) :=
    (RationalGaussianEmbedding.embed_add _ _).eqTrans (qadd_congr (.eqRefl _) (RationalGaussianEmbedding.embed_multiply _ _))
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalFiniteSum.sum_well_formed _ _ _) (RationalArithmetic.add_guard _ _) ((dot_embedding a s x y).eqTrans rhs.eqSymm)

theorem dot_as_vector (a s x y : PTm n) : Γ ⊢[PRAAx]
    embed (dot a s x y) ≐ GaussianRationalRowSpan.vectorDot (dimension s)
      (coefficients (features s x y) (dimension s)) (coefficients a (dimension s)) := by
  refine (RationalGaussianRealPart.embed_sum RationalOriginalAnnihilator.dotBody (dimension s) (dotData a s x y)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ GaussianRationalRowElimination.dotBody (dimension s) _
      (GaussianRationalRowElimination.dotData (GaussianRationalMonicReduction.singleton
        (coefficients (features s x y) (dimension s))) (coefficients a (dimension s)) zero) (.allI (.impI ?_)))
  let Δ := lt (var 0) (dimension (Syn.shift s)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (dimension (Syn.shift s)) := Prf.hyp0
  have low := dot_term_embedding (Γ := Δ) (Syn.shift a) (Syn.shift s) (Syn.shift x) (Syn.shift y) (var 0) hi
  have high := (GaussianRationalRowSpan.vector_dot_term (Γ := Δ)
    (coefficients (features (Syn.shift s) (Syn.shift x) (Syn.shift y)) (dimension (Syn.shift s)))
    (coefficients (Syn.shift a) (dimension (Syn.shift s))) (var 0)).eqTrans
      (qmul_congr ((coefficient_lookup _ _ _ hi).eqTrans (embed_congr (features_lookup _ _ _ _ hi))) (coefficient_lookup _ _ _ hi))
  simpa only [Δ,Syn.shift,subst_dimension,subst_dotData,subst_features,RationalPolynomialGaussianEmbedding.subst_coefficients,
    GaussianRationalRowElimination.subst_dotData,GaussianRationalMonicReduction.subst_singleton,ConciseIPRA.PTm.subst_zero] using
    low.eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans high.eqSymm)

theorem span_equation (A R a s x y : PTm n)
    (hn : Γ ⊢[PRAAx] RationalOriginalAnnihilator.nullRows A R (dimension s) a)
    (hm : Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.hasCoefficients A R (dimension s) (features s x y)) : Γ ⊢[PRAAx]
    equation a s x y ≐ scalarZero := by
  have zeroDot := GaussianSuperellipticSubspaceFromSpan.span_dot_zero _ _ _ _ _
    (RationalRowSpanGaussianEmbedding.span_embedding A R (dimension s) (features s x y) hm)
    (RationalAnnihilatorOnSpan.null_rows_embedding A R (dimension s) a hn)
  have zero : Γ ⊢[PRAAx] embed (dot a s x y) ≐ embed (scalarZero : PTm n) :=
    (dot_as_vector a s x y).eqTrans (zeroDot.eqTrans RationalGaussianEmbedding.embed_zero.eqSymm)
  have literal := RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalFiniteSum.sum_well_formed _ _ _) (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) zero
  exact (dot_identity a s x y).eqSymm.eqTrans literal

def annihilator (A R s : PTm n) : PTm n := RationalOriginalAnnihilator.vector A R (dimension s)
def free (A R s : PTm n) : PTm n := RationalOriginalAnnihilator.free A R (dimension s)
@[simp] theorem subst_annihilator {q : ℕ} (σ : Fin n → PTm q) (A R s : PTm n) :
    Syn.subst σ (annihilator A R s) = annihilator (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ s) := by simp [annihilator]
@[simp] theorem subst_free {q : ℕ} (σ : Fin n → PTm q) (A R s : PTm n) :
    Syn.subst σ (free A R s) = free (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ s) := by simp [free]

theorem computed_certificate (A R s : PTm n) (hp : Γ ⊢[PRAAx] RationalSuperellipticSubspace.properSpan A R (dimension s)) : Γ ⊢[PRAAx]
    RationalOriginalAnnihilator.certificate A R (dimension s) (annihilator A R s) (free A R s) :=
  RationalOriginalAnnihilator.certificate_of_deficit _ _ _ (RationalSuperellipticSubspace.rank_deficit _ _ _ hp)
theorem computed_equation (A R s x y : PTm n) (hp : Γ ⊢[PRAAx] RationalSuperellipticSubspace.properSpan A R (dimension s))
    (hm : Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.hasCoefficients A R (dimension s) (features s x y)) : Γ ⊢[PRAAx]
    equation (annihilator A R s) s x y ≐ scalarZero :=
  span_equation A R (annihilator A R s) s x y (.andE₂ (.andE₂ (.andE₂ (computed_certificate A R s hp)))) hm

def featuresF : PR 3 := PTm.toPR (features (var 0) (var 1) (var 2))
def polynomialF : PR 2 := PTm.toPR (polynomial (var 0) (var 1))
def output (A R s x y : PTm n) : PTm n := pairT (features s x y)
  (pairT (annihilator A R s) (pairT (polynomial (annihilator A R s) s)
    (pairT (equation (annihilator A R s) s x y) (free A R s))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R s x y : PTm n) : PTm n := app outputF ![A,R,s,x,y]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (A R s x y : PTm n) :
    Syn.subst σ (output A R s x y) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (A R s x y : PTm n) :
    Syn.subst σ (run A R s x y) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ y) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem features_program_at (s x y : PTm n) : Γ ⊢[PRAAx] app featuresF ![s,x,y] ≐ features s x y := by
  simpa [featuresF] using toPR_eq (Γ := Γ) (features (var 0) (var 1) (var 2) : PTm 3) ![s,x,y]
theorem polynomial_program_at (a s : PTm n) : Γ ⊢[PRAAx] app polynomialF ![a,s] ≐ polynomial a s := by
  simpa [polynomialF] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) : PTm 2) ![a,s]
theorem program_at (A R s x y : PTm n) : Γ ⊢[PRAAx] run A R s x y ≐ output A R s x y := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,s,x,y]
theorem returned_features (A R s x y : PTm n) : Γ ⊢[PRAAx] fstT (run A R s x y) ≐ features s x y :=
  (congrFst (program_at A R s x y)).eqTrans (fst_pair _ _)
theorem returned_annihilator (A R s x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A R s x y)) ≐ annihilator A R s :=
  (congrFst ((congrSnd (program_at A R s x y)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_polynomial (A R s x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A R s x y))) ≐ polynomial (annihilator A R s) s :=
  (congrFst ((congrSnd ((congrSnd (program_at A R s x y)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_equation (A R s x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run A R s x y)))) ≐ equation (annihilator A R s) s x y :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at A R s x y)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_free (A R s x y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run A R s x y)))) ≐ free A R s :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at A R s x y)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_zero (A R s x y : PTm n) (hp : Γ ⊢[PRAAx] RationalSuperellipticSubspace.properSpan A R (dimension s))
    (hm : Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.hasCoefficients A R (dimension s) (features s x y)) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run A R s x y)))) ≐ scalarZero :=
  (returned_equation A R s x y).eqTrans (computed_equation A R s x y hp hm)

theorem actual_phi_features_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (features (var 0) (var 1) (var 2)) ≐ dimension (var 0)) := closeUniv 3 (features_length _ _ _)
theorem actual_phi_features_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 0) ⟶ entry (features (var 0) (var 1) (var 2)) (var 3) ≐ power (var 1) (var 3)) :=
  closeUniv 4 (.impI (features_power _ _ _ _ Prf.hyp0))
theorem actual_phi_features_last_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (features (var 0) (var 1) (var 2)) (succ (var 0)) ≐ RationalArithmetic.recode (var 2)) := closeUniv 3 (features_last _ _ _)
theorem actual_phi_polynomial_ascending_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ entry (polynomial (var 0) (var 1)) (monus (var 1) (var 2)) ≐ RationalArithmetic.recode (entry (var 0) (var 2))) :=
  closeUniv 3 (.impI (polynomial_ascending _ _ _ Prf.hyp0))
theorem actual_phi_dot_horner_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (dot (var 0) (var 1) (var 2) (var 3) ≐ equation (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (dot_identity _ _ _ _)
theorem actual_phi_computed_linear_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (RationalSuperellipticSubspace.properSpan (var 0) (var 1) (dimension (var 2)) ⟶
      RationalRowSpanGaussianEmbedding.hasCoefficients (var 0) (var 1) (dimension (var 2)) (features (var 2) (var 3) (var 4)) ⟶
        equation (annihilator (var 0) (var 1) (var 2)) (var 2) (var 3) (var 4) ≐ scalarZero) :=
  closeUniv 5 (.impI (.impI (computed_equation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_phi_features_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (app featuresF ![var 0,var 1,var 2] ≐ features (var 0) (var 1) (var 2)) := closeUniv 3 (features_program_at _ _ _)
theorem actual_phi_polynomial_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app polynomialF ![var 0,var 1] ≐ polynomial (var 0) (var 1)) := closeUniv 2 (polynomial_program_at _ _)
theorem actual_phi_computed_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_phi_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (RationalSuperellipticSubspace.properSpan (var 0) (var 1) (dimension (var 2)) ⟶
      RationalRowSpanGaussianEmbedding.hasCoefficients (var 0) (var 1) (dimension (var 2)) (features (var 2) (var 3) (var 4)) ⟶
        fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ scalarZero) :=
  closeUniv 5 (.impI (.impI (returned_zero _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalPhiFeatures
