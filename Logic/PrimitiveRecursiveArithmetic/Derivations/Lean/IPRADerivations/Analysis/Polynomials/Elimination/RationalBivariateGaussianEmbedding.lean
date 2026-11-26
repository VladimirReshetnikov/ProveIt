import IPRADerivations.Analysis.RationalArithmetic.Spans.RationalRowSpanGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.RationalPolynomialBuffersGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialMonicCompanion

/-!
# Original rational bivariate evaluation and monic specialization

Both evaluations use the original rational Horner fold in each variable.
The monic specialization inserts the literal leading coefficient one.
The same rectangular coefficient matrix already used for rational row
span transports these computations to the original Gaussian evaluators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalBivariateGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarOne scalarZero)
open RationalPolynomialGaussianEmbedding (embed_congr evaluate hornerF)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries evaluation_transport)
open RationalRowSpanGaussianEmbedding (matrix matrix_shape matrix_lookup)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open GaussianRationalHorner (qzero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def valuesBody : PTm 2 := evaluate (entry (fstT (var 1)) (var 0)) (sndT (var 1))
def values (P R x : PTm n) : PTm n := sequence valuesBody R (pairT P x)
def monicCoefficient (P x i : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg i) scalarOne (evaluate (entry P (pred i)) x)
def monicBody : PTm 2 := monicCoefficient (fstT (var 1)) (sndT (var 1)) (var 0)
def monicValues (P R x : PTm n) : PTm n := sequence monicBody (succ R) (pairT P x)
def bivariate (P R x y : PTm n) : PTm n := evaluate (values P R x) y
def monic (P R x y : PTm n) : PTm n := evaluate (monicValues P R x) y

@[simp] theorem subst_values {l : ℕ} (σ : Fin n → PTm l) (P R x : PTm n) :
    Syn.subst σ (values P R x) = values (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ x) := by simp [values]
@[simp] theorem subst_monicCoefficient {l : ℕ} (σ : Fin n → PTm l) (P x i : PTm n) :
    Syn.subst σ (monicCoefficient P x i) = monicCoefficient (Syn.subst σ P) (Syn.subst σ x)
      (Syn.subst σ i) := by simp [monicCoefficient,Signum.sg]
@[simp] theorem subst_monicValues {l : ℕ} (σ : Fin n → PTm l) (P R x : PTm n) :
    Syn.subst σ (monicValues P R x) = monicValues (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [monicValues]
@[simp] theorem subst_bivariate {l : ℕ} (σ : Fin n → PTm l) (P R x y : PTm n) :
    Syn.subst σ (bivariate P R x y) = bivariate (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [bivariate]
@[simp] theorem subst_monic {l : ℕ} (σ : Fin n → PTm l) (P R x y : PTm n) :
    Syn.subst σ (monic P R x y) = monic (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [monic]

theorem evaluation_congr {P Q x y : PTm n} (hP : Γ ⊢[PRAAx] P ≐ Q) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] evaluate P x ≐ evaluate Q y :=
  congrAp3 hornerF (congrFst hP) hP hx

theorem values_length (P R x : PTm n) : Γ ⊢[PRAAx] length (values P R x) ≐ R := sequence_length _ _ _
theorem values_lookup (P R x i : PTm n) (hi : Γ ⊢[PRAAx] lt i R) :
    Γ ⊢[PRAAx] entry (values P R x) i ≐ evaluate (entry P i) x := by
  have actual := sequence_decode (Γ := Γ) valuesBody (x := pairT P x) hi
  simp only [valuesBody,inst2,RationalPolynomialGaussianEmbedding.subst_evaluate,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at actual
  exact actual.eqTrans (evaluation_congr (entry_congr (fst_pair P x) (.eqRefl _)) (snd_pair P x))

private theorem monic_body_at (P x i : PTm n) : Γ ⊢[PRAAx]
    inst2 monicBody i (pairT P x) ≐ monicCoefficient P x i := by
  simp only [monicBody,inst2,subst_monicCoefficient,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalMonicReconstruction.select_congr (.eqRefl _) (.eqRefl _)
    (evaluation_congr (entry_congr (fst_pair P x) (.eqRefl _)) (snd_pair P x))

theorem monic_length (P R x : PTm n) : Γ ⊢[PRAAx] length (monicValues P R x) ≐ succ R := sequence_length _ _ _
theorem monic_head (P R x : PTm n) : Γ ⊢[PRAAx] entry (monicValues P R x) zero ≐ scalarOne :=
  (sequence_decode monicBody (zero_lt_succ R)).eqTrans
    ((monic_body_at P x zero).eqTrans (RationalArithmetic.select_zero _ _ _ Signum.sg_zero))
theorem monic_tail (P R x i : PTm n) (hi : Γ ⊢[PRAAx] lt i R) :
    Γ ⊢[PRAAx] entry (monicValues P R x) (succ i) ≐ evaluate (entry P i) x :=
  (sequence_decode monicBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans
    ((monic_body_at P x (succ i)).eqTrans ((RationalArithmetic.select_one _ _ _ (Signum.sg_succ i)).eqTrans
      (evaluation_congr (entry_congr (.eqRefl _) (pred_succ _)) (.eqRefl _))))

theorem embedded_row_length (P R W i : PTm n) (hi : Γ ⊢[PRAAx] lt i R) :
    Γ ⊢[PRAAx] length (entry (matrix P R W) i) ≐ W := by
  have rule : Γ ⊢[PRAAx] lt i R ⟶ length (entry (matrix P R W) i) ≐ W :=
    by simpa using (Prf.andE₂ (matrix_shape P R W)).allE i
  exact .impE rule hi

theorem embedded_row_shape (P R c : PTm n) : Γ ⊢[PRAAx] rowShape (matrix P R (succ c)) R c := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,RationalRowSpanGaussianEmbedding.subst_matrix,ConciseIPRA.PTm.subst_succ] using
    embedded_row_length (Syn.shift P) (Syn.shift R) (succ (Syn.shift c)) (var 0) Prf.hyp0

theorem row_embedding (P R W i : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    embeddedEntries (entry P i) (entry (matrix P R W) i) W := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift R) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hi.shift
  simpa only [Syn.shift,subst_entry,RationalRowSpanGaussianEmbedding.subst_matrix,
    GaussianPolynomialDeterminantTerms.cell] using
    (matrix_lookup (Syn.shift P) (Syn.shift R) (Syn.shift W) (Syn.shift i) (var 0) hs.wk Prf.hyp0).eqSymm

theorem row_evaluation (P R c x i : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) (hi : Γ ⊢[PRAAx] lt i R) :
    Γ ⊢[PRAAx] embed (evaluate (entry P i) x) ≐
      GaussianRationalHorner.evaluate (entry (matrix P R (succ c)) i) (embed x) :=
  evaluation_transport _ _ _ _ (row_shape_at _ _ _ _ hp hi) (embedded_row_length _ _ _ _ hi)
    (row_embedding _ _ _ _ hi)

theorem value_embedding (P R c x : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) : Γ ⊢[PRAAx]
    embeddedEntries (values P R x) (GaussianPolynomialMonicCompanion.values (matrix P R (succ c)) R (embed x)) R := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have s : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift P) (Syn.shift R) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hp.shift
  have e := (embed_congr (values_lookup (Γ := Δ) (Syn.shift P) (Syn.shift R) (Syn.shift x) (var 0) Prf.hyp0)).eqTrans
    ((row_evaluation _ _ _ _ _ s.wk Prf.hyp0).eqTrans
      (GaussianPolynomialMonicCompanion.values_lookup _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,subst_values,GaussianPolynomialMonicCompanion.subst_values,
    RationalRowSpanGaussianEmbedding.subst_matrix,ConciseIPRA.PTm.subst_succ,RationalGaussianEmbedding.subst_embed] using e

theorem monic_value_at (P R c x i : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) (hi : Γ ⊢[PRAAx] lt i (succ R)) :
    Γ ⊢[PRAAx] embed (entry (monicValues P R x) i) ≐
      entry (GaussianPolynomialMonicCompanion.monicValues (matrix P R (succ c)) R (embed x)) i := by
  let C := monicValues P R x
  let D := GaussianPolynomialMonicCompanion.monicValues (matrix P R (succ c)) R (embed x)
  refine .orE (zero_or_succ i) ?_ ?_
  · exact (embed_congr ((entry_congr (.eqRefl C) Prf.hyp0).eqTrans (monic_head _ _ _))).eqTrans
      (RationalGaussianEmbedding.embed_one.eqTrans
        ((GaussianPolynomialMonicCompanion.monic_head _ _ _).eqSymm.eqTrans (entry_congr (.eqRefl D) Prf.hyp0).eqSymm))
  · let Δ := (i ≐ succ (pred i)) :: Γ
    have earlier : Δ ⊢[PRAAx] lt (pred i) R := (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (Prf.hyp0 : Δ ⊢[PRAAx] i ≐ succ (pred i)) (.eqRefl _) hi.wk)
    exact (embed_congr ((entry_congr (.eqRefl C) Prf.hyp0).eqTrans (monic_tail _ _ _ _ earlier))).eqTrans
      ((row_evaluation _ _ _ _ _ hp.wk earlier).eqTrans
        ((GaussianPolynomialMonicCompanion.monic_tail _ _ _ _ earlier).eqSymm.eqTrans
          (entry_congr (.eqRefl D) Prf.hyp0).eqSymm))

theorem monic_embedding (P R c x : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) : Γ ⊢[PRAAx]
    embeddedEntries (monicValues P R x)
      (GaussianPolynomialMonicCompanion.monicValues (matrix P R (succ c)) R (embed x)) (succ R) := by
  refine .allI (.impI ?_)
  have s : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift P) (Syn.shift R) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hp.shift
  simpa only [Syn.shift,subst_monicValues,GaussianPolynomialMonicCompanion.subst_monicValues,
    RationalRowSpanGaussianEmbedding.subst_matrix,ConciseIPRA.PTm.subst_succ,RationalGaussianEmbedding.subst_embed] using
    monic_value_at (Syn.shift P) (Syn.shift R) (Syn.shift c) (Syn.shift x) (var 0) s.wk Prf.hyp0

theorem bivariate_conjugacy (P R c x y : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) :
    Γ ⊢[PRAAx] embed (bivariate P R x y) ≐ GaussianRationalHorner.evaluate
      (GaussianPolynomialMonicCompanion.values (matrix P R (succ c)) R (embed x)) (embed y) :=
  evaluation_transport _ _ _ _ (values_length _ _ _) (GaussianPolynomialMonicCompanion.values_length _ _ _)
    (value_embedding _ _ _ _ hp)

theorem monic_conjugacy (P R c x y : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) :
    Γ ⊢[PRAAx] embed (monic P R x y) ≐ GaussianRationalHorner.evaluate
      (GaussianPolynomialMonicCompanion.monicValues (matrix P R (succ c)) R (embed x)) (embed y) :=
  evaluation_transport _ _ _ _ (monic_length _ _ _) (GaussianPolynomialMonicCompanion.monic_length _ _ _)
    (monic_embedding _ _ _ _ hp)

private theorem zero_transfer {u v : PTm n} (e : Γ ⊢[PRAAx] embed u ≐ v) : Γ ⊢[PRAAx]
    Fm.iff (RationalArgmin.rationalEq u scalarZero) (v ≐ qzero) :=
  .andI (.impI (e.wk.eqSymm.eqTrans ((RationalGaussianEmbedding.zero_iff u).iffMpr Prf.hyp0)))
    (.impI ((RationalGaussianEmbedding.zero_iff u).iffMp (e.wk.eqTrans Prf.hyp0)))

theorem bivariate_zero_iff (P R c x y : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) :
    Γ ⊢[PRAAx] Fm.iff (RationalArgmin.rationalEq (bivariate P R x y) scalarZero)
      (GaussianRationalHorner.evaluate
        (GaussianPolynomialMonicCompanion.values (matrix P R (succ c)) R (embed x)) (embed y) ≐ qzero) :=
  zero_transfer (bivariate_conjugacy P R c x y hp)

theorem monic_zero_iff (P R c x y : PTm n) (hp : Γ ⊢[PRAAx] rowShape P R c) :
    Γ ⊢[PRAAx] Fm.iff (RationalArgmin.rationalEq (monic P R x y) scalarZero)
      (GaussianRationalHorner.evaluate
        (GaussianPolynomialMonicCompanion.monicValues (matrix P R (succ c)) R (embed x)) (embed y) ≐ qzero) :=
  zero_transfer (monic_conjugacy P R c x y hp)

def bivariateF : PR 4 := PTm.toPR (bivariate (var 0) (var 1) (var 2) (var 3))
def monicF : PR 4 := PTm.toPR (monic (var 0) (var 1) (var 2) (var 3))

theorem bivariate_at (P R x y : PTm n) : Γ ⊢[PRAAx] PTm.app bivariateF ![P,R,x,y] ≐ bivariate P R x y := by
  simpa [bivariateF] using toPR_eq (Γ := Γ) (bivariate (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,R,x,y]
theorem monic_at (P R x y : PTm n) : Γ ⊢[PRAAx] PTm.app monicF ![P,R,x,y] ≐ monic P R x y := by
  simpa [monicF] using toPR_eq (Γ := Γ) (monic (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,R,x,y]

theorem actual_bivariate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app bivariateF ![var 0,var 1,var 2,var 3] ≐ bivariate (var 0) (var 1) (var 2) (var 3) ⋏
      PTm.app monicF ![var 0,var 1,var 2,var 3] ≐ monic (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.andI (bivariate_at _ _ _ _) (monic_at _ _ _ _))

theorem actual_rational_bivariate_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rowShape (var 0) (var 1) (var 2) ⟶
      embed (bivariate (var 0) (var 1) (var 3) (var 4)) ≐ GaussianRationalHorner.evaluate
        (GaussianPolynomialMonicCompanion.values (matrix (var 0) (var 1) (succ (var 2))) (var 1) (embed (var 3)))
        (embed (var 4))) :=
  closeUniv 5 (.impI (bivariate_conjugacy _ _ _ _ _ Prf.hyp0))

theorem actual_rational_monic_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rowShape (var 0) (var 1) (var 2) ⟶
      embed (monic (var 0) (var 1) (var 3) (var 4)) ≐ GaussianRationalHorner.evaluate
        (GaussianPolynomialMonicCompanion.monicValues (matrix (var 0) (var 1) (succ (var 2))) (var 1) (embed (var 3)))
        (embed (var 4))) :=
  closeUniv 5 (.impI (monic_conjugacy _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalBivariateGaussianEmbedding
