import IPRADerivations.Analysis.Polynomials.Horner.RationalPolynomialMonicHornerReductionGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Translation.RationalPolynomialYShiftGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Horner.GaussianPolynomialMonicHornerQuotient
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual original rational polynomial-valued monic quotient

The actual quotient recursor multiplies its stored original rational rows
by Y and adds the top row of the SAME actual rational remainder. A bounded
QF coefficient invariant derives transport to the checked Gaussian quotient.
Original rational all-query Horner reconstruction is then obtained from the
actual operations; no quotient/evaluation/output law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialMonicHornerQuotientGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open RationalPolynomialMonicHornerReductionGaussianEmbedding (width zeroRows data data_fields stage stage_computed_shape input originalValue remainder)
open RationalPolynomialConstantInjectionGaussianEmbedding (inject fields)
open RationalPolynomialYShiftGaussianEmbedding (shiftY shift_shape shift_rows_embedded)
open RationalPolynomialMultiplicationMatrixGaussianEmbedding (pairedRows paired_rows_congr rowShapeSyntax rowsEmbeddedSyntax)
open RationalPolynomialMonicCompanionGaussianEmbedding (rowsEmbedded row_embedded_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def advance (F H m a c j Q : PTm n) : PTm n :=
  inject (shiftY Q (succ j) (width a c j) c) (entry (stage F H m a c j) zero) (succ (succ j)) (width a c j) c

def initial : PTm 1 := zeroRows one (fields (var 0) 3)
def stepBody : PTm 3 := advance (fields (var 2) 0) (fields (var 2) 1) (fields (var 2) 2)
  (fields (var 2) 3) (fields (var 2) 4) (var 0) (var 1)
def quotientF : PR 2 := rec2 initial stepBody
def quotient (F H m a c j : PTm n) : PTm n := ap2 quotientF j (data F H m a c)

@[simp] theorem subst_advance {k : ℕ} (σ : Fin n → PTm k) (F H m a c j Q : PTm n) :
    Syn.subst σ (advance F H m a c j Q) = advance (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) (Syn.subst σ Q) := by simp [advance]
@[simp] theorem subst_quotient {k : ℕ} (σ : Fin n → PTm k) (F H m a c j : PTm n) :
    Syn.subst σ (quotient F H m a c j) = quotient (Syn.subst σ F) (Syn.subst σ H)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [quotient]

theorem advance_parameters (p : PTm n) (F H m a c j Q : PTm n)
    (h : ∀ i : Fin 5, Γ ⊢[PRAAx] fields p i ≐ ![F,H,m,a,c] i) :
    Γ ⊢[PRAAx] advance (fields p 0) (fields p 1) (fields p 2) (fields p 3) (fields p 4) j Q ≐ advance F H m a c j Q := by
  ipra_congr (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) with
    [h 0, h 1, h 2, h 3, h 4, .eqRefl j, .eqRefl Q]

theorem quotient_zero (F H m a c : PTm n) : Γ ⊢[PRAAx] quotient F H m a c zero ≐ zeroRows one a := by
  have base := rec2_zero (Γ := Γ) initial stepBody (data F H m a c)
  simp only [initial,RationalPolynomialMonicHornerReductionGaussianEmbedding.subst_zeroRows,
    RationalPolynomialConstantInjectionGaussianEmbedding.subst_fields,Syn.subst_var,
    one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] at base
  have widthField : Γ ⊢[PRAAx] fields (data F H m a c) 3 ≐ a := by simpa using data_fields F H m a c 3
  have e : Γ ⊢[PRAAx] zeroRows one (fields (data F H m a c) 3) ≐ zeroRows one a := by
    ipra_congr (zeroRows one (var 0) : PTm 1) with [widthField]
  exact base.eqTrans e

theorem quotient_succ (F H m a c j : PTm n) : Γ ⊢[PRAAx]
    quotient F H m a c (succ j) ≐ advance F H m a c j (quotient F H m a c j) := by
  have e := rec2_succ (Γ := Γ) initial stepBody j (data F H m a c)
  simp only [stepBody,subst_advance,RationalPolynomialConstantInjectionGaussianEmbedding.subst_fields,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  exact e.eqTrans (advance_parameters _ _ _ _ _ _ _ _ (data_fields F H m a c))

def targetQuotient (F H m a c L j : PTm n) : PTm n := GaussianPolynomialMonicHornerQuotient.quotient
  (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix H L (succ a)) m a c j
@[simp] theorem subst_targetQuotient {k : ℕ} (σ : Fin n → PTm k) (F H m a c L j : PTm n) :
    Syn.subst σ (targetQuotient F H m a c L j) = targetQuotient (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ j) := by simp [targetQuotient]

def profile (F H m a c L j : PTm n) : Fm PTm n := le j L ⟶
  pairedRows (quotient F H m a c j) (targetQuotient F H m a c L j) (succ j) (width a c j)
@[simp] theorem subst_profile {k : ℕ} (σ : Fin n → PTm k) (F H m a c L j : PTm n) :
    (profile F H m a c L j).subst σ = profile (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ j) := by simp [profile]

theorem profile_base (F H m a c L : PTm n) : Γ ⊢[PRAAx] profile F H m a c L zero := by
  refine .impI ?_
  exact paired_rows_congr (quotient_zero _ _ _ _ _).eqSymm (GaussianPolynomialMonicHornerQuotient.quotient_zero _ _ _ _ _).eqSymm
    (by unfold width; ipra_ring) (RationalPolynomialMonicHornerReductionGaussianEmbedding.zero_rows_profile one a)

theorem profile_step (F H m a c L j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a)
    (ih : Γ ⊢[PRAAx] profile F H m a c L j) : Γ ⊢[PRAAx] profile F H m a c L (succ j) := by
  refine .impI ?_
  let Δ := le (succ j) L :: Γ
  have prior : Δ ⊢[PRAAx] le j L := le_trans (le_succ_self _) Prf.hyp0
  have before : Δ ⊢[PRAAx] pairedRows (quotient F H m a c j) (targetQuotient F H m a c L j) (succ j) (width a c j) := .impE ih.wk prior
  have targetShape : Δ ⊢[PRAAx] rowShape (targetQuotient F H m a c L j) (succ j) (width a c j) :=
    .andE₁ (.andE₂ (GaussianPolynomialMonicHornerQuotient.quotient_stored _ _ _ _ _ _))
  have shifts := shift_rows_embedded (quotient F H m a c j) (targetQuotient F H m a c L j) (succ j) (width a c j) c
    (.andE₁ before) targetShape (.andE₂ before)
  have rprior := RationalPolynomialMonicHornerReductionGaussianEmbedding.stage_profile F H m a c L j hm.wk hF.wk hH.wk prior
  have originalTop : Δ ⊢[PRAAx] length (entry (stage F H m a c j) zero) ≐ succ (width a c j) :=
    row_shape_at _ _ _ _ (.andE₁ rprior) hm.wk
  have targetTop : Δ ⊢[PRAAx] length (entry (RationalPolynomialMonicHornerReductionGaussianEmbedding.targetStage F H m a c L j) zero) ≐ succ (width a c j) :=
    row_shape_at _ _ _ _ (GaussianPolynomialMonicHornerReduction.stage_shape _ _ _ _ _ _) hm.wk
  have topEntries := row_embedded_at _ _ _ _ _ (.andE₂ rprior) hm.wk
  have out := RationalPolynomialConstantInjectionGaussianEmbedding.inject_rows_embedded
    (shiftY (quotient F H m a c j) (succ j) (width a c j) c)
    (GaussianPolynomialYShift.shiftY (targetQuotient F H m a c L j) (succ j) (width a c j) c)
    (entry (stage F H m a c j) zero) (entry (RationalPolynomialMonicHornerReductionGaussianEmbedding.targetStage F H m a c L j) zero)
    (succ (succ j)) (width a c j) c originalTop targetTop shifts topEntries
  exact paired_rows_congr (quotient_succ _ _ _ _ _ _).eqSymm (GaussianPolynomialMonicHornerQuotient.quotient_succ _ _ _ _ _ _).eqSymm
    (by unfold width; ipra_ring) (.andI (RationalPolynomialConstantInjectionGaussianEmbedding.inject_shape _ _ _ _ _) out)

def profileSyntax (F H m a c L j : PTm n) : BFm n := .imp (.le j L) (.and
  (rowShapeSyntax (quotient F H m a c j) (succ j) (width a c j))
  (rowsEmbeddedSyntax (quotient F H m a c j) (targetQuotient F H m a c L j) (succ j) (width a c j)))
theorem profile_formula (F H m a c L j : PTm n) : formula (profileSyntax F H m a c L j) = profile F H m a c L j := rfl

theorem quotient_profile (F H m a c L j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    pairedRows (quotient F H m a c j) (targetQuotient F H m a c L j) (succ j) (width a c j) := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hF.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (Syn.shift L) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hH.shift
  let S := profileSyntax (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift L) (var 0)
  have all : Γ ⊢[PRAAx] .all (profile (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift L) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,profile_formula,subst_profile,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact profile_base _ _ _ _ _ _
    · simp only [S,profile_formula,subst_profile,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact profile_step _ _ _ _ _ _ _ ms.wk fs.wk hs.wk Prf.hyp0
  have p : Γ ⊢[PRAAx] profile F H m a c L j := by
    simpa only [subst_profile,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE p hj

theorem quotient_evaluation_conjugacy (F H m a c L j x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    embed (RationalBivariateGaussianEmbedding.bivariate (quotient F H m a c j) (succ j) x y) ≐
      GaussianPolynomialMonicHornerQuotient.qvalue (RationalRowSpanGaussianEmbedding.matrix F m (succ c))
        (RationalRowSpanGaussianEmbedding.matrix H L (succ a)) m a c j (embed x) (embed y) := by
  have qp := quotient_profile F H m a c L j hm hF hH hj
  exact RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport _ _ _ _ _ _
    (.andE₁ qp) (.andE₁ (.andE₂ (GaussianPolynomialMonicHornerQuotient.quotient_stored _ _ _ _ _ _))) (.andE₂ qp)

theorem remainder_evaluation_conjugacy (F H m a c L j x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    embed (RationalBivariateGaussianEmbedding.bivariate (stage F H m a c j) m x y) ≐
      GaussianPolynomialMonicHornerQuotient.rvalue (RationalRowSpanGaussianEmbedding.matrix F m (succ c))
        (RationalRowSpanGaussianEmbedding.matrix H L (succ a)) m a c j (embed x) (embed y) := by
  have rp := RationalPolynomialMonicHornerReductionGaussianEmbedding.stage_profile F H m a c L j hm hF hH hj
  exact RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport _ _ _ _ _ _
    (.andE₁ rp) (GaussianPolynomialMonicHornerReduction.stage_shape _ _ _ _ _ _) (.andE₂ rp)

def finalQuotient (F H m a c N : PTm n) : PTm n := quotient F H m a c (succ N)
@[simp] theorem subst_finalQuotient {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    Syn.subst σ (finalQuotient F H m a c N) = finalQuotient (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by simp [finalQuotient]

theorem reconstruction (F H m a c N x y : PTm n)
    (h : Γ ⊢[PRAAx] RationalPolynomialMonicHornerReductionGaussianEmbedding.input F H m a c N) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate H (succ N) x y ≐ RationalArithmetic.add
      (RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic F m x y)
        (RationalBivariateGaussianEmbedding.bivariate (finalQuotient F H m a c N) (succ (succ N)) x y))
      (RationalBivariateGaussianEmbedding.bivariate (RationalPolynomialMonicHornerReductionGaussianEmbedding.remainder F H m a c N) m x y) := by
  have hm := Prf.andE₁ h
  have hF := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hH := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have qtransport := quotient_evaluation_conjugacy F H m a c (succ N) (succ N) x y hm hF hH (le_refl _)
  have rtransport := remainder_evaluation_conjugacy F H m a c (succ N) (succ N) x y hm hF hH (le_refl _)
  have ftransport := RationalBivariateGaussianEmbedding.monic_conjugacy F m c x y hF
  have original := RationalBivariateGaussianEmbedding.bivariate_conjugacy H (succ N) a x y hH
  have reconstruct := GaussianPolynomialMonicHornerQuotient.prefix_reconstruction
    (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix H (succ N) (succ a))
    m a c (succ N) (embed x) (embed y) (succ N) hm
    (RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _)
    (RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _) (le_refl _)
  have old := original.eqTrans ((congrAp3 GaussianRationalHorner.hornerF (GaussianPolynomialMonicCompanion.values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans reconstruct)
  have rhs := (RationalGaussianEmbedding.embed_add _ _).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr
      ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr ftransport qtransport)) rtransport)
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.add_guard _ _) (old.eqTrans rhs.eqSymm)

theorem original_reconstruction (F H m a c N x y : PTm n)
    (h : Γ ⊢[PRAAx] RationalPolynomialMonicHornerReductionGaussianEmbedding.input F H m a c N) : Γ ⊢[PRAAx]
    RationalPolynomialMonicHornerReductionGaussianEmbedding.originalValue H x y ≐ RationalArithmetic.add
      (RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic F m x y)
        (RationalBivariateGaussianEmbedding.bivariate (finalQuotient F H m a c N) (succ (succ N)) x y))
      (RationalBivariateGaussianEmbedding.bivariate (RationalPolynomialMonicHornerReductionGaussianEmbedding.remainder F H m a c N) m x y) := by
  have hLen : Γ ⊢[PRAAx] length H ≐ succ N := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact (RationalPolynomialMonicHornerReductionGaussianEmbedding.bivariate_count_congr _ _ _ _ _ hLen).eqTrans
    (reconstruction _ _ _ _ _ _ _ _ h)

theorem quotient_length (F H m a c j : PTm n) : Γ ⊢[PRAAx] length (quotient F H m a c j) ≐ succ j := by
  have all : Γ ⊢[PRAAx] .all (length (quotient (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)) ≐ succ (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,Foundations.SequenceComposition.subst_length,subst_quotient,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (quotient_zero _ _ _ _ _)).eqTrans (RationalPolynomialMonicHornerReductionGaussianEmbedding.zero_rows_length _ _)
    · simp only [Fm.subst_eq,Foundations.SequenceComposition.subst_length,subst_quotient,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (quotient_succ _ _ _ _ _ _)).eqTrans (RationalPolynomialConstantInjectionGaussianEmbedding.inject_length _ _ _ _ _)
  simpa only [Fm.subst_eq,Foundations.SequenceComposition.subst_length,subst_quotient,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def computedShapeSyntax (F H m a c j : PTm n) : BFm n := rowShapeSyntax (quotient F H m a c j) (succ j) (width a c j)
theorem computed_shape_formula (F H m a c j : PTm n) : formula (computedShapeSyntax F H m a c j) = rowShape (quotient F H m a c j) (succ j) (width a c j) := rfl
theorem quotient_computed_shape (F H m a c j : PTm n) : Γ ⊢[PRAAx] rowShape (quotient F H m a c j) (succ j) (width a c j) := by
  let S := computedShapeSyntax (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)
  have all : Γ ⊢[PRAAx] .all (formula S) := by
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,computed_shape_formula,GaussianPolynomialMonicCompanion.subst_rowShape,subst_quotient,RationalPolynomialMonicHornerReductionGaussianEmbedding.subst_width,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact RationalPolynomialMonicHornerReductionGaussianEmbedding.row_shape_congr
        (quotient_zero _ _ _ _ _).eqSymm (.eqRefl _) (by unfold width; ipra_ring)
        (.andE₁ (RationalPolynomialMonicHornerReductionGaussianEmbedding.zero_rows_profile _ _))
    · simp only [S,computed_shape_formula,GaussianPolynomialMonicCompanion.subst_rowShape,subst_quotient,RationalPolynomialMonicHornerReductionGaussianEmbedding.subst_width,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact RationalPolynomialMonicHornerReductionGaussianEmbedding.row_shape_congr
        (quotient_succ _ _ _ _ _ _).eqSymm (.eqRefl _) (by unfold width; ipra_ring)
        (RationalPolynomialConstantInjectionGaussianEmbedding.inject_shape _ _ _ _ _)
  simpa only [S,computed_shape_formula,GaussianPolynomialMonicCompanion.subst_rowShape,subst_quotient,RationalPolynomialMonicHornerReductionGaussianEmbedding.subst_width,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem final_quotient_coefficient (F H m a c N r s : PTm n)
    (h : Γ ⊢[PRAAx] RationalPolynomialMonicHornerReductionGaussianEmbedding.input F H m a c N)
    (hr : Γ ⊢[PRAAx] lt r (succ (succ N))) (hs : Γ ⊢[PRAAx] le s (width a c (succ N))) : Γ ⊢[PRAAx]
    embed (entry (entry (finalQuotient F H m a c N) r) s) ≐ entry (entry (targetQuotient F H m a c (succ N) (succ N)) r) s :=
  RationalPolynomialMonicCompanionGaussianEmbedding.embedded_at _ _ _ _
    (row_embedded_at _ _ _ _ _ (.andE₂ (quotient_profile _ _ _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ (.andE₂ h)))
      (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))) (le_refl _))) hr) ((succ_monus_succ _ _).eqTrans hs)

theorem final_quotient_well_formed (F H m a c N r s : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (succ (succ N))) (hs : Γ ⊢[PRAAx] le s (width a c (succ N))) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (finalQuotient F H m a c N) r) s) := by
  have bound : Γ ⊢[PRAAx] le s (width a c N+c) := le_congr (.eqRefl _) (by unfold width; ipra_ring) hs
  have e := (Foundations.SequenceComposition.entry_congr
    (Foundations.SequenceComposition.entry_congr (quotient_succ F H m a c N) (.eqRefl r)) (.eqRefl s)).eqTrans
      (RationalPolynomialConstantInjectionGaussianEmbedding.coefficient_lookup _ _ _ _ _ _ _ hr bound)
  exact RationalArithmetic.guard_congr e (RationalArithmetic.add_guard _ _)

def output (F H m a c N : PTm n) : PTm n := pairT (finalQuotient F H m a c N)
  (RationalPolynomialMonicHornerReductionGaussianEmbedding.remainder F H m a c N)
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (F H m a c N : PTm n) : PTm n := PTm.app outputF ![F,H,m,a,c,N]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    Syn.subst σ (output F H m a c N) = output (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    Syn.subst σ (run F H m a c N) = run (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (F H m a c N : PTm n) : Γ ⊢[PRAAx] run F H m a c N ≐ output F H m a c N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,H,m,a,c,N]
theorem returned_quotient (F H m a c N : PTm n) : Γ ⊢[PRAAx] fstT (run F H m a c N) ≐ finalQuotient F H m a c N :=
  (congrFst (program_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_remainder (F H m a c N : PTm n) : Γ ⊢[PRAAx] sndT (run F H m a c N) ≐
    RationalPolynomialMonicHornerReductionGaussianEmbedding.remainder F H m a c N :=
  (congrSnd (program_at _ _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_reconstruction (F H m a c N x y : PTm n)
    (h : Γ ⊢[PRAAx] RationalPolynomialMonicHornerReductionGaussianEmbedding.input F H m a c N) : Γ ⊢[PRAAx]
    RationalPolynomialMonicHornerReductionGaussianEmbedding.originalValue H x y ≐ RationalArithmetic.add
      (RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic F m x y)
        (RationalBivariateGaussianEmbedding.bivariate (fstT (run F H m a c N)) (succ (succ N)) x y))
      (RationalBivariateGaussianEmbedding.bivariate (sndT (run F H m a c N)) m x y) :=
  (original_reconstruction _ _ _ _ _ _ _ _ h).eqTrans
    (RationalAlgebra.add_congr (RationalAlgebra.multiply_congr (.eqRefl _)
      (RationalPolynomialMonicHornerReductionGaussianEmbedding.bivariate_code_congr _ _ _ _ _ (returned_quotient _ _ _ _ _ _)).eqSymm)
      (RationalPolynomialMonicHornerReductionGaussianEmbedding.bivariate_code_congr _ _ _ _ _ (returned_remainder _ _ _ _ _ _)).eqSymm)

theorem actual_rational_quotient_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (quotient (var 0) (var 1) (var 2) (var 3) (var 4) zero ≐ zeroRows one (var 3) ⋏
      quotient (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) ≐ advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
        (quotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.andI (quotient_zero _ _ _ _ _) (quotient_succ _ _ _ _ _ _))
theorem actual_rational_quotient_profile_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 5) (var 3) ⟶ le (var 6) (var 5) ⟶
      pairedRows (quotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))
        (targetQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (succ (var 6)) (width (var 3) (var 4) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (quotient_profile _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_rational_quotient_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (quotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ succ (var 5) ⋏
      rowShape (quotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 5)) (width (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.andI (quotient_length _ _ _ _ _ _) (quotient_computed_shape _ _ _ _ _ _))
theorem actual_rational_quotient_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ lt (var 6) (succ (succ (var 5))) ⟶ le (var 7) (width (var 3) (var 4) (succ (var 5))) ⟶
      embed (entry (entry (finalQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7)) ≐
        entry (entry (targetQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (succ (var 5))) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (final_quotient_coefficient _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_quotient_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (lt (var 6) (succ (succ (var 5))) ⟶ le (var 7) (width (var 3) (var 4) (succ (var 5))) ⟶
      RationalNormalForm.wellFormed (entry (entry (finalQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7))) :=
  closeUniv 8 (.impI (.impI (final_quotient_well_formed _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_horner_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      originalValue (var 1) (var 6) (var 7) ≐ RationalArithmetic.add
        (RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic (var 0) (var 2) (var 6) (var 7))
          (RationalBivariateGaussianEmbedding.bivariate (finalQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
            (succ (succ (var 5))) (var 6) (var 7)))
        (RationalBivariateGaussianEmbedding.bivariate (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6) (var 7))) :=
  closeUniv 8 (.impI (original_reconstruction _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_division_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_rational_returned_division_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ finalQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
      (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
        (length (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ succ (succ (var 5)) ⋏
          length (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ var 2))) :=
  closeUniv 6 (.andI (returned_quotient _ _ _ _ _ _) (.andI (returned_remainder _ _ _ _ _ _)
    (.andI ((congrFst (returned_quotient _ _ _ _ _ _)).eqTrans (quotient_length _ _ _ _ _ _))
      ((congrFst (returned_remainder _ _ _ _ _ _)).eqTrans (RationalPolynomialMonicHornerReductionGaussianEmbedding.remainder_length _ _ _ _ _ _)))))
theorem actual_rational_returned_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      originalValue (var 1) (var 6) (var 7) ≐ RationalArithmetic.add
        (RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic (var 0) (var 2) (var 6) (var 7))
          (RationalBivariateGaussianEmbedding.bivariate (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
            (succ (succ (var 5))) (var 6) (var 7)))
        (RationalBivariateGaussianEmbedding.bivariate (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) (var 2) (var 6) (var 7))) :=
  closeUniv 8 (.impI (returned_reconstruction _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialMonicHornerQuotientGaussianEmbedding
