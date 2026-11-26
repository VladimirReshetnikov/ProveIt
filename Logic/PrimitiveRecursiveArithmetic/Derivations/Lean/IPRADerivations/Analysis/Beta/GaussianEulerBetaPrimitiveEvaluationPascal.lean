import IPRADerivations.Analysis.Beta.GaussianEulerBetaPrimitivePascal
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerPerturbation

/-!
# Literal Horner Pascal identity for the actual finite Beta primitive

The unchanged stored coefficient Pascal relation is transported through
the actual original Horner recursor. A genuine bounded atomic-QF prefix
invariant retains the one-cell offset between its two old buffers. The
last constant cell is proved separately. No evaluation or endpoint
recurrence is a premise, and all degrees and raw query codes are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaPrimitiveEvaluationPascal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerBetaPolynomialPrimitive (primitive primitive_length primitive_entry_canonical)
open GaussianEulerBetaPrimitivePascal (primitiveReader primitive_reader_Pascal primitive_constant_Pascal)
open GaussianRationalHorner (qzero qmul qadd horner evaluate canonical)
open GaussianRationalMetric (qnegative qsub)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr)
open GaussianRationalReciprocal (qone)
open GaussianRationalLowCoefficientConvolution (exponent_inside)
open GaussianGammaEulerHeadShift (shifted)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem reader_leading (z B N : PTm n) : Γ ⊢[PRAAx] primitiveReader z B N N ≐ entry (primitive z B N) zero :=
  (exponent_inside _ _ _ (le_refl N)).eqTrans (entry_congr (.eqRefl _) (monus_self N))

theorem leading_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    entry (primitive z B (succ N)) zero ≐ qnegative (entry (primitive (shifted z B) B N) zero) :=
  (reader_leading z B (succ N)).eqSymm.eqTrans
    ((primitive_reader_Pascal z B N N hB).eqTrans
      ((qsub_congr (GaussianRationalLowCoefficientConvolution.exponent_outside _ _ _ (le_refl (succ N)))
        (reader_leading (shifted z B) B N)).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _))))

theorem interior_step (z B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hr : Γ ⊢[PRAAx] le (succ r) N) : Γ ⊢[PRAAx]
    entry (primitive z B (succ N)) (succ r) ≐ qsub (entry (primitive z B N) r) (entry (primitive (shifted z B) B N) (succ r)) := by
  let e := monus N (succ r)
  have idx := GaussianEulerBetaPrimitivePascal.index_before N r hr
  have bound : Γ ⊢[PRAAx] le (succ e) N := le_congr idx (.eqRefl _) (GaussianRationalMonicReconstruction.monus_le_left N r)
  have high : Γ ⊢[PRAAx] primitiveReader z B N (succ e) ≐ entry (primitive z B N) r :=
    (exponent_inside _ _ _ bound).eqTrans
      (entry_congr (.eqRefl _) ((congrMonus (.eqRefl N) idx.eqSymm).eqTrans
        (GaussianRationalMonicReconstruction.complement N r (le_trans (le_succ_self r) hr))))
  have low : Γ ⊢[PRAAx] primitiveReader (shifted z B) B N e ≐ entry (primitive (shifted z B) B N) (succ r) :=
    (exponent_inside _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      (entry_congr (.eqRefl _) (GaussianRationalMonicReconstruction.complement N (succ r) hr))
  have next : Γ ⊢[PRAAx] primitiveReader z B (succ N) (succ e) ≐ entry (primitive z B (succ N)) (succ r) :=
    (exponent_inside _ _ _ (le_trans bound (le_succ_self N))).eqTrans
      (entry_congr (.eqRefl _) ((succ_monus_succ N e).eqTrans (GaussianRationalMonicReconstruction.complement N (succ r) hr)))
  exact next.eqSymm.eqTrans ((primitive_reader_Pascal z B N e hB).eqTrans (qsub_congr high low))

theorem constant_step (z B N : PTm n) : Γ ⊢[PRAAx]
    entry (primitive z B (succ N)) (succ N) ≐ entry (primitive z B N) N := by
  have next : Γ ⊢[PRAAx] primitiveReader z B (succ N) zero ≐ entry (primitive z B (succ N)) (succ N) :=
    (exponent_inside _ _ _ (zero_le _)).eqTrans (entry_congr (.eqRefl _) (monus_zero _))
  have old : Γ ⊢[PRAAx] primitiveReader z B N zero ≐ entry (primitive z B N) N :=
    (exponent_inside _ _ _ (zero_le _)).eqTrans (entry_congr (.eqRefl _) (monus_zero _))
  exact next.eqSymm.eqTrans ((primitive_constant_Pascal z B N).eqTrans old)

theorem horner_first (C t : PTm n) (hc : Γ ⊢[PRAAx] canonical (entry C zero)) : Γ ⊢[PRAAx] horner C t one ≐ entry C zero :=
  (GaussianRationalHorner.horner_succ C t zero).eqTrans
    ((qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero C t) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left t)) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ hc))

def prefixLaw (z B N t i : PTm n) : Fm PTm n := le i N ⟶
  horner (primitive z B (succ N)) t (succ i) ≐
    qsub (horner (primitive z B N) t i) (horner (primitive (shifted z B) B N) t (succ i))
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (z B N t i : PTm n) :
    (prefixLaw z B N t i).subst σ = prefixLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ i) := by simp [prefixLaw]

theorem prefix_zero (z B N t : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    horner (primitive z B (succ N)) t one ≐ qsub (horner (primitive z B N) t zero) (horner (primitive (shifted z B) B N) t one) := by
  have left := (horner_first _ t (primitive_entry_canonical z B (succ N) zero (zero_le _))).eqTrans (leading_step z B N hB)
  have right : Γ ⊢[PRAAx] qsub (horner (primitive z B N) t zero) (horner (primitive (shifted z B) B N) t one) ≐
      qnegative (entry (primitive (shifted z B) B N) zero) := (qsub_congr (GaussianRationalHorner.horner_zero (primitive z B N) t)
    (horner_first _ t (primitive_entry_canonical (shifted z B) B N zero (zero_le _)))).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _))
  exact left.eqTrans right.eqSymm

theorem prefix_step (z B N t i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le (succ i) N)
    (ih : Γ ⊢[PRAAx] horner (primitive z B (succ N)) t (succ i) ≐
      qsub (horner (primitive z B N) t i) (horner (primitive (shifted z B) B N) t (succ i))) : Γ ⊢[PRAAx]
    horner (primitive z B (succ N)) t (succ (succ i)) ≐
      qsub (horner (primitive z B N) t (succ i)) (horner (primitive (shifted z B) B N) t (succ (succ i))) :=
  (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr (qmul_congr ih (.eqRefl _)) (interior_step z B N i hB hi)).eqTrans
      ((GaussianRationalHornerPerturbation.affine_difference _ _ _ _ _).eqSymm.eqTrans
        (qsub_congr (GaussianRationalHorner.horner_succ _ _ _).eqSymm (GaussianRationalHorner.horner_succ _ _ _).eqSymm)))

theorem horner_prefix (z B N t i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    horner (primitive z B (succ N)) t (succ i) ≐
      qsub (horner (primitive z B N) t i) (horner (primitive (shifted z B) B N) t (succ i)) := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift t) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero z B N t hB).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let IH := prefixLaw (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift t) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      exact prefix_step _ _ _ _ _ bs.wk.wk Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw z B N t i := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

theorem negative_zero : Γ ⊢[PRAAx] qnegative (qzero : PTm n) ≐ qzero :=
  (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)).eqSymm.eqTrans (GaussianCoefficientNormOrder.qsub_self qzero)
theorem sub_zero (a : PTm n) (ha : Γ ⊢[PRAAx] canonical a) : Γ ⊢[PRAAx] qsub a qzero ≐ a :=
  (qadd_congr (.eqRefl _) negative_zero).eqTrans (GaussianReciprocalHorner.qadd_zero_right a ha)

def value (z B N : PTm n) : PTm n := evaluate (primitive z B N) qone
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (value z B N) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [value]

/-- Literal original Horner evaluation, for any raw query code t. -/
theorem evaluation_Pascal (z B N t : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (primitive z B (succ N)) t ≐ qsub (evaluate (primitive z B N) t) (qmul (evaluate (primitive (shifted z B) B N) t) t) := by
  let P := primitive z B N
  let Q := primitive (shifted z B) B N
  have affine := GaussianRationalHornerPerturbation.affine_difference (Γ := Γ) (horner P t N) (horner Q t (succ N)) (entry P N) qzero t
  have clear : Γ ⊢[PRAAx] qsub (qadd (qmul (horner P t N) t) (entry P N)) (qmul (horner Q t (succ N)) t) ≐
      qadd (qmul (qsub (horner P t N) (horner Q t (succ N))) t) (entry P N) :=
    (qsub_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)).eqSymm).eqTrans
      (affine.eqTrans (qadd_congr (.eqRefl _) (sub_zero _ (primitive_entry_canonical z B N N (le_refl N)))))
  exact (congrAp3 GaussianRationalHorner.hornerF (primitive_length z B (succ N)) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
      ((qadd_congr (qmul_congr (horner_prefix z B N t N hB (le_refl N)) (.eqRefl _)) (constant_step z B N)).eqTrans
        (clear.eqSymm.eqTrans (qsub_congr
          ((GaussianRationalHorner.horner_succ P t N).eqSymm.eqTrans (congrAp3 GaussianRationalHorner.hornerF (primitive_length z B N).eqSymm (.eqRefl _) (.eqRefl _)))
          (qmul_congr (congrAp3 GaussianRationalHorner.hornerF (primitive_length (shifted z B) B N).eqSymm (.eqRefl _) (.eqRefl _)) (.eqRefl _))))))

theorem endpoint_Pascal (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    value z B (succ N) ≐ qsub (value z B N) (value (shifted z B) B N) :=
  (evaluation_Pascal z B N qone hB).eqTrans
    (qsub_congr (.eqRefl _) (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)))

def output (z B N t : PTm n) : PTm n := pairT (evaluate (primitive z B (succ N)) t)
  (pairT (qsub (evaluate (primitive z B N) t) (qmul (evaluate (primitive (shifted z B) B N) t) t))
    (pairT (value z B (succ N)) (qsub (value z B N) (value (shifted z B) B N))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z B N t : PTm n) : PTm n := PTm.app outputF ![z,B,N,t]
theorem program_at (z B N t : PTm n) : Γ ⊢[PRAAx] run z B N t ≐ output z B N t := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,B,N,t]

theorem actual_Beta_primitive_storage_Pascal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le (succ (var 3)) (var 2)) ⟶
      entry (primitive (var 0) (var 1) (succ (var 2))) (succ (var 3)) ≐
        qsub (entry (primitive (var 0) (var 1) (var 2)) (var 3))
          (entry (primitive (shifted (var 0) (var 1)) (var 1) (var 2)) (succ (var 3)))) :=
  closeUniv 4 (.impI (interior_step _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_Beta_primitive_Horner_prefix_Pascal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 1) ⋏ le (var 4) (var 2)) ⟶
      horner (primitive (var 0) (var 1) (succ (var 2))) (var 3) (succ (var 4)) ≐
        qsub (horner (primitive (var 0) (var 1) (var 2)) (var 3) (var 4))
          (horner (primitive (shifted (var 0) (var 1)) (var 1) (var 2)) (var 3) (succ (var 4)))) :=
  closeUniv 5 (.impI (horner_prefix _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_Beta_primitive_literal_evaluation_Pascal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ evaluate (primitive (var 0) (var 1) (succ (var 2))) (var 3) ≐
      qsub (evaluate (primitive (var 0) (var 1) (var 2)) (var 3))
        (qmul (evaluate (primitive (shifted (var 0) (var 1)) (var 1) (var 2)) (var 3)) (var 3))) :=
  closeUniv 4 (.impI (evaluation_Pascal _ _ _ _ Prf.hyp0))
theorem actual_Beta_primitive_endpoint_Pascal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ value (var 0) (var 1) (succ (var 2)) ≐
      qsub (value (var 0) (var 1) (var 2)) (value (shifted (var 0) (var 1)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (endpoint_Pascal _ _ _ Prf.hyp0))
theorem actual_Beta_primitive_evaluation_Pascal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerBetaPrimitiveEvaluationPascal
