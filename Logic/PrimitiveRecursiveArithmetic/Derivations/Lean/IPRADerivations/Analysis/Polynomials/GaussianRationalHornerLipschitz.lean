import IPRADerivations.Analysis.Polynomials.GaussianRationalHornerPerturbation
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianEuclideanResidualRadius
import IPRADerivations.AnalyticNumberTheory.GoldbachGeometric
import IPRADerivations.Core.LinearCombination

/-!
# Exact runtime Lipschitz bounds for original rational Horner evaluation

The constant is the actual weighted power sum A sum_(i<N) (i+1) U^i.
Actual prefix-size bounds and the actual Horner difference recurrence are
proved using original Euclidean coefficient bounds, exact rational triangle
and product estimates, and QF induction. No derivative, power-difference,
evaluation or Lipschitz identity is supplied. All numerical data are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHornerLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul represents qadd_represents qmul_represents represents_rescale represents_congr canonical_unique
    positive_product horner evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_represents bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr qsub_congr rescale_to remainingDen remaining_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr bounded_product)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation (bounded_sum_same_den)
open LeanProofs.IPRA.Analysis.GaussianEuclideanResidualRadius (coefficientBounds coefficient_at)
open LeanProofs.IPRA.AnalyticNumberTheory.GoldbachGeometric (gB inst2_gB)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def geometric (U k : PTm n) : PTm n := ap2 (sumF gB) k U
def weightedBody : PTm 2 := succ (var 0)*pw (var 1) (var 0)
def weighted (U k : PTm n) : PTm n := ap2 (sumF weightedBody) k U
def constant (N U A : PTm n) : PTm n := A*weighted U N

@[simp] theorem subst_geometric {m : ℕ} (σ : Fin n → PTm m) (U k : PTm n) :
    Syn.subst σ (geometric U k) = geometric (Syn.subst σ U) (Syn.subst σ k) := by simp only [geometric,subst_ap2]
@[simp] theorem subst_weighted {m : ℕ} (σ : Fin n → PTm m) (U k : PTm n) :
    Syn.subst σ (weighted U k) = weighted (Syn.subst σ U) (Syn.subst σ k) := by simp only [weighted,subst_ap2]
@[simp] theorem subst_constant {m : ℕ} (σ : Fin n → PTm m) (N U A : PTm n) :
    Syn.subst σ (constant N U A) = constant (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ A) := by simp only [constant,PTm.subst_mul,subst_weighted]

theorem geometric_zero (U : PTm n) : Γ ⊢[PRAAx] geometric U zero ≐ zero := sum_zero _ _
theorem geometric_succ (U k : PTm n) : Γ ⊢[PRAAx] geometric U (succ k) ≐ geometric U k+pw U k := by
  simpa only [geometric,inst2_gB] using sum_succ' (Γ := Γ) gB k U

theorem geometric_affine (U k : PTm n) : Γ ⊢[PRAAx] geometric U (succ k) ≐ U*geometric U k+one := by
  have all : Γ ⊢[PRAAx] .all (geometric (Syn.shift U) (succ (var 0)) ≐ Syn.shift U*geometric (Syn.shift U) (var 0)+one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_geometric,ConciseIPRA.PTm.subst_succ,PTm.subst_mul,PTm.subst_add,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have g0 := natEq (geometric_zero (Γ := Γ) U)
      have g1 := natEq (geometric_succ (Γ := Γ) U zero)
      have p := natEq (pw_zero (Γ := Γ) U)
      apply deriveNat
      ipra_simps
      rw [g1,g0,p]
      ring
    · simp only [Fm.subst_eq,subst_geometric,ConciseIPRA.PTm.subst_succ,PTm.subst_mul,PTm.subst_add,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := (geometric (Syn.shift U) (succ (var 0)) ≐ Syn.shift U*geometric (Syn.shift U) (var 0)+one) :: Γ.map Fm.shift
      have g0 := natEq (geometric_succ (Γ := Δ) (Syn.shift U) (var 0))
      have g1 := natEq (geometric_succ (Γ := Δ) (Syn.shift U) (succ (var 0)))
      have p := natEq (pw_succ (Γ := Δ) (Syn.shift U) (var 0))
      have ih := natEq (Prf.hyp0 (Γ := Γ.map Fm.shift) (φ := geometric (Syn.shift U) (succ (var 0)) ≐ Syn.shift U*geometric (Syn.shift U) (var 0)+one))
      apply deriveNat
      ipra_simps
      linear_combination g1-Groth.ι (IPRA.Q.mk Δ (Syn.shift U))*g0+ih+p
  simpa only [Fm.subst_eq,subst_geometric,ConciseIPRA.PTm.subst_succ,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem weighted_zero (U : PTm n) : Γ ⊢[PRAAx] weighted U zero ≐ zero := sum_zero _ _
theorem weighted_body_at (U i : PTm n) : inst2 weightedBody i U = succ i*pw U i := by simp [weightedBody,inst2]
theorem weighted_succ (U k : PTm n) : Γ ⊢[PRAAx] weighted U (succ k) ≐ weighted U k+succ k*pw U k := by
  simpa only [weighted,weighted_body_at] using sum_succ' (Γ := Γ) weightedBody k U

theorem weighted_affine_step (U k : PTm n)
    (ih : Γ ⊢[PRAAx] weighted U (succ k) ≐ U*weighted U k+geometric U (succ k)) : Γ ⊢[PRAAx]
    weighted U (succ (succ k)) ≐ U*weighted U (succ k)+geometric U (succ (succ k)) := by
  ipra_lc natEq (weighted_succ (Γ := Γ) U (succ k))-natEq (geometric_succ (Γ := Γ) U (succ k))+natEq ih-
    Groth.ι (IPRA.Q.mk Γ U)*natEq (weighted_succ (Γ := Γ) U k)+
    (Groth.ι (IPRA.Q.mk Γ k)+1)*natEq (pw_succ (Γ := Γ) U k)

/-- The independently computed weighted power sum satisfies precisely the
Horner derivative recurrence; this identity is not an input. -/
theorem weighted_affine (U k : PTm n) : Γ ⊢[PRAAx]
    weighted U (succ k) ≐ U*weighted U k+geometric U (succ k) := by
  have all : Γ ⊢[PRAAx] .all (weighted (Syn.shift U) (succ (var 0)) ≐
      Syn.shift U*weighted (Syn.shift U) (var 0)+geometric (Syn.shift U) (succ (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_weighted,subst_geometric,ConciseIPRA.PTm.subst_succ,
        PTm.subst_mul,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have w0 := natEq (weighted_zero (Γ := Γ) U)
      have w1 := natEq (weighted_succ (Γ := Γ) U zero)
      have g0 := natEq (geometric_zero (Γ := Γ) U)
      have g1 := natEq (geometric_succ (Γ := Γ) U zero)
      have p := natEq (pw_zero (Γ := Γ) U)
      apply deriveNat
      ipra_simps
      rw [w1,w0,g1,g0,p]
      ring
    · simp only [Fm.subst_eq,subst_weighted,subst_geometric,ConciseIPRA.PTm.subst_succ,
        PTm.subst_mul,PTm.subst_add,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact weighted_affine_step _ _ Prf.hyp0
  simpa only [Fm.subst_eq,subst_weighted,subst_geometric,ConciseIPRA.PTm.subst_succ,
    PTm.subst_mul,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

/-- Genuine finite Gaussian arithmetic for varying the query of one
actual Horner step. Every operand retains its own decoded denominator. -/
theorem affine_query_difference_from_representations (a b z w c A B Z W C E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b B E) (hz : Γ ⊢[PRAAx] represents z Z E)
    (hw : Γ ⊢[PRAAx] represents w W E) (hc : Γ ⊢[PRAAx] represents c C E) : Γ ⊢[PRAAx]
    qsub (qadd (qmul a z) c) (qadd (qmul b w) c) ≐
      qadd (qmul (qsub a b) z) (qmul b (qsub z w)) := by
  have E2 := positive_product E E hE hE
  have c2 := represents_rescale c C E E hc
  have left := qsub_represents _ _ _ _ _ E2
    (qadd_represents _ _ _ _ _ E2 (qmul_represents _ _ _ _ _ _ hE hE ha hz) c2)
    (qadd_represents _ _ _ _ _ E2 (qmul_represents _ _ _ _ _ _ hE hE hb hw) c2)
  have right := qadd_represents _ _ _ _ _ E2
    (qmul_represents _ _ _ _ _ _ hE hE (qsub_represents _ _ _ _ _ hE ha hb) hz)
    (qmul_represents _ _ _ _ _ _ hE hE hb (qsub_represents _ _ _ _ _ hE hz hw))
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) E2 (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_add,im_add,re_mul,im_mul,re_scale,im_scale] <;> ring

theorem affine_query_difference (a b z w c : PTm n) : Γ ⊢[PRAAx]
    qsub (qadd (qmul a z) c) (qadd (qmul b w) c) ≐
      qadd (qmul (qsub a b) z) (qmul b (qsub z w)) := by
  let E := rawDen a*remainingDen b z w c
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive a) (remaining_den_positive _ _ _ _)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (remainingDen b z w c) E (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (remainingDen a z w c) E (raw_represents (Γ := Γ) b)
    (by unfold E remainingDen; ipra_ring)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (remainingDen a b w c) E (raw_represents (Γ := Γ) z)
    (by unfold E remainingDen; ipra_ring)
  have hw := rescale_to w (rawGaussian w) (rawDen w) (remainingDen a b z c) E (raw_represents (Γ := Γ) w)
    (by unfold E remainingDen; ipra_ring)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (remainingDen a b z w) E (raw_represents (Γ := Γ) c)
    (by unfold E remainingDen; ipra_ring)
  exact affine_query_difference_from_representations _ _ _ _ _ _ _ _ _ _ E hE ha hb hz hw hc

theorem horner_query_difference_succ (C z w k : PTm n) : Γ ⊢[PRAAx]
    qsub (horner C z (succ k)) (horner C w (succ k)) ≐
      qadd (qmul (qsub (horner C z k) (horner C w k)) z) (qmul (horner C w k) (qsub z w)) :=
  (qsub_congr (GaussianRationalHorner.horner_succ _ _ _) (GaussianRationalHorner.horner_succ _ _ _)).eqTrans
    (affine_query_difference _ _ _ _ _)

def sizeLaw (C w A U k : PTm n) : Fm PTm n := le k (length C) ⟶ bounded (horner C w k) (A*geometric U k) one
@[simp] theorem subst_sizeLaw {m : ℕ} (σ : Fin n → PTm m) (C w A U k : PTm n) :
    (sizeLaw C w A U k).subst σ = sizeLaw (Syn.subst σ C) (Syn.subst σ w) (Syn.subst σ A) (Syn.subst σ U) (Syn.subst σ k) := by
  simp only [sizeLaw,Fm.subst_imp,subst_le,subst_length,GaussianRationalMetric.subst_bounded,
    GaussianRationalHorner.subst_horner,PTm.subst_mul,subst_geometric,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

theorem size_zero (C w A U : PTm n) : Γ ⊢[PRAAx] bounded (horner C w zero) (A*geometric U zero) one :=
  bound_congr (GaussianRationalHorner.horner_zero C w).eqSymm
    ((congrMul (.eqRefl _) (geometric_zero U)).eqTrans (mul_zero A)).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl _))

theorem size_step (C w A U k : PTm n)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hk : Γ ⊢[PRAAx] lt k (length C)) (ih : Γ ⊢[PRAAx] bounded (horner C w k) (A*geometric U k) one) :
    Γ ⊢[PRAAx] bounded (horner C w (succ k)) (A*geometric U (succ k)) one := by
  have prod := bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) ih hw
  have prod' := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one) prod
  have sum := bounded_sum_same_den _ _ _ _ one (le_refl _) prod' (coefficient_at C A k hC hk)
  have num : Γ ⊢[PRAAx] A*geometric U k*U+A ≐ A*geometric U (succ k) := by
    have g := natEq (geometric_affine (Γ := Γ) U k)
    apply deriveNat
    ipra_simps
    rw [g]
    ring
  exact bound_congr (GaussianRationalHorner.horner_succ C w k).eqSymm num (.eqRefl _) sum

/-- Actual Horner prefixes are bounded by the actual geometric sum. -/
theorem size_prefix (C w A U k : PTm n)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx] bounded (horner C w k) (A*geometric U k) one := by
  have cShift : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianEuclideanResidualRadius.subst_coefficientBounds,Syn.shift] using hC.shift
  have wShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift U) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift] using hw.shift
  have all : Γ ⊢[PRAAx] .all (sizeLaw (Syn.shift C) (Syn.shift w) (Syn.shift A) (Syn.shift U) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (size_zero C w A U).wk
    · simp only [subst_sizeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact size_step _ _ _ _ _ cShift.wk.wk wShift.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] sizeLaw C w A U k := by
    simpa only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

def differenceLaw (C z w N U A p q k : PTm n) : Fm PTm n := le k N ⟶
  distanceBounded (horner C z (succ k)) (horner C w (succ k)) (constant k U A*p) q
@[simp] theorem subst_differenceLaw {m : ℕ} (σ : Fin n → PTm m) (C z w N U A p q k : PTm n) :
    (differenceLaw C z w N U A p q k).subst σ = differenceLaw (Syn.subst σ C) (Syn.subst σ z)
      (Syn.subst σ w) (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) := by
  simp only [differenceLaw,Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,
    GaussianRationalHorner.subst_horner,ConciseIPRA.PTm.subst_succ,PTm.subst_mul,subst_constant]

theorem difference_zero (C z w U A p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ zero)) (horner C w (succ zero)) (constant zero U A*p) q := by
  have same : Γ ⊢[PRAAx] horner C z (succ zero) ≐ horner C w (succ zero) :=
    (GaussianRationalHorner.horner_succ C z zero).eqTrans
      ((qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero C z) (.eqRefl _)).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_zero_left z).eqTrans
          ((GaussianRationalSyntheticDivision.qmul_zero_left w).eqSymm.eqTrans
            (qmul_congr (GaussianRationalHorner.horner_zero C w).eqSymm (.eqRefl _))))) (.eqRefl _)).eqTrans
              (GaussianRationalHorner.horner_succ C w zero).eqSymm)
  have zeroDiff := (qsub_congr same (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)
  have num : Γ ⊢[PRAAx] constant zero U A*p ≐ zero :=
    (congrMul (congrMul (.eqRefl _) (weighted_zero U)) (.eqRefl _)).eqTrans (by ipra_ring)
  exact bound_congr zeroDiff.eqSymm num.eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero q hq)

theorem difference_step (C z w N U A p q k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q)
    (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] distanceBounded (horner C z (succ k)) (horner C w (succ k)) (constant k U A*p) q) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ (succ k))) (horner C w (succ (succ k))) (constant (succ k) U A*p) q := by
  have prefixIndex : Γ ⊢[PRAAx] le (succ k) (length C) :=
    le_congr (.eqRefl _) hLen.eqSymm (le_trans hk (le_succ_self N))
  have size := size_prefix C w A U (succ k) hC hw prefixIndex
  have first := bounded_product _ _ _ _ _ _ hq (le_refl one) ih hz
  have first' := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] q*one ≐ q) first
  have second := bounded_product _ _ _ _ _ _ (le_refl one) hq size hzw
  have second' := bound_congr (.eqRefl _) (.eqRefl _) (one_mul q) second
  have sum := bounded_sum_same_den _ _ _ _ q hq first' second'
  have num : Γ ⊢[PRAAx] constant k U A*p*U+A*geometric U (succ k)*p ≐ constant (succ k) U A*p := by
    have h := natEq (weighted_affine (Γ := Γ) U k)
    apply deriveNat
    unfold constant
    ipra_simps
    rw [h]
    ring
  exact bound_congr (horner_query_difference_succ C z w (succ k)).eqSymm num (.eqRefl _) sum

/-- Uniform QF induction on the actual Horner counter, with every size
estimate obtained from the original coefficient condition. -/
theorem difference_prefix (C z w N U A p q k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ k)) (horner C w (succ k)) (constant k U A*p) q := by
  have lenShift : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
  have cShift : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianEuclideanResidualRadius.subst_coefficientBounds,Syn.shift] using hC.shift
  have zShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift U) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift] using hz.shift
  have wShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift U) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift] using hw.shift
  have qShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift q) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hq.shift
  have zwShift : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z) (Syn.shift w) (Syn.shift p) (Syn.shift q) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_distanceBounded,Syn.shift] using hzw.shift
  have all : Γ ⊢[PRAAx] .all (differenceLaw (Syn.shift C) (Syn.shift z) (Syn.shift w) (Syn.shift N)
      (Syn.shift U) (Syn.shift A) (Syn.shift p) (Syn.shift q) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_differenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (difference_zero C z w U A p q hq).wk
    · simp only [subst_differenceLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact difference_step _ _ _ _ _ _ _ _ _ lenShift.wk.wk cShift.wk.wk zShift.wk.wk wShift.wk.wk
        qShift.wk.wk zwShift.wk.wk Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] differenceLaw C z w N U A p q k := by
    simpa only [subst_differenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- Exact original Euclidean point-variation estimate. It holds even for
constant polynomials and radius U=0, so the source N,U>=1 case follows. -/
theorem evaluation_bound (C z w N U A p q : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate C w) (constant N U A*p) q :=
  bound_congr (qsub_congr
    (congrAp3 GaussianRationalHorner.hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _))
    (congrAp3 GaussianRationalHorner.hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _))) (.eqRefl _) (.eqRefl _)
      (difference_prefix C z w N U A p q N hLen hC hz hw hq hzw (le_refl _))

def difference (C z w : PTm n) : PTm n := qsub (evaluate C z) (evaluate C w)
def differenceF : PR 3 := PTm.toPR (difference (var 0) (var 1) (var 2))
def constantF : PR 3 := PTm.toPR (constant (var 0) (var 1) (var 2))

@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (C z w : PTm n) :
    Syn.subst σ (difference C z w) = difference (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ w) := by
  simp only [difference,GaussianRationalMetric.subst_qsub,GaussianRationalHorner.subst_evaluate]

theorem difference_program_at (C z w : PTm n) : Γ ⊢[PRAAx] ap3 differenceF C z w ≐ difference C z w := by
  simpa only [differenceF,ap3,subst_difference,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (difference (var 0) (var 1) (var 2) : PTm 3) ![C,z,w]
theorem constant_program_at (N U A : PTm n) : Γ ⊢[PRAAx] ap3 constantF N U A ≐ constant N U A := by
  simpa only [constantF,ap3,subst_constant,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (constant (var 0) (var 1) (var 2) : PTm 3) ![N,U,A]

theorem program_bound (C z w N U A p q : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) : Γ ⊢[PRAAx]
    bounded (ap3 differenceF C z w) (ap3 constantF N U A*p) q :=
  bound_congr (difference_program_at C z w).eqSymm (congrMul (constant_program_at N U A).eqSymm (.eqRefl _)) (.eqRefl _)
    (evaluation_bound C z w N U A p q hLen hC hz hw hq hzw)

theorem actual_weighted_power_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((geometric (var 0) (succ (var 1)) ≐ var 0*geometric (var 0) (var 1)+one) ⋏
      (weighted (var 0) (succ (var 1)) ≐ var 0*weighted (var 0) (var 1)+geometric (var 0) (succ (var 1)))) :=
  closeUniv 2 (.andI (geometric_affine _ _) (weighted_affine _ _))

theorem actual_horner_query_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (qsub (qadd (qmul (var 0) (var 2)) (var 4)) (qadd (qmul (var 1) (var 3)) (var 4)) ≐
      qadd (qmul (qsub (var 0) (var 1)) (var 2)) (qmul (var 1) (qsub (var 2) (var 3)))) :=
  closeUniv 5 (affine_query_difference _ _ _ _ _)

theorem rational_horner_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coefficientBounds (var 0) (var 2) ⟶ bounded (var 1) (var 3) one ⟶ le (var 4) (length (var 0)) ⟶
      bounded (horner (var 0) (var 1) (var 4)) (var 2*geometric (var 3) (var 4)) one) :=
  closeUniv 5 (.impI (.impI (.impI (size_prefix _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem rational_horner_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (length (var 0) ≐ succ (var 3) ⟶ coefficientBounds (var 0) (var 5) ⟶
      bounded (var 1) (var 4) one ⟶ bounded (var 2) (var 4) one ⟶ le one (var 7) ⟶
      distanceBounded (var 1) (var 2) (var 6) (var 7) ⟶
      distanceBounded (evaluate (var 0) (var 1)) (evaluate (var 0) (var 2))
        (constant (var 3) (var 4) (var 5)*var 6) (var 7)) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact evaluation_bound _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem rational_horner_lipschitz_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (length (var 0) ≐ succ (var 3) ⟶ coefficientBounds (var 0) (var 5) ⟶
      bounded (var 1) (var 4) one ⟶ bounded (var 2) (var 4) one ⟶ le one (var 7) ⟶
      distanceBounded (var 1) (var 2) (var 6) (var 7) ⟶
      bounded (ap3 differenceF (var 0) (var 1) (var 2))
        (ap3 constantF (var 3) (var 4) (var 5)*var 6) (var 7)) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact program_bound _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRationalHornerLipschitz
