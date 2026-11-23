import IPRADerivations.Analysis.GaussianGammaCanonicalPrefixTaylor
import IPRADerivations.Analysis.GaussianGammaCanonicalCoefficientRecurrence
import IPRADerivations.Analysis.GaussianRationalPowerNonzero

/-!
# Branchless finite cancellation of the leading P factor

The actual all-order coefficient sampler has c_0=0 and c_1=1.
Its finite canonical Taylor polynomial factors as w times the shifted
coefficient sum, for every raw w, including zero. No reciprocal of w
or decision of its nonzeroness is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDeflatedPrefixTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaCanonicalPrefixTaylor (canonicalTerm canonicalPrefix taylor)
open GaussianRationalHorner (qmul qadd qzero qmul_canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qzero_add qmul_zero_left qmul_zero_right)
open GaussianRationalReciprocal (power power_zero power_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (r w e : PTm n) : PTm n := qmul (sample r (succ e)) (power w e)
def data (r w : PTm n) : PTm n := pairT r w
def body : PTm 2 := term (fstT (var 1)) (sndT (var 1)) (var 0)
def prefixValue (r w k : PTm n) : PTm n := GaussianRationalFiniteSum.sum body k (data r w)
def deflatedTaylor (r d w : PTm n) : PTm n := prefixValue r w (succ d)
def factorLaw (r w k : PTm n) : Fm PTm n := canonicalPrefix r w (succ k) ≐ qmul w (prefixValue r w k)

@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (r w e : PTm n) :
    Syn.subst σ (term r w e) = term (Syn.subst σ r) (Syn.subst σ w) (Syn.subst σ e) := by simp [term]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (r w : PTm n) :
    Syn.subst σ (data r w) = data (Syn.subst σ r) (Syn.subst σ w) := by simp [data]
@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (r w k : PTm n) :
    Syn.subst σ (prefixValue r w k) = prefixValue (Syn.subst σ r) (Syn.subst σ w) (Syn.subst σ k) := by simp [prefixValue]
@[simp] theorem subst_deflatedTaylor {m : ℕ} (σ : Fin n → PTm m) (r d w : PTm n) :
    Syn.subst σ (deflatedTaylor r d w) = deflatedTaylor (Syn.subst σ r) (Syn.subst σ d) (Syn.subst σ w) := by simp [deflatedTaylor]
@[simp] theorem subst_factorLaw {m : ℕ} (σ : Fin n → PTm m) (r w k : PTm n) :
    (factorLaw r w k).subst σ = factorLaw (Syn.subst σ r) (Syn.subst σ w) (Syn.subst σ k) := by simp [factorLaw]

theorem body_at (r w e : PTm n) : Γ ⊢[PRAAx] inst2 body e (data r w) ≐ term r w e := by
  simp only [body,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (congrAp2 GaussianGammaHigherCoefficientName.nameF (fst_pair r w) (.eqRefl _))
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (snd_pair r w))

theorem prefix_zero (r w : PTm n) : Γ ⊢[PRAAx] prefixValue r w zero ≐ qzero := GaussianRationalFiniteSum.sum_zero body _
theorem prefix_succ (r w k : PTm n) : Γ ⊢[PRAAx]
    prefixValue r w (succ k) ≐ qadd (prefixValue r w k) (term r w k) :=
  (GaussianRationalFiniteSum.sum_succ body k _).eqTrans (qadd_congr (.eqRefl _) (body_at r w k))

theorem canonical_prefix_zero (r w : PTm n) : Γ ⊢[PRAAx] canonicalPrefix r w one ≐ qzero := by
  have row : Γ ⊢[PRAAx] canonicalTerm r w zero ≐ qzero :=
    (qmul_congr (GaussianGammaCanonicalCoefficientRecurrence.canonical_zero r) (.eqRefl _)).eqTrans (qmul_zero_left _)
  exact (GaussianRationalFiniteSum.sum_succ GaussianGammaCanonicalPrefixTaylor.body zero
    (GaussianGammaCanonicalPrefixTaylor.data r w)).eqTrans
      ((qadd_congr (GaussianRationalFiniteSum.sum_zero _ _) ((GaussianGammaCanonicalPrefixTaylor.body_at r w zero).eqTrans row)).eqTrans
        (qzero_add qzero GaussianRationalSyntheticDivision.qzero_canonical))

theorem shifted_term (r w e : PTm n) : Γ ⊢[PRAAx] canonicalTerm r w (succ e) ≐ qmul w (term r w e) :=
  (qmul_congr (.eqRefl _) (power_succ w e)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative _ _))

theorem factor_zero (r w : PTm n) : Γ ⊢[PRAAx] factorLaw r w zero :=
  (canonical_prefix_zero r w).eqTrans
    ((qmul_congr (.eqRefl _) (prefix_zero r w)).eqTrans (qmul_zero_right w)).eqSymm

theorem factor_step (r w k : PTm n) (ih : Γ ⊢[PRAAx] factorLaw r w k) : Γ ⊢[PRAAx] factorLaw r w (succ k) := by
  have next := (GaussianRationalFiniteSum.sum_succ GaussianGammaCanonicalPrefixTaylor.body (succ k)
    (GaussianGammaCanonicalPrefixTaylor.data r w)).eqTrans
      (qadd_congr ih ((GaussianGammaCanonicalPrefixTaylor.body_at r w (succ k)).eqTrans (shifted_term r w k)))
  exact next.eqTrans ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm.eqTrans
    (qmul_congr (.eqRefl _) (prefix_succ r w k).eqSymm))

/-- Exact normalized finite cancellation, with no nonzero input premise. -/
theorem original_factor (r d w : PTm n) : Γ ⊢[PRAAx]
    taylor r (succ d) w ≐ qmul w (deflatedTaylor r d w) := by
  have all : Γ ⊢[PRAAx] .all (factorLaw (Syn.shift r) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_factorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact factor_zero r w
    · simp only [subst_factorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact factor_step _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] factorLaw r w (succ d)
  simpa only [subst_factorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE (succ d)

theorem fixed_linear (q R : PTm n) : Γ ⊢[PRAAx] GaussianGammaFiniteCoefficientStability.fixedCoefficient q R one ≐ qone :=
  (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ one
    (le_trans (zero_lt_succ (two*R)) (le_add_right _ _))).eqTrans
      (GaussianGammaPolynomialConstantLinear.whole_linear q R one one (le_refl one))

theorem canonical_one (r : PTm n) : Γ ⊢[PRAAx] sample r one ≐ qone :=
  (GaussianGammaHigherCoefficientName.sample_fixed_coefficient r one).eqTrans (fixed_linear _ _)

theorem zero_term (r : PTm n) : Γ ⊢[PRAAx] term r qzero zero ≐ qone :=
  (qmul_congr (canonical_one r) (power_zero qzero)).eqTrans
    (GaussianReciprocalHorner.qmul_one_right qone GaussianRationalSyntheticDivision.qone_canonical)
theorem positive_zero_term (r k : PTm n) : Γ ⊢[PRAAx] term r qzero (succ k) ≐ qzero :=
  (qmul_congr (.eqRefl _) (GaussianRationalPowerNonzero.zero_positive_power k)).eqTrans (qmul_zero_right _)

def zeroLaw (r k : PTm n) : Fm PTm n := prefixValue r qzero (succ k) ≐ qone
@[simp] theorem subst_zeroLaw {m : ℕ} (σ : Fin n → PTm m) (r k : PTm n) :
    (zeroLaw r k).subst σ = zeroLaw (Syn.subst σ r) (Syn.subst σ k) := by simp [zeroLaw]

theorem at_zero (r d : PTm n) : Γ ⊢[PRAAx] deflatedTaylor r d qzero ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (zeroLaw (Syn.shift r) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_zeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (prefix_succ r qzero zero).eqTrans
        ((qadd_congr (prefix_zero r qzero) (zero_term r)).eqTrans (qzero_add qone GaussianRationalSyntheticDivision.qone_canonical))
    · simp only [subst_zeroLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (prefix_succ _ qzero _).eqTrans
        ((qadd_congr Prf.hyp0 (positive_zero_term _ _)).eqTrans
          (GaussianReciprocalHorner.qadd_zero_right qone GaussianRationalSyntheticDivision.qone_canonical))
  change Γ ⊢[PRAAx] zeroLaw r d
  simpa only [subst_zeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE d

def deflatedF : PR 3 := PTm.toPR (deflatedTaylor (var 0) (var 1) (var 2))
theorem program_at (r d w : PTm n) : Γ ⊢[PRAAx] ap3 deflatedF r d w ≐ deflatedTaylor r d w := by
  simpa only [deflatedF,ap3,subst_deflatedTaylor,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (deflatedTaylor (var 0) (var 1) (var 2) : PTm 3) ![r,d,w]

theorem actual_original_canonical_taylor_leading_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (taylor (var 0) (succ (var 1)) (var 2) ≐ qmul (var 2) (deflatedTaylor (var 0) (var 1) (var 2))) :=
  closeUniv 3 (original_factor _ _ _)
theorem actual_original_deflated_taylor_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (deflatedTaylor (var 0) (var 1) qzero ≐ qone) := closeUniv 2 (at_zero _ _)
theorem actual_original_deflated_taylor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 deflatedF (var 0) (var 1) (var 2) ≐ deflatedTaylor (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaDeflatedPrefixTaylor
