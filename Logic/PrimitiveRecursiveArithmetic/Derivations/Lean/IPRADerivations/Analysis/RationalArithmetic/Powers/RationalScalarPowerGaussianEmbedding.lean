import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialGaussianEmbedding

/-!
# Original signed rational powers on the Gaussian real axis

The original rational multiplication recursor runs for an arbitrary
numerical exponent. An atomic object induction identifies its output
with the original Gaussian power of the embedded base.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalScalarPowerGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed scalarOne)
open RationalPolynomialGaussianEmbedding (embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step : PTm 3 := RationalArithmetic.multiply (var 1) (var 2)
def powerF : PR 2 := rec2 (scalarOne : PTm 1) step
def power (z k : PTm n) : PTm n := ap2 powerF k z

ipra_subst power

theorem power_zero (z : PTm n) : Γ ⊢[PRAAx] power z zero ≐ scalarOne := by
  simpa only [power,powerF,RationalGaussianEmbedding.subst_scalarOne] using
    rec2_zero (Γ := Γ) (scalarOne : PTm 1) step z

theorem power_succ (z k : PTm n) : Γ ⊢[PRAAx] power z (succ k) ≐ RationalArithmetic.multiply (power z k) z := by
  simpa only [power,powerF,step,RationalArithmetic.subst_multiply,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    rec2_succ (Γ := Γ) (scalarOne : PTm 1) step k z

theorem power_canonical (z k : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (power z k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · exact RationalArithmetic.guard_congr
      ((congrAp2 powerF Prf.hyp0 (.eqRefl z)).eqTrans (power_zero z))
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  · exact RationalArithmetic.guard_congr
      ((congrAp2 powerF Prf.hyp0 (.eqRefl z)).eqTrans (power_succ z _))
      (RationalArithmetic.multiply_guard _ _)

def law (z k : PTm n) : Fm PTm n := embed (power z k) ≐ GaussianRationalReciprocal.power (embed z) k

ipra_subst law

theorem power_embedding (z k : PTm n) : Γ ⊢[PRAAx] law z k := by
  have all : Γ ⊢[PRAAx] .all (law (Syn.shift z) (var 0)) := by
    ipra_qfind [subst_law]
    · exact (embed_congr (power_zero z)).eqTrans
        (RationalGaussianEmbedding.embed_one.eqTrans (GaussianRationalReciprocal.power_zero _).eqSymm)
    · exact (embed_congr (power_succ _ _)).eqTrans ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans
          (GaussianRationalReciprocal.power_succ _ _).eqSymm))
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem power_equality (z k v : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (RationalArgmin.rationalEq (power z k) v) (GaussianRationalReciprocal.power (embed z) k ≐ embed v) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (power_embedding z k).eqSymm.eqTrans
      ((RationalGaussianEmbedding.embed_eq_iff (power z k) v).iffMpr Prf.hyp0)
  · exact (RationalGaussianEmbedding.embed_eq_iff (power z k) v).iffMp ((power_embedding z k).eqTrans Prf.hyp0)

theorem actual_rational_power_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (ap2 powerF (var 1) (var 0)) ≐ GaussianRationalReciprocal.power (embed (var 0)) (var 1)) :=
  closeUniv 2 (power_embedding _ _)
theorem actual_rational_power_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (RationalArgmin.rationalEq (power (var 0) (var 1)) (var 2))
      (GaussianRationalReciprocal.power (embed (var 0)) (var 1) ≐ embed (var 2))) :=
  closeUniv 3 (power_equality _ _ _)

end LeanProofs.IPRA.Analysis.RationalScalarPowerGaussianEmbedding
