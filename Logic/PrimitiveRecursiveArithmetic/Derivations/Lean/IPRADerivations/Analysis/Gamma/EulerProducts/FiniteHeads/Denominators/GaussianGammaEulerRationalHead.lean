import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Denominators.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartJacobian

/-!
# Natural numerator and denominator of the original real Euler head

On the positive rational axis, the actual head at cutoff N is the
product of a+bj for 0 ≤ j ≤ N divided by b^(N+1) times N!. This
representation lets the weighted product inequalities act on the
original head used in the convergence proof.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalHead

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianGammaEulerHead (head factor head_zero head_succ run program_at)
open GaussianGammaEulerHeadLower (translated factor_represents)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product ofGaussian_represents ofGaussian_canonical
  canonical_unique represents_congr qadd_canonical)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal_of_values re_add im_add re_scale im_scale re_one im_one)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linearBody : PTm 2 := fstT (var 1) + sndT (var 1) * var 0

def numerator (K a b : PTm n) : PTm n :=
  ap2 (prodF linearBody) K (pairT a b)

def denominator (N b : PTm n) : PTm n := pw b (succ N) * fact N

ipra_subst numerator

ipra_subst denominator [fact]

theorem numerator_zero (a b : PTm n) : Γ ⊢[PRAAx] numerator zero a b ≐ one :=
  prod_zero linearBody (pairT a b)

theorem numerator_succ (K a b : PTm n) : Γ ⊢[PRAAx]
    numerator (succ K) a b ≐ numerator K a b * (a+b*K) := by
  have point : Γ ⊢[PRAAx] inst2 linearBody K (pairT a b) ≐ a+b*K := by
    simpa only [linearBody,inst2,PTm.subst_add,PTm.subst_mul,subst_fstT,subst_sndT,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
      congrAdd (fst_pair a b) (congrMul (snd_pair a b) (.eqRefl K))
  exact (prod_succ linearBody K (pairT a b)).eqTrans (congrMul (.eqRefl _) point)

theorem numerator_positive (K a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (numerator K a b) := by
  have h : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift,one] using ha.shift
  have hall : Γ ⊢[PRAAx] .all (le one (numerator (var 0) (Syn.shift a) (Syn.shift b))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_numerator, one]
    · exact le_congr (.eqRefl _) (numerator_zero a b).eqSymm (le_refl _)
    · exact le_congr (.eqRefl _) (numerator_succ _ _ _).eqSymm
        (positive_product _ _ Prf.hyp0 (le_trans h.wk (le_add_right _ _)))
  simpa only [subst_le,subst_numerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hall.allE K

theorem denominator_positive (N b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (denominator N b) :=
  positive_product _ _ (RationalNonnegativePowers.denominator_positive b (succ N) hb)
    (GammaEulerMesh.factorial_positive N)

theorem denominator_succ (N b : PTm n) : Γ ⊢[PRAAx]
    denominator (succ N) b ≐ denominator N b * (b*succ N) := by
  unfold denominator
  exact (congrMul (pw_succ _ _) (fact_succ N zero)).eqTrans (by ipra_ring)

private theorem fraction_factor (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] factor N (scale a oneCode) b ≐ fraction (a+b*succ N) (b*succ N) := by
  have hD := positive_product _ _ hb (zero_lt_succ (Γ := Γ) N)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (hrv := ofGaussian_represents _ _ hD)
  apply represents_congr (.eqRefl _) (h := factor_represents N (scale a oneCode) b hb) ?_ (.eqRefl _)
  unfold translated
  apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

def headLaw (N a b : PTm n) : Fm PTm n :=
  head (scale a oneCode) b N ≐ fraction (numerator (succ N) a b) (denominator N b)

ipra_subst headLaw [fraction]

private theorem head_zero_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] headLaw zero a b := by
  have e₁ : Γ ⊢[PRAAx] numerator (succ zero) a b ≐ a := (numerator_succ zero a b).eqTrans
    ((congrMul (numerator_zero a b) (.eqRefl _)).eqTrans (by ipra_ring))
  have e₂ : Γ ⊢[PRAAx] denominator zero b ≐ b :=
    (congrMul (pw_succ _ _ |>.eqTrans (congrMul (pw_zero b) (.eqRefl b))) (fact_zero zero)).eqTrans (by ipra_ring)
  exact (head_zero _ _ hb).eqTrans (GaussianEulerPositivePowerChartJacobian.fraction_congr e₁.eqSymm e₂.eqSymm)

private theorem head_succ_fraction (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ih : Γ ⊢[PRAAx] headLaw N a b) : Γ ⊢[PRAAx] headLaw (succ N) a b :=
  (head_succ _ _ _).eqTrans ((qmul_congr ih (fraction_factor N a b hb)).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product _ _ _ _ (denominator_positive N b hb)
      (positive_product _ _ hb (zero_lt_succ N))).eqTrans
      (GaussianEulerPositivePowerChartJacobian.fraction_congr (numerator_succ (succ N) a b).eqSymm
        (denominator_succ N b).eqSymm)))

theorem head_fraction (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] headLaw N a b := by
  have hb' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift,one] using hb.shift
  have h : Γ ⊢[PRAAx] .all (headLaw (var 0) (Syn.shift a) (Syn.shift b)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using head_zero_fraction a b hb
    · simpa only [subst_headLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        (head_succ_fraction (var 0) (Syn.shift a) (Syn.shift b) hb'.wk Prf.hyp0)
  simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE N

theorem returned_head_fraction (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    run (scale a oneCode) b N ≐ fraction (numerator (succ N) a b) (denominator N b) :=
  (program_at _ _ _).eqTrans (head_fraction N a b hb)

theorem actual_Euler_rational_head_fraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ run (scale (var 1) oneCode) (var 2) (var 0) ≐
      fraction (numerator (succ (var 0)) (var 1) (var 2)) (denominator (var 0) (var 2))) :=
  closeUniv 3 (.impI (returned_head_fraction _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalHead
