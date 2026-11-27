import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaReciprocalPair
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingTailComparison
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.Lattice.GaussianEulerPositivePowerChartCorrectedImage

/-!
# Finite reciprocal correction on a negative Gamma interval

Write the argument as `−N−1+a/b` with `0<a<b`. The finite correction
from the argument shifted to `1+a/b` is the sum of the reciprocals
`b/(jb−a)` for `1≤j≤N+1`, minus the single positive-pole reciprocal
`b/a`. Every denominator on this domain is proved positive.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalCorrection

open_ipra
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero ofGaussian_canonical)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianGammaRationalWendelBoundary (fraction_zero)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def guard (a b : PTm n) : Fm PTm n := le one a ⋏ lt a b
def bottomDen (a b j : PTm n) : PTm n := monus (succ j*b) a
def row (a b j : PTm n) : PTm n := fraction b (bottomDen a b j)
def body : PTm 2 := row (fstT (var 1)) (sndT (var 1)) (var 0)
def positiveSum (a b N : PTm n) : PTm n := GaussianRationalFiniteSum.sum body N (pairT a b)
def correction (a b N : PTm n) : PTm n := qsub (positiveSum a b (succ N)) (fraction b a)

ipra_subst guard

ipra_subst bottomDen

ipra_subst row

ipra_subst positiveSum

ipra_subst correction

theorem row_at (a b j : PTm n) : Γ ⊢[PRAAx] inst2 body j (pairT a b) ≐ row a b j := by
  simp only [inst2,body,subst_row,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,subst_fstT,subst_sndT]
  exact GaussianCompactRiemannName.fraction_congr _ _ _ _ (snd_pair _ _)
    (congrMonus (congrMul (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))

theorem prefix_succ (a b N : PTm n) :
    Γ ⊢[PRAAx] positiveSum a b (succ N) ≐ qadd (positiveSum a b N) (row a b N) :=
  (GaussianRationalFiniteSum.sum_succ body N (pairT a b)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (row_at a b N))

theorem den_expand (a b j : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] bottomDen a b j ≐ monus b a+j*b := by
  have e := natEq (eq_add_of_le (le_of_lt h))
  have expand : Γ ⊢[PRAAx] succ j*b ≐ (monus b a+j*b)+a := by
    apply deriveNat
    ipra_simps
    linear_combination e
  exact (congrMonus expand (.eqRefl _)).eqTrans (add_monus _ _)

alias separation_positive := Common.one_le_monus_of_lt

theorem row_den_positive (a b j : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] le one (bottomDen a b j) :=
  le_trans (separation_positive a b h)
    (le_congr (.eqRefl _) (den_expand a b j h).eqSymm (le_add_right _ _))

theorem row_distance_exact (a c b j : PTm n) (hc : Γ ⊢[PRAAx] lt c b)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    qsub (row c b j) (row a b j) ≐
      fraction (b*monus c a) (bottomDen c b j*bottomDen a b j) := by
  let P := bottomDen c b j
  let Q := bottomDen a b j
  have hcb : Γ ⊢[PRAAx] le c (succ j*b) :=
    le_trans (le_of_lt hc) (by ipra_le 𝔞(j)*𝔞(b))
  have ec := natEq (eq_add_of_le hcb)
  have ea := natEq (eq_add_of_le (le_trans hac hcb))
  have ed := natEq (eq_add_of_le hac)
  have ex : Γ ⊢[PRAAx] Q ≐ monus c a+P := by
    apply deriveNat
    dsimp only [Q,P,bottomDen]
    ipra_simps
    linear_combination -ea+ec+ed
  have hPQ := le_of_eq_add (ex.eqTrans (add_comm _ _))
  have e := (congrMonus ex (.eqRefl _)).eqTrans (add_monus _ _)
  exact (GaussianGammaDigammaReciprocalPair.fraction_gap b P Q (row_den_positive c b j hc) hPQ).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul (.eqRefl _) e) (.eqRefl _))

private theorem row_nonnegative (a b j : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT (row a b j)) :=
  rationalLE_congr (congrFst (fraction_zero one (le_refl one))) (.eqRefl _)
    (fractions_order zero one b (bottomDen a b j) (le_refl one) (row_den_positive a b j h) (by ipra_le 𝔞(b)))

private theorem row_upper (a b j K : PTm n) (h : Γ ⊢[PRAAx] lt a b)
    (hK : Γ ⊢[PRAAx] le b (K*monus b a)) :
    Γ ⊢[PRAAx] rationalLE (fstT (row a b j)) (fstT (fraction K one)) := by
  have e := natEq (den_expand (Γ := Γ) a b j h)
  exact fractions_order b (bottomDen a b j) K one (row_den_positive a b j h) (le_refl one)
    (by ipra_le sl hK+𝔞(K)*𝔞(j)*𝔞(b) with 𝔞(K)*e)

private theorem integer_sum (a b : PTm n) : Γ ⊢[PRAAx] qadd (fraction a one) (fraction b one) ≐ fraction (a+b) one :=
  (GaussianEulerPositivePowerChartCorrectedImage.fraction_sum a one b one (le_refl one) (le_refl one)).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring))

def prefixUpper (a b K N : PTm n) : Fm PTm n :=
  rationalLE (fstT (positiveSum a b N)) (fstT (fraction (K*N) one))

ipra_subst prefixUpper

private theorem upper_zero (a b K : PTm n) : Γ ⊢[PRAAx] prefixUpper a b K zero :=
  rationalLE_congr (congrFst (GaussianRationalFiniteSum.sum_zero body _)).eqSymm
    (congrFst ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (mul_zero K) (.eqRefl _)).eqTrans
      (fraction_zero one (le_refl one)))).eqSymm (point_order_refl qzero)

private theorem upper_step (a b K j : PTm n) (h : Γ ⊢[PRAAx] lt a b)
    (hK : Γ ⊢[PRAAx] le b (K*monus b a)) (ih : Γ ⊢[PRAAx] prefixUpper a b K j) :
    Γ ⊢[PRAAx] prefixUpper a b K (succ j) := by
  have r := point_add_order (positiveSum a b j) (fraction (K*j) one) (row a b j) (fraction K one)
    ih (row_upper a b j K h hK)
  have e := (integer_sum (K*j) K).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (show Γ ⊢[PRAAx] K*j+K ≐ K*succ j from by ipra_ring) (.eqRefl _))
  exact rationalLE_congr (congrFst (prefix_succ a b j)).eqSymm (congrFst e) r

theorem prefix_upper (a b K N : PTm n) (h : Γ ⊢[PRAAx] lt a b)
    (hK : Γ ⊢[PRAAx] le b (K*monus b a)) : Γ ⊢[PRAAx] prefixUpper a b K N := by
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift,Δ] using h.shift
  have hK' : Δ ⊢[PRAAx] le (Syn.shift b) (Syn.shift K*monus (Syn.shift b) (Syn.shift a)) := by
    simpa [Fm.shift,Syn.shift,Δ] using hK.shift
  have all : Γ ⊢[PRAAx] .all (prefixUpper (Syn.shift a) (Syn.shift b) (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ (by simp [prefixUpper,rationalLE,le_QF]) ?_ ?_
    · simpa only [subst_prefixUpper,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using upper_zero (Γ := Γ) a b K
    · simpa only [subst_prefixUpper,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        upper_step (Syn.shift a) (Syn.shift b) (Syn.shift K) (var 0) h'.wk hK'.wk Prf.hyp0
  simpa only [subst_prefixUpper,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def firstLower (a b N : PTm n) : Fm PTm n :=
  rationalLE (fstT (row a b zero)) (fstT (positiveSum a b (succ N)))

ipra_subst firstLower

theorem first_lower (a b N : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] firstLower a b N := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (firstLower (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ (by simp [firstLower,rationalLE,le_QF]) ?_ ?_
    · simp only [subst_firstLower,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have canon : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (row a b zero) :=
        ofGaussian_canonical _ _ (row_den_positive a b zero h)
      have e := (prefix_succ a b zero).eqTrans ((GaussianRationalSyntheticDivision.qadd_congr
        (GaussianRationalFiniteSum.sum_zero body _) (.eqRefl _)).eqTrans (qzero_add (row a b zero) canon))
      exact rationalLE_congr (.eqRefl _) (congrFst e).eqSymm (point_order_refl _)
    · simp only [subst_firstLower,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let A := Syn.shift a
      let B := Syn.shift b
      let J := succ (var 0 : PTm (n+1))
      have c : (firstLower A B (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          GaussianRationalHorner.canonical (row A B zero) :=
        ofGaussian_canonical _ _ (row_den_positive A B zero h'.wk)
      exact rationalLE_congr (congrFst (GaussianReciprocalHorner.qadd_zero_right _ c))
        (congrFst (prefix_succ A B J)).eqSymm
        (point_add_order (row A B zero) (positiveSum A B J) qzero (row A B J) Prf.hyp0
          (row_nonnegative A B J h'.wk))
  simpa only [subst_firstLower,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalCorrection
