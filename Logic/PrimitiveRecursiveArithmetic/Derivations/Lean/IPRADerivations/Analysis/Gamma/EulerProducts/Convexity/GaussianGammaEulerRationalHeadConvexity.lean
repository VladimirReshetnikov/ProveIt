import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerRationalHead
import IPRADerivations.Analysis.Optimization.WeightedAMGM
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# Weighted comparison of the original rational Euler heads

Each factor a+bj inherits the barycenter of two input numerators.
Weighted arithmetic-geometric mean bounds the powered product with
natural weights. The precise normalization of the head denominators
then gives the same comparison for the actual rational heads.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalHeadConvexity

open_ipra
open GaussianGammaEulerRationalHead (numerator denominator numerator_zero numerator_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (r s : PTm n) : PTm n := succ (r+s)
def barycenter (a d r s : PTm n) : PTm n := succ r*a+s*d

def compareNumerators (K a d b r s : PTm n) : Fm PTm n :=
  le (pw (pw (weight r s) (weight r s)) K * (pw (numerator K a b) (succ r) * pw (numerator K d b) s))
    (pw (numerator K (barycenter a d r s) (weight r s*b)) (weight r s))

ipra_subst compareNumerators [weight, barycenter, pw]

private theorem numerator_comparison_zero (a d b r s : PTm n) :
    Γ ⊢[PRAAx] compareNumerators zero a d b r s := by
  let P := weight r s
  have base (t B e : PTm n) : Γ ⊢[PRAAx] pw (numerator zero t B) e ≐ one :=
    (congrAp2 powF (.eqRefl e) (numerator_zero t B)).eqTrans (AnalyticNumberTheory.Order.pw_one_base e)
  exact le_congr
    ((congrMul (pw_zero (pw P P)) (congrMul (base a b (succ r)) (base d b s))).eqTrans (by ipra_ring)).eqSymm
    (base (barycenter a d r s) (P*b) P).eqSymm (le_refl one)

private theorem numerator_power_step (K a b t : PTm n) :
    Γ ⊢[PRAAx] pw (numerator (succ K) a b) t ≐ pw (numerator K a b) t * pw (a+b*K) t :=
  (congrAp2 powF (.eqRefl t) (numerator_succ K a b)).eqTrans (pw_mul_base _ _ _)

private theorem numerator_comparison_succ (K a d b r s : PTm n)
    (ih : Γ ⊢[PRAAx] compareNumerators K a d b r s) :
    Γ ⊢[PRAAx] compareNumerators (succ K) a d b r s := by
  let P := weight r s
  let C := barycenter a d r s
  let D := P*b
  let L := a+b*K
  let R := d+b*K
  have point : Γ ⊢[PRAAx] succ r*L+s*R ≐ C+D*K := by
    dsimp [L,R,C,D,barycenter,P,weight]
    ipra_ring
  have h := le_congr (.eqRefl _)
    (congrAp2 powF (.eqRefl P) point) (WeightedAMGM.amgm (Γ := Γ) r s L R)
  have forward : Γ ⊢[PRAAx]
      pw (pw P P) (succ K) * (pw (numerator (succ K) a b) (succ r) * pw (numerator (succ K) d b) s) ≐
        (pw (pw P P) K * (pw (numerator K a b) (succ r) * pw (numerator K d b) s)) *
        (pw P P * (pw L (succ r) * pw R s)) :=
    (congrMul (pw_succ _ _) (congrMul (numerator_power_step K a b (succ r))
      (numerator_power_step K d b s))).eqTrans (by ipra_ring)
  exact le_congr forward.eqSymm (numerator_power_step K C D P).eqSymm (le_mul_mono ih h)

theorem numerator_comparison (K a d b r s : PTm n) :
    Γ ⊢[PRAAx] compareNumerators K a d b r s := by
  have hall : Γ ⊢[PRAAx] .all (compareNumerators (var 0) (Syn.shift a) (Syn.shift d)
      (Syn.shift b) (Syn.shift r) (Syn.shift s)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_compareNumerators,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        numerator_comparison_zero a d b r s
    · simp only [subst_compareNumerators,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact numerator_comparison_succ _ _ _ _ _ _ Prf.hyp0
  simpa only [subst_compareNumerators,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE K

theorem denominator_power_scale (N b P : PTm n) : Γ ⊢[PRAAx]
    pw (denominator N (P*b)) P ≐ pw (pw P P) (succ N) * pw (denominator N b) P := by
  have exchange : Γ ⊢[PRAAx] pw (pw P (succ N)) P ≐ pw (pw P P) (succ N) :=
    (pw_mul P (succ N) P).eqTrans ((congrAp2 powF (mul_comm (succ N) P) (.eqRefl P)).eqTrans
      (pw_mul P P (succ N)).eqSymm)
  have h : Γ ⊢[PRAAx] denominator N (P*b) ≐ pw P (succ N) * denominator N b := by
    unfold denominator
    exact (congrMul (pw_mul_base _ _ _) (.eqRefl _)).eqTrans (by ipra_ring)
  exact (congrAp2 powF (.eqRefl P) h).eqTrans
    ((pw_mul_base _ _ _).eqTrans (congrMul exchange (.eqRefl _)))

def comparison (N a d b r s : PTm n) : Fm PTm n :=
  le
    ((pw (numerator (succ N) a b) (succ r) * pw (numerator (succ N) d b) s) *
      pw (denominator N (weight r s*b)) (weight r s))
    (pw (numerator (succ N) (barycenter a d r s) (weight r s*b)) (weight r s) *
      (pw (denominator N b) (succ r) * pw (denominator N b) s))

theorem weighted_head_comparison (N a d b r s : PTm n) : Γ ⊢[PRAAx] comparison N a d b r s := by
  let P := weight r s
  let A := pw (numerator (succ N) a b) (succ r) * pw (numerator (succ N) d b) s
  let T := pw (pw P P) (succ N)
  let B := denominator N b
  let B' := pw B (succ r) * pw B s
  have p : Γ ⊢[PRAAx] P ≐ succ r+s := by unfold P weight; ipra_ring
  have e : Γ ⊢[PRAAx] pw (denominator N (P*b)) P ≐ T*B' :=
    (denominator_power_scale N b P).eqTrans (congrMul (.eqRefl T)
      ((congrAp2 powF p (.eqRefl B)).eqTrans (pw_add _ _ _)))
  have h : Γ ⊢[PRAAx] A * pw (denominator N (P*b)) P ≐ (T*A)*B' :=
    (congrMul (.eqRefl A) e).eqTrans (by ipra_ring)
  exact le_congr h.eqSymm (.eqRefl _) (mul_le_mul_right B' (numerator_comparison (succ N) a d b r s))

theorem actual_Euler_rational_head_weighted_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (comparison (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (weighted_head_comparison _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalHeadConvexity
