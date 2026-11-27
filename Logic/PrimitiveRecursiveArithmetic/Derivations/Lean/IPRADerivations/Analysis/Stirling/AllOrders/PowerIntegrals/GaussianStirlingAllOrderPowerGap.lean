import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowerOrder
import IPRADerivations.Core.OrderCertificates

/-!
# A positive numerator for the paired inverse-power weight

The mixed increment of an ordinary power is nonnegative. Applying
this fact after cross multiplication yields a quantitative gap in the
paired reciprocal powers used in the signed Stirling remainders.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerGap

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mixedIncrement (q a b c : PTm n) : Fm PTm n :=
  le (pw (a+b) q+pw (a+c) q) (pw (a+b+c) q+pw a q)

ipra_subst mixedIncrement [pw]

private theorem mixed_zero (a b c : PTm n) : Γ ⊢[PRAAx] mixedIncrement zero a b c :=
  le_congr (congrAdd (pw_zero _) (pw_zero _)).eqSymm (congrAdd (pw_zero _) (pw_zero _)).eqSymm (le_refl _)

private theorem mixed_succ (q a b c : PTm n) (h : Γ ⊢[PRAAx] mixedIncrement q a b c) :
    Γ ⊢[PRAAx] mixedIncrement (succ q) a b c := by
  have hb := pw_le_pw q (le_add_right a b : Γ ⊢[PRAAx] le a (a+b))
  have hc := pw_le_pw q (le_add_right a c : Γ ⊢[PRAAx] le a (a+c))
  change Γ ⊢[PRAAx] le (pw (a+b) (succ q)+pw (a+c) (succ q)) (pw (a+b+c) (succ q)+pw a (succ q))
  refine le_congr (congrAdd (pw_succ _ _) (pw_succ _ _)).eqSymm (congrAdd (pw_succ _ _) (pw_succ _ _)).eqSymm ?_
  ipra_le (𝔞 a+𝔞 b+𝔞 c)*sl h+𝔞 c*sl hb+𝔞 b*sl hc

theorem mixed_gap (q a b c : PTm n) : Γ ⊢[PRAAx] mixedIncrement q a b c := by
  have all : Γ ⊢[PRAAx] .all (mixedIncrement (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_mixedIncrement,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using mixed_zero a b c
    · simpa only [subst_mixedIncrement,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        (mixed_succ (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) Prf.hyp0)
  simpa only [subst_mixedIncrement,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE q

theorem power_increment (q a d : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ q)+d*pw a q) (pw (a+d) (succ q)) := by
  have mono := mul_le_mul_right (a+d) (pw_le_pw q (le_add_right a d : Γ ⊢[PRAAx] le a (a+d)))
  exact le_congr ((by ipra_ring : Γ ⊢[PRAAx] pw a q*(a+d) ≐ pw a q*a+d*pw a q).eqTrans
      (congrAdd (pw_succ _ _).eqSymm (.eqRefl _)))
    (pw_succ _ _).eqSymm mono

def low (a b d : PTm n) : PTm n := b*(a*(a+d))
def base (a b d h : PTm n) : PTm n := low a b d+a*b*h+d*(a*(a+d))
def gap (q a b d h : PTm n) : PTm n := d*h*(a+b+d)*pw (base a b d h) q

ipra_subst low
ipra_subst base
ipra_subst gap [pw]

theorem cleared_weight_gap (q a d h : PTm n) :
    Γ ⊢[PRAAx] le
      (pw ((a+h+d)*(a*(a+d))) (succ q)+pw (a*((a+h)*(a+h+d))) (succ q)+gap q a (a+h) d h)
      (pw ((a+d)*((a+h)*(a+h+d))) (succ q)+pw (low a (a+h) d) (succ q)) := by
  let b := a+h
  let X := a*(a+d)
  let Y := b*(b+d)
  let L := low a b d
  let B := a*b*h
  let C := d*X
  let U := base a b d h
  let E := d*h*(a+b+d)
  have e₁ : Γ ⊢[PRAAx] L+C ≐ (b+d)*X := by dsimp [L,low,C,X]; ipra_ring
  have e₂ : Γ ⊢[PRAAx] L+B ≐ a*Y := by dsimp [L,low,B,X,Y,b]; ipra_ring
  have e₃ : Γ ⊢[PRAAx] U+E ≐ (a+d)*Y := by dsimp [U,base,E,low,Y,b]; ipra_ring
  have mix : Γ ⊢[PRAAx] le (pw (L+C) (succ q)+pw (L+B) (succ q)) (pw U (succ q)+pw L (succ q)) :=
    le_congr (add_comm _ _) (.eqRefl _) (mixed_gap (succ q) L B C)
  have withGap := add_le_add_right (E*pw U q) mix
  have top := add_le_add₂ (power_increment (Γ := Γ) q U E) (le_refl (pw L (succ q)))
  have together := le_trans withGap (le_congr (by ipra_ring) (.eqRefl _) top)
  exact le_congr
    (congrAdd (congrAdd (congrAp2 powF (.eqRefl _) e₁) (congrAp2 powF (.eqRefl _) e₂)) (.eqRefl _))
    (congrAdd (congrAp2 powF (.eqRefl _) e₃) (.eqRefl _)) together

theorem actual_cleared_inverse_power_paired_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (pw ((var 1+var 3+var 2)*(var 1*(var 1+var 2))) (succ (var 0))+
         pw (var 1*((var 1+var 3)*(var 1+var 3+var 2))) (succ (var 0))+
         gap (var 0) (var 1) (var 1+var 3) (var 2) (var 3))
      (pw ((var 1+var 2)*((var 1+var 3)*(var 1+var 3+var 2))) (succ (var 0))+
        pw (low (var 1) (var 1+var 3) (var 2)) (succ (var 0)))) :=
  closeUniv 4 (cleared_weight_gap _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerGap
