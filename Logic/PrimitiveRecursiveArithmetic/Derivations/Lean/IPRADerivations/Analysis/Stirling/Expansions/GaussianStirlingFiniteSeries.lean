import IPRADerivations.Analysis.Stirling.Expansions.StirlingRationalSeries
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddSeries
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRationalTelescopers
import IPRADerivations.AnalyticNumberTheory.EnergyWitness

/-!
# The literal finite Stirling series and its cleared Horner fold

The independently defined list sum of the odd-denominator powers at
x=a/b agrees with a Horner evaluation over a common factorial
denominator, including at internal order zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFiniteSeries

open_ipra
open ComplexLogarithmRemainder (oneCode zeroCode scale)
open GaussianEulerPositivePowerChartCorrectedImage (fraction_sum)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd positive_product canonical_unique ofGaussian_canonical ofGaussian_represents
  represents_congr zero_represents qzero)
open GaussianRationalSyntheticDivision (qadd_congr qzero_canonical)
open GaussianStirlingOddSeries (term partialSum partial_zero partial_succ)
open GaussianStirlingRationalTelescopers
  (fraction_same numeratorSquare denominatorSquare gap square_split square_positive)
open StirlingRationalSeries (fold fold_zero fold_succ)
open RobbinsSeries (gq g_eq)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (a b L K : PTm n) : PTm n := pw (denominatorSquare a b) K*fact L
def folded (a b L K : PTm n) : PTm n :=
  fraction (fold (denominatorSquare a b) (numeratorSquare b) L K) (denominator a b L K)

ipra_subst denominator
ipra_subst folded

theorem denominator_positive (a b L K : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (denominator a b L K) :=
  positive_product _ _
    (GaussianFactorBudget.power_positive _ _ (square_positive a b hb)) (GammaEulerMesh.factorial_positive L)

theorem denominator_step (a b L K : PTm n) :
    Γ ⊢[PRAAx] denominator a b L (succ K) ≐ denominator a b L K*denominatorSquare a b := by
  unfold denominator
  exact (congrMul (pw_succ _ _) (.eqRefl _)).eqTrans (by ipra_ring)

private theorem twice_power (q j : PTm n) : Γ ⊢[PRAAx] pw q (two*j) ≐ pw (q*q) j :=
  (congrAp2 powF (by ipra_ring) (.eqRefl _)).eqTrans (AnalyticNumberTheory.EnergyWitness.pw_sq q j).eqSymm

theorem term_squared (a b j : PTm n) : Γ ⊢[PRAAx]
    term a b j ≐ fraction (pw (numeratorSquare b) (succ j))
      (succ (two*succ j)*pw (denominatorSquare a b) (succ j)) :=
  GaussianCompactRiemannName.fraction_congr _ _ _ _ (twice_power b (succ j))
    (congrMul (.eqRefl _) (twice_power (two*a+b) (succ j)))

theorem term_at_factorial (a b L j : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hL : Γ ⊢[PRAAx] le (succ (two*succ j)) L) :
    Γ ⊢[PRAAx] term a b j ≐
      fraction (pw (numeratorSquare b) (succ j)*gq (succ j) L) (denominator a b L (succ j)) := by
  have hd := positive_product _ _ (zero_lt_succ (two*succ j))
    (GaussianFactorBudget.power_positive (denominatorSquare a b) (succ j) (square_positive a b hb))
  have fact := natEq (g_eq hL)
  refine (term_squared a b j).eqTrans (fraction_same _ _ _ _ hd (denominator_positive a b L (succ j) hb) ?_)
  unfold denominator
  apply deriveNat
  ipra_simps
  linear_combination Groth.ι (IPRA.Q.mk Γ (pw (numeratorSquare b) (succ j))) *
    Groth.ι (IPRA.Q.mk Γ (pw (denominatorSquare a b) (succ j)))*fact

private theorem zero_is_fraction (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qzero ≐ fraction zero D := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal zeroCode (scale zero oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_zero,
        GaussianRootAlgebra.im_zero,IPRA.Q.mk_zero]
  exact canonical_unique _ _ _ D qzero_canonical (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) native (.eqRefl _) (zero_represents D)) (ofGaussian_represents _ _ hD)

private theorem add_fold_and_term (a b L j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hL : Γ ⊢[PRAAx] le (succ (two*succ j)) L) :
    Γ ⊢[PRAAx] qadd (folded a b L j) (term a b j) ≐ folded a b L (succ j) := by
  let w := denominatorSquare a b
  let u := numeratorSquare b
  let D := denominator a b L j
  let E := denominator a b L (succ j)
  let T := fold w u L j
  let c := pw u (succ j)*gq (succ j) L
  have hD := denominator_positive a b L j hb
  have hE := denominator_positive a b L (succ j) hb
  have rebase : Γ ⊢[PRAAx] folded a b L j ≐ fraction (w*T) E := by
    apply fraction_same _ _ _ _ hD hE
    have e := natEq (denominator_step (Γ := Γ) a b L j)
    apply deriveNat
    change Groth.ι (IPRA.Q.mk Γ (T*E)) = Groth.ι (IPRA.Q.mk Γ (w*T*D))
    ipra_simps
    linear_combination Groth.ι (IPRA.Q.mk Γ T)*e
  have right := qadd_congr rebase (term_at_factorial a b L j hb hL)
  apply right.eqTrans
  refine (fraction_sum (w*T) E c E hE hE).eqTrans ?_
  refine (fraction_same _ _ _ _ (positive_product _ _ hE hE) hE (by ipra_ring :
    Γ ⊢[PRAAx] ((w*T)*E+c*E)*E ≐ (w*T+c)*(E*E))).eqTrans ?_
  exact GaussianCompactRiemannName.fraction_congr _ _ _ _ (fold_succ w u L j).eqSymm (.eqRefl _)

private def foldLaw (a b L j : PTm n) : Fm PTm n :=
  le (succ (two*j)) L ⟶ partialSum a b j ≐ folded a b L j

@[simp] private theorem subst_foldLaw {l : ℕ} (σ : Fin n → PTm l) (a b L j : PTm n) :
    (foldLaw a b L j).subst σ =
      foldLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ L) (Syn.subst σ j) := by simp [foldLaw,one,two]

theorem partial_equals_fold (a b L K : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hL : Γ ⊢[PRAAx] le (succ (two*K)) L) : Γ ⊢[PRAAx] partialSum a b K ≐ folded a b L K := by
  have all : Γ ⊢[PRAAx] .all (foldLaw (Syn.shift a) (Syn.shift b) (Syn.shift L) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_foldLaw]
    · exact .impI ((partial_zero a b).eqTrans ((zero_is_fraction _ (denominator_positive a b L zero hb.wk)).eqTrans
        (GaussianCompactRiemannName.fraction_congr _ _ _ _ (fold_zero _ _ _).eqSymm (.eqRefl _))))
    · refine .impI ?_
      let j : PTm (n+1) := var 0
      let a' := Syn.shift a
      let b' := Syn.shift b
      let L' := Syn.shift L
      let Δ := le (succ (two*succ j)) L' :: foldLaw a' b' L' j :: Γ.map Fm.shift
      have h' : Δ ⊢[PRAAx] le one b' := by simpa [b',Fm.shift,Syn.shift,one] using hb.shift.wk.wk
      have old := le_of_eq_add (d := two)
        (by ipra_ring : Δ ⊢[PRAAx] succ (two*succ j) ≐ succ (two*j)+two)
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] foldLaw a' b' L' j) (le_trans old Prf.hyp0)
      exact (partial_succ a' b' j).eqTrans ((qadd_congr ih (.eqRefl _)).eqTrans
        (add_fold_and_term a' b' L' j h' Prf.hyp0))
  have result : Γ ⊢[PRAAx] foldLaw a b L K := by
    simpa only [subst_foldLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K
  exact .impE result hL

theorem actual_finite_Stirling_partial_equals_fold_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (succ (two*var 3)) (var 2) ⟶
      partialSum (var 0) (var 1) (var 3) ≐ folded (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (partial_equals_fold _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingFiniteSeries
