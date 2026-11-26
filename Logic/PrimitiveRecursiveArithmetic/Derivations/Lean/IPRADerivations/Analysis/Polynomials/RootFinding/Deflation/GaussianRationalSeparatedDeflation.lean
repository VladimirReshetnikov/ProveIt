import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalFiniteRoots
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameReciprocal

/-!
# Residual propagation under separated synthetic deflation

Each stage divides by the next sampled linear factor. Original
residuals bounded by E/K and pairwise separation 1/D give a residual
bound E(2D)^i/K at every remaining sample after i stages.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSeparatedDeflation

open_ipra
open GaussianNameReciprocal (lower lower_norm_positive inverse_bound)
open GaussianRationalFiniteRoots (stage stage_zero stage_succ stage_length)
open GaussianRationalHorner (evaluate qmul horner_canonical qmul_canonical)
open GaussianRationalMetric (bounded qsub boundedSyntax bounded_formula)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone reciprocal reciprocal_identity bounded_difference bounded_product bound_congr)
open GaussianRationalSyntheticDivision (quotient division_evaluation qsub_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right qsub_add_cancel)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quotient_residual (C z y N E K D : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hK : Γ ⊢[PRAAx] le one K) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] bounded (evaluate C z) E K)
    (hy : Γ ⊢[PRAAx] bounded (evaluate C y) E K)
    (hsep : Γ ⊢[PRAAx] lower (qsub y z) D) :
    Γ ⊢[PRAAx] bounded (evaluate (quotient C z N) y) (E*(two*D)) K := by
  let d := qsub y z
  let v := evaluate (quotient C z N) y
  let w := qsub (evaluate C y) (evaluate C z)
  have product : Γ ⊢[PRAAx] w ≐ qmul d v :=
    (qsub_congr (division_evaluation C z y N hC) (.eqRefl _)).eqTrans
      (qsub_add_cancel _ _ (qmul_canonical _ _))
  have leftInverse : Γ ⊢[PRAAx] qmul (reciprocal d) d ≐ qone :=
    (qmul_commutative _ _).eqTrans (reciprocal_identity d (lower_norm_positive d D hD hsep))
  have value : Γ ⊢[PRAAx] qmul (reciprocal d) w ≐ v :=
    (qmul_congr (.eqRefl _) product).eqTrans ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr leftInverse (.eqRefl _)).eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_one_right v (horner_canonical _ _ _)))))
  have diff := bounded_difference _ _ _ _ _ _ hK hK hy hz
  have diff' := GaussianCoefficientNameBounds.bounded_radius_mono w (E*K+E*K) (K*K) (two*E) K
    (GaussianRationalHorner.positive_product _ _ hK hK) hK (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) diff
  exact bound_congr value (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl _) hK (inverse_bound d D hD hsep) diff')

def separationFrom (R D i : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶ lt (Syn.shift i) (var 0) ⟶
    lower (qsub (entry (Syn.shift R) (var 0)) (entry (Syn.shift R) (Syn.shift i))) (Syn.shift D))

def separation (R D : PTm n) : Fm PTm n := .all (separationFrom (Syn.shift R) (Syn.shift D) (var 0))

def laterResiduals (C R i E K : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶ le (Syn.shift i) (var 0) ⟶
    bounded (evaluate (Syn.shift C) (entry (Syn.shift R) (var 0))) (Syn.shift E) (Syn.shift K))

def budget (E D i : PTm n) : PTm n := E*pw (two*D) i

ipra_subst separationFrom [Syn.subst_shift, Syn.shift_subst]

ipra_subst separation [Syn.subst_shift, Syn.shift_subst]

ipra_subst laterResiduals [Syn.subst_shift, Syn.shift_subst]

ipra_subst budget [two, one]

theorem budget_zero (E D : PTm n) : Γ ⊢[PRAAx] budget E D zero ≐ E :=
  (congrMul (.eqRefl _) (pw_zero _)).eqTrans (by ipra_ring)

theorem budget_succ (E D i : PTm n) : Γ ⊢[PRAAx] budget E D (succ i) ≐ budget E D i*(two*D) :=
  (congrMul (.eqRefl _) (pw_succ _ _)).eqTrans (by unfold budget; ipra_ring)

theorem separated_at (R D i j : PTm n) (h : Γ ⊢[PRAAx] separation R D)
    (hj : Γ ⊢[PRAAx] lt j (length R)) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] lower (qsub (entry R j) (entry R i)) D := by
  have outer : Γ ⊢[PRAAx] separationFrom R D i := by
    simpa only [separation,subst_separationFrom,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  have inner : Γ ⊢[PRAAx] lt j (length R) ⟶ lt i j ⟶ lower (qsub (entry R j) (entry R i)) D := by
    simpa [separationFrom] using outer.allE j
  exact .impE (.impE inner hj) hij

theorem later_at (C R i j E K : PTm n) (h : Γ ⊢[PRAAx] laterResiduals C R i E K)
    (hj : Γ ⊢[PRAAx] lt j (length R)) (hij : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] bounded (evaluate C (entry R j)) E K := by
  have rule : Γ ⊢[PRAAx] lt j (length R) ⟶ le i j ⟶ bounded (evaluate C (entry R j)) E K := by
    simpa [laterResiduals] using h.allE j
  exact .impE (.impE rule hj) hij

private theorem later_congr {C C' E E' : PTm n} (R i K : PTm n)
    (hC : Γ ⊢[PRAAx] C ≐ C') (hE : Γ ⊢[PRAAx] E ≐ E') (h : Γ ⊢[PRAAx] laterResiduals C R i E K) :
    Γ ⊢[PRAAx] laterResiduals C' R i E' K := by
  simpa using Prf.eqSubst (Ax := PRAAx) (Γ := Γ)
    (laterResiduals (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![C,R,i,E,K] ![C',R,i,E',K] (fun j => by
      fin_cases j
      · exact hC
      · exact .eqRefl _
      · exact .eqRefl _
      · exact hE
      · exact .eqRefl _)
    (by simpa using h)

private theorem later_after_division (C R i N E K D : PTm n)
    (hc : Γ ⊢[PRAAx] length C ≐ succ N) (hk : Γ ⊢[PRAAx] le one K) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] laterResiduals C R i E K) (hs : Γ ⊢[PRAAx] separation R D) :
    Γ ⊢[PRAAx] laterResiduals (quotient C (entry R i) N) R (succ i) (E*(two*D)) K := by
  refine .allI (.impI (.impI ?_))
  let Δ := le (succ (Syn.shift i)) (var 0) :: lt (var 0) (length (Syn.shift R)) :: Γ.map Fm.shift
  have hc' : Δ ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa [Δ,Fm.shift,Syn.shift] using hc.shift.wk.wk
  have hk' : Δ ⊢[PRAAx] le one (Syn.shift K) := by simpa [Δ,Fm.shift,Syn.shift,one] using hk.shift.wk.wk
  have hd' : Δ ⊢[PRAAx] le one (Syn.shift D) := by simpa [Δ,Fm.shift,Syn.shift,one] using hd.shift.wk.wk
  have hr' : Δ ⊢[PRAAx] laterResiduals (Syn.shift C) (Syn.shift R) (Syn.shift i) (Syn.shift E) (Syn.shift K) := by
    simpa [Δ,Fm.shift,Syn.shift] using hr.shift.wk.wk
  have hs' : Δ ⊢[PRAAx] separation (Syn.shift R) (Syn.shift D) := by
    simpa [Δ,Fm.shift,Syn.shift] using hs.shift.wk.wk
  have hi : Δ ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift R)) := lt_of_lt_of_le Prf.hyp0 (le_of_lt Prf.hyp1)
  have residualI := later_at _ _ _ _ _ _ hr' hi (le_refl _)
  have residualJ := later_at _ _ _ _ _ _ hr' Prf.hyp1 (le_of_lt Prf.hyp0)
  have separationIJ := separated_at _ _ _ _ hs' Prf.hyp1 Prf.hyp0
  simpa only [Δ,Syn.shift,GaussianRationalSyntheticDivision.subst_quotient,subst_entry,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,PTm.subst_mul,two,one] using quotient_residual _ _ _ _ _ _ _ hc' hk' hd'
      residualI residualJ separationIJ

def stageLaw (C N R E K D i : PTm n) : Fm PTm n :=
  le i N ⟶ laterResiduals (stage C N R i) R i (budget E D i) K

def stageSyntax (C N R E K D i : PTm n) : BFm n := .imp (.le i N)
  (.all (length R) (.imp (.le (Syn.shift i) (var 0))
    (boundedSyntax (evaluate (Syn.shift (stage C N R i)) (entry (Syn.shift R) (var 0)))
      (Syn.shift (budget E D i)) (Syn.shift K))))

theorem stage_formula (C N R E K D i : PTm n) :
    formula (stageSyntax C N R E K D i) = stageLaw C N R E K D i := by
  simp only [stageSyntax,stageLaw,laterResiduals,formula,BFm.le,bounded_formula,Syn.shift,subst_length,le]

ipra_subst stageLaw

theorem stage_residuals (C N R E K D i : PTm n) (hc : Γ ⊢[PRAAx] length C ≐ succ N)
    (hk : Γ ⊢[PRAAx] le one K) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] laterResiduals C R zero E K) (hs : Γ ⊢[PRAAx] separation R D)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] laterResiduals (stage C N R i) R i (budget E D i) K := by
  have hc' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hc.shift
  have hk' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift,Syn.shift,one] using hk.shift
  have hd' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift,one] using hd.shift
  have hs' : Γ.map Fm.shift ⊢[PRAAx] separation (Syn.shift R) (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (stageLaw (Syn.shift C) (Syn.shift N) (Syn.shift R)
      (Syn.shift E) (Syn.shift K) (Syn.shift D) (var 0)) := by
    simpa only [stage_formula] using Foundations.BoundedSyntaxInduction.induction
      (stageSyntax (Syn.shift C) (Syn.shift N) (Syn.shift R) (Syn.shift E) (Syn.shift K) (Syn.shift D) (var 0))
      (Γ := Γ)
      (by
        simp only [stage_formula,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        exact .impI (later_congr R zero K (stage_zero C N R).eqSymm (budget_zero E D).eqSymm hr).wk)
      (by
        simp only [stage_formula,subst_stageLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
        refine .impI ?_
        let I := stageLaw (Syn.shift C) (Syn.shift N) (Syn.shift R) (Syn.shift E) (Syn.shift K) (Syn.shift D) (var 0)
        let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
        have index : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
        have prior : Δ ⊢[PRAAx] I := Prf.hyp1
        have prev := Prf.impE prior index
        have shape := stage_length (Γ := Δ) (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0) hc'.wk.wk index
        exact later_congr _ _ _ (stage_succ _ _ _ _).eqSymm (budget_succ _ _ _).eqSymm
          (later_after_division _ _ _ _ _ _ _ shape hk'.wk.wk hd'.wk.wk prev hs'.wk.wk))
  have rule : Γ ⊢[PRAAx] stageLaw C N R E K D i := by
    simpa only [subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

theorem actual_separated_deflation_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((length (var 0) ≐ succ (var 1)) ⟶ (le one (var 4) ⋏ le one (var 5)) ⟶
      laterResiduals (var 0) (var 2) zero (var 3) (var 4) ⟶ separation (var 2) (var 5) ⟶
        stageLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (stage_residuals _ _ _ _ _ _ _ hyp2.wk.wk hyp2.wk.andE₁ hyp2.wk.andE₂ hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianRationalSeparatedDeflation
