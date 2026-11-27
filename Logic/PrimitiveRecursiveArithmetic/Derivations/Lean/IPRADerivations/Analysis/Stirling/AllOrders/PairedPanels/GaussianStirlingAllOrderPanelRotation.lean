import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.OuterSums.GaussianStirlingAllOrderPanelTail

/-!
# Exact left and right endpoint rotation of the periodic kernel

The two endpoint samples of the centered Bernoulli profile vanish.
Accordingly the original complete panel can be summed over r = 1 to M
using the same rational sum program. This is the indexing of the
original harmonic and reciprocal-square intervals.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelRotation

open_ipra
open GaussianStirlingAllOrderCenteredBernoulli (endpoint_samples_zero)
open GaussianStirlingAllOrderKernel (row multiply_zero_right)
open GaussianStirlingAllOrderPanelTail (panelBody panelData panel_row_at)
open GaussianEuclideanDistanceName (fraction)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_commutative)
open RationalArithmetic (add multiply)
open RationalFiniteSum (term sum_well_formed)
open RationalReciprocalPowerTail (zero_fraction add_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum

def nextBody (f : PTm 2) : PTm 2 := inst2 f (succ (var 0)) (var 1)

@[simp] theorem next_term (f : PTm 2) (i x : PTm n) :
    term (nextBody f) i x = term f (succ i) x := by
  simp only [term,nextBody,inst2,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp

def rotationLaw (f : PTm 2) (N x : PTm n) : Fm PTm n :=
  add (rsum f N x) (term f N x) ≐ add (term f zero x) (rsum (nextBody f) N x)

ipra_subst rotationLaw

private theorem rotate_zero (f : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] rotationLaw f zero x := by
  exact (add_congr (RationalFiniteSum.sum_zero f x) (.eqRefl _)).eqTrans
    ((add_commutative _ _).eqTrans (add_congr (.eqRefl _) (RationalFiniteSum.sum_zero (nextBody f) x).eqSymm))

private theorem rotate_succ (f : PTm 2) (N x : PTm n) (ih : Γ ⊢[PRAAx] rotationLaw f N x) :
    Γ ⊢[PRAAx] rotationLaw f (succ N) x := by
  have step := RationalFiniteSum.sum_succ (Γ := Γ) (nextBody f) N x
  rw [next_term] at step
  exact (add_congr (RationalFiniteSum.sum_succ f N x) (.eqRefl _)).eqTrans
    ((add_congr ih (.eqRefl _)).eqTrans ((add_associative _ _ _).eqTrans (add_congr (.eqRefl _) step.eqSymm)))

theorem rotate (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] rotationLaw f N x := by
  have all : Γ ⊢[PRAAx] .all (rotationLaw f (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_rotationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using rotate_zero (Γ := Γ) f x
    · simp only [subst_rotationLaw,subst_repl_shift]
      exact rotate_succ f (var 0) (Syn.shift x) Prf.hyp0
  simpa only [subst_rotationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem rotate_zero_endpoints (f : PTm 2) (N x : PTm n)
    (h0 : Γ ⊢[PRAAx] term f zero x ≐ fraction zero one)
    (hN : Γ ⊢[PRAAx] term f N x ≐ fraction zero one) :
    Γ ⊢[PRAAx] rsum f N x ≐ rsum (nextBody f) N x := by
  have left := (add_congr (.eqRefl (rsum f N x)) hN).eqTrans (add_zero_right _ (sum_well_formed f N x))
  have right := (add_congr h0 (.eqRefl (rsum (nextBody f) N x))).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right _ (sum_well_formed (nextBody f) N x)))
  exact left.eqSymm.eqTrans ((rotate f N x).eqTrans right)

theorem panel_right_endpoints (m : ℕ) (q A B M k : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] rsum (panelBody m) M (panelData q A B M k) ≐ rsum (nextBody (panelBody m)) M (panelData q A B M k) := by
  have ends := endpoint_samples_zero (m+1) M hM
  have hr (r : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingAllOrderCenteredBernoulli.sample (m+1) r M ≐ fraction zero one) :
      Γ ⊢[PRAAx] term (panelBody m) r (panelData q A B M k) ≐ fraction zero one := by
    refine (panel_row_at m q A B M k r).eqTrans ?_
    exact (multiply_congr h (.eqRefl _)).eqTrans ((multiply_commutative _ _).eqTrans (multiply_zero_right _))
  exact rotate_zero_endpoints _ _ _ (hr zero ends.1) (hr M ends.2)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelRotation
