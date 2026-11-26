import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogSchedule
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# Dyadic growth of the original Barnes head powers

On the disk of radius R, the k-th polynomial factor has norm at most
(R+1)^k. The original finite product has norm at most (R+1)^(N²).
At R=2^j the original mandatory head N=2R thus has a dyadic cap with
exponent 4R²(j+1).
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicHeadPower

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open BarnesCutoff (maximum_of_right)
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct power_at subst_powerProduct)
open GaussianBarnesCanonicalFactor (base powerValue base_bound)
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFactorBudget (power_monotone_length)
open GaussianRationalFiniteProduct (product_zero product_succ)
open GaussianRationalMetric (bounded subst_bounded)
open GaussianRationalPowerDifference (bounded_power_integer)
open GaussianRationalReciprocal (bound_congr bounded_product qone_bounded)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "pointData" => GaussianBarnesCanonicalPolynomialShift.data

private def law (z R B N : PTm n) : Fm PTm n :=
  bounded (powerProduct z B N) (pw (R+one) (N*N)) one

@[simp] private theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    (law z R B N).subst σ = law (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [law,one]

private theorem power_bound_zero (z R B : PTm n) : Γ ⊢[PRAAx] law z R B zero :=
  bound_congr (product_zero powerBody (pointData z B)).eqSymm
    ((congrAp2 powF (mul_zero zero) (.eqRefl (R+one))).eqTrans (pw_zero (R+one))).eqSymm
    (.eqRefl _) qone_bounded

private theorem power_bound_step (z R B N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (ih : Γ ⊢[PRAAx] law z R B N) :
    Γ ⊢[PRAAx] law z R B (succ N) := by
  let A := R+one
  let k := succ N
  let P := powerProduct z B N
  let q := powerValue z B k
  have hbase := base_bound z R B k (.andI hz.andE₁ (.andI (zero_lt_succ N) hz.andE₂))
  have hpow := bounded_power_integer (base z B k) A k hbase
  have exactProduct : Γ ⊢[PRAAx] powerProduct z B k ≐ GaussianRationalHorner.qmul P q :=
    (product_succ powerBody N (pointData z B)).eqTrans (qmul_congr (.eqRefl _) (power_at N z B))
  have old := bounded_product P q (pw A (N*N)) one (pw A k) one (le_refl one) (le_refl one) ih hpow
  have new := bound_congr exactProduct.eqSymm (pw_add A (N*N) k).eqSymm (one_mul one) old
  have order : Γ ⊢[PRAAx] le (N*N+k) (k*k) := by
    apply le_of_eq_add (d := N)
    dsimp only [k]
    ipra_ring
  have hA := le_add_left (Γ := Γ) one R
  have radius := power_monotone_length A (N*N+k) (k*k) hA order
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (mul_le_mul_right one radius) new

theorem power_bound (z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (powerProduct z B N) (pw (R+one) (N*N)) one := by
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) :=
    by simpa [Fm.shift,Syn.shift,sh] using hz.shift
  have all : Γ ⊢[PRAAx] .all (law (sh z) (sh R) (sh B) (var 0)) := by
    refine PRA.qfInd _ ?_ ?_ ?_
    · simp only [law,bounded]
      exact le_QF _ _
    · simp only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh]
      exact power_bound_zero z R B
    · simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh]
      exact power_bound_step _ _ _ _ hs.wk Prf.hyp0
  change Γ ⊢[PRAAx] law z R B N
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE N

theorem dyadic_bound (z B N j : PTm n) (hz : Γ ⊢[PRAAx] source z (unit j) B) :
    Γ ⊢[PRAAx] bounded (powerProduct z B N) (unit ((N*N)*succ j)) one := by
  let R := unit j
  let D := N*N
  have double : Γ ⊢[PRAAx] unit (succ j) ≐ R*two := pw_succ two j
  have edge : Γ ⊢[PRAAx] le (R+one) (R*two) :=
    le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] R+R ≐ R*two)
      (le_congr (add_comm one R) (add_comm R R) (add_le_add_right R (unit_positive j)))
  have edge' : Γ ⊢[PRAAx] le (R+one) (unit (succ j)) :=
    le_congr (.eqRefl _) double.eqSymm edge
  have pow : Γ ⊢[PRAAx] pw (unit (succ j)) D ≐ unit (D*succ j) :=
    (pw_mul two (succ j) D).eqTrans (congrAp2 powF (mul_comm _ _) (.eqRefl _))
  have radius := le_congr (.eqRefl _) pow (pw_le_pw D edge')
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (mul_le_mul_right one radius) (power_bound z R B N hz)

theorem initial_dyadic_bound (z B j : PTm n) (hz : Γ ⊢[PRAAx] source z (unit j) B) :
    Γ ⊢[PRAAx] bounded (powerProduct z B (initial (unit j))) (unit (num 4*unit j*unit j*succ j)) one := by
  let R := unit j
  let N := initial R
  have hR : Γ ⊢[PRAAx] le one (two*R) :=
    le_trans (unit_positive j) (le_of_eq_add (d := R) (by ipra_ring))
  have hN : Γ ⊢[PRAAx] N ≐ two*R := maximum_of_right hR
  have e : Γ ⊢[PRAAx] unit ((N*N)*succ j) ≐ unit (num 4*R*R*succ j) := by
    refine congrAp2 powF ((congrMul (congrMul hN hN) (.eqRefl _)).eqTrans ?_) (.eqRefl _)
    ipra_ring
  exact bound_congr (.eqRefl _) e (.eqRefl _) (dyadic_bound z B N j hz)

theorem actual_Barnes_head_power_disk_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) ⟶ bounded (powerProduct (var 0) (var 2) (var 3))
        (pw (var 1+one) (var 3*var 3)) one) :=
  closeUniv 4 (.impI (power_bound _ _ _ _ Prf.hyp0))

theorem actual_Barnes_initial_head_dyadic_power_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (unit (var 2)) (var 1) ⟶
        bounded (powerProduct (var 0) (var 1) (initial (unit (var 2))))
          (unit (num 4*unit (var 2)*unit (var 2)*succ (var 2))) one) :=
  closeUniv 3 (.impI (initial_dyadic_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicHeadPower
